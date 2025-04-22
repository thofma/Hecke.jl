################################################################################
#
#  Reduction of sparse rows modulo sparse upper triangular matrices
#
################################################################################
@doc raw"""
    reduce(A::SMat{T}, g::SRow{T}) -> SRow{T}

Given an upper triangular matrix $A$ over a field and a sparse row $g$, this
function reduces $g$ modulo $A$.
"""
function reduce(A::SMat{T}, g::SRow{T}; new_g::Bool = false) where {T <: FieldElement}
  return _reduce_field(A, g; new_g)
end

function reduce(A::SMat{zzModRingElem}, g::SRow{zzModRingElem}; new_g::Bool = false)
  return _reduce_field(A, g; new_g)
end

function _reduce_field(A::SMat{T}, g::SRow{T}; new_g::Bool = false) where {T}
  @hassert :HNF 1  is_upper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  # supposed to be a field...
  if A.r == A.c
    return sparse_row(base_ring(A))
  end
  g = deepcopy(g)
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= nrows(A) && A.rows[j].pos[1] < s
      j += 1
    end
    if j > nrows(A) || A.rows[j].pos[1] > s
      break
    end
    @hassert :HNF 2  A.rows[j].pos[1] == g.pos[1]
    @hassert :HNF 2  (A.rows[j].values[1]) == 1
    p = g.values[1]
    g = Hecke.add_scaled_row(A[j], g, -p)
    @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
  end
  if length(g) > 0
    li = inv(g.values[1])
    scale_row!(g, li)
  end
  return g
end

function gcdx!(a::ZZRingElem, b::ZZRingElem, c::ZZRingElem, d::ZZRingElem, e::ZZRingElem)
  @ccall Nemo.libflint.fmpz_xgcd_canonical_bezout(a::Ref{ZZRingElem}, b::Ref{ZZRingElem}, c::Ref{ZZRingElem}, d::Ref{ZZRingElem}, e::Ref{ZZRingElem})::Nothing
  return a, b, c
end

function gcdx!(a::T, b::T, c::T, d::T, e::T) where {T <: RingElem}
  return gcdx(d, e)
end

@doc raw"""
    reduce(A::SMat{T}, g::SRow{T}) -> SRow{T}

Given an upper triangular matrix $A$ over a field and a sparse row $g$, this
function reduces $g$ modulo $A$.
"""
function reduce(A::SMat{T}, g::SRow{T}; new_g::Bool = false) where {T}

  @hassert :HNF 1  is_upper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  #until the 1st (pivot) change in A

  tmpa = get_tmp(A)
  tmpb = get_tmp(A)

  R = base_ring(A)
  tmp, p_v, A_v, x, a, b = tmp_scalar = get_tmp_scalar(A, 6)

  @inbounds while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= nrows(A) && A.rows[j].pos[1] < s
      j += 1
    end
    if j > nrows(A) || A.rows[j].pos[1] > s
      if length(g) > 0 && is_negative(getindex!(tmp, g.values, 1))
        if !new_g
          g = deepcopy(g)
          new_g = true
        end
        scale_row!(g, -1)
      end
      if !new_g
        g = deepcopy(g)
        new_g = true
      end
      release_tmp_scalar(A, tmp_scalar)
      release_tmp(A, tmpa)
      release_tmp(A, tmpb)
      @assert new_g
      return g
    end
    p_v = getindex!(p_v, g.values, 1)
    if !new_g
      g = deepcopy(g)
      new_g = true
    end
    A_v = getindex!(A_v, A.rows[j].values, 1)
    fl, tmp = Nemo.divides!(tmp, p_v, A_v)
    if fl
      tmp = neg!(tmp)
      if new_g
        g = Hecke.add_scaled_row!(A[j], g, tmp, tmpa)
      else
        g = deepcopy(g)
        g = Hecke.add_scaled_row!(A[j], g, tmp, tmpa)
        new_g = true
      end
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx!(x, a, b, A_v, p_v)
      @hassert :HNF 2  x > 0
      c = div!(tmp, p_v, x)
      c = neg!(c)
      d = div!(A_v, A_v, x)
      if new_g
        new_g = true
        g = deepcopy(g)
      end
      A[j], g = Hecke.transform_row!(A[j], g, a, b, c, d, tmpa, tmpb)
      @hassert :HNF 2  A[j].values[1] == x
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    end
  end
 
  if length(g.values) > 0 && is_negative(getindex!(tmp, g.values, 1))
    if !new_g
      g = deepcopy(g)
      new_g = true
    end
    scale_row!(g, -1)
  end
  release_tmp_scalar(A, tmp_scalar)
  release_tmp(A, tmpa)
  release_tmp(A, tmpb)
  @assert new_g
  return g
end

@doc raw"""
    reduce(A::SMat{T}, g::SRow{T}, m::T) -> SRow{T}

Given an upper triangular matrix $A$ over the integers, a sparse row $g$ and an
integer $m$, this function reduces $g$ modulo $A$ and returns $g$
modulo $m$ with respect to the symmetric residue system.
"""
function reduce(A::SMat{T}, g::SRow{T}, m::T; new_g::Bool = false) where {T}
  @hassert :HNF 1 is_upper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  @assert m > 0 
  g = deepcopy(g)
  mod_sym!(g, m)

  tmpa = get_tmp(A)
  tmpb = get_tmp(A)

  R = base_ring(A)
  p_v, g_v, A_v, a, b, x = tmp_scalar = get_tmp_scalar(A, 6)

  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= nrows(A) && A.rows[j].pos[1] < s
      j += 1
    end
    if j > nrows(A) || A.rows[j].pos[1] > s
      g_v = getindex!(g_v, g.values, 1)
      g_v = mod_sym!(g_v, m)
      if is_negative(g_v)
        scale_row!(g, -1)
        @hassert :HNF 3  mod_sym(g.values[1], m) > 0
      end
      mod_sym!(g, m)
      release_tmp_scalar(A, tmp_scalar)
      release_tmp(A, tmpa)
      release_tmp(A, tmpb)
      return g
    end
    
    p_v = getindex!(p_v, g.values, 1)
    A_v = getindex!(A_v, A.rows[j].values, 1)
    fl, g_v = divides!(g_v, p_v, A_v)

    if fl
      g_v = neg!(g_v)
      add_scaled_row!(A[j], g, g_v)#, tmpa) #changes g
      mod_sym!(g, m)
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx!(x, a, b, A_v, p_v)
      @hassert :HNF 2  x > 0
      c = div!(g_v, p_v, x)
      c = neg!(c)
      d = div!(A_v, A_v, x)
      Hecke.transform_row!(A[j], g, a, b, c, d, tmpa, tmpb)
#      @hassert :HNF 2  A[j].values[1] == x
      mod_sym!(g, m)
      mod_sym!(A[j], m)
#      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
#      @hassert :HNF 2  A[j].values[1] > 0
    end
  end
  if length(g.values) > 0 && is_negative(mod_sym!(getindex!(g_v, g.values, 1), m))
    scale_row!(g, -1)
  end
  Hecke.mod_sym!(g, m)
#  @hassert :HNF 1  length(g.pos) == 0 || g.values[1] >= 0
  release_tmp_scalar(A, tmp_scalar)
  release_tmp(A, tmpa)
  release_tmp(A, tmpb)
  return g
end



################################################################################
#
#  Saturation
#
################################################################################

@doc raw"""
    saturate(A::SMat{ZZRingElem}) -> SMat{ZZRingElem}

Computes the saturation of $A$, that is, a basis for $\mathbf{Q}\otimes M \cap
\mathbf{Z}^n$, where $M$ is the row span of $A$ and $n$ the number of rows of
$A$.

Equivalently, return $TA$ for an invertible rational matrix $T$, such that $TA$
is integral and the elementary divisors of $TA$ are all trivial.
"""
function saturate(A::SMat{ZZRingElem})
  Hti = transpose(hnf(transpose(A)))
  Hti = sub(Hti , 1:nrows(Hti), 1:nrows(Hti))
  Hti = transpose(Hti)
  S, s = _solve_ut(Hti, transpose(A))
  @assert isone(s)
  SS = transpose(S)
  return SS
end

################################################################################
#
#  Hermite normal form using Kannan-Bachem algorithm
#
################################################################################

@doc raw"""
    find_row_starting_with(A::SMat, p::Int) -> Int

Tries to find the index $i$ such that $A_{i,p} \neq 0$ and $A_{i, p-j} = 0$
for all $j > 1$. It is assumed that $A$ is upper triangular.
If such an index does not exist, find the smallest index larger.
"""
function find_row_starting_with(A::SMat, p::Int)
#  @hassert :HNF 1  is_upper_triangular(A)
  start = 0
  stop = nrows(A)+1
  @inbounds while start < stop - 1
    mid = div((stop + start), 2)
    Am = A[mid]
    if length(Am) == 0 || Am.pos[1] == p
      return mid
    elseif Am.pos[1] < p
      start = mid
    else
      stop = mid
    end
  end
  return stop
end

# If with_transform is set to true, then additionally an Array of transformations
# is returned.
function reduce_up(A::SMat{T}, piv::Vector{Int}, with_transform_val::Val{with_transform} = Val(false); limit::Int = typemax(Int)) where {T, with_transform}

  if with_transform
    trafos = SparseTrafoElem{T, dense_matrix_type(T)}[]
  end

  sort!(piv)
  p = find_row_starting_with(A, piv[end])

  @inbounds for red=p-1:-1:1
    # the last argument should be the smallest pivot larger then pos[1]
    if with_transform
      A[red], new_trafos = reduce_right(A, A[red], max(A[red].pos[1]+1, piv[1]), with_transform_val; limit, new_g = true)
      for t in new_trafos
        t.j = red
      end
      append!(trafos, new_trafos)
    else
      A[red] = reduce_right(A, A[red], max(A[red].pos[1]+1, piv[1]); limit, new_g = true)
    end
  end
  with_transform ? (return trafos) : nothing
end

# If trafo is set to Val{true}, then additionally an Array of transformations
# is returned.
@doc raw"""
    reduce_full(A::SMat{ZZRingElem}, g::SRow{ZZRingElem},
                          with_transform = Val(false)) -> SRow{ZZRingElem}, Vector{Int}

Reduces $g$ modulo $A$ and assumes that $A$ is upper triangular.

The second return value is the array of pivot elements of $A$ that changed.

If `with_transform` is set to `Val(true)`, then additionally an array of transformations
is returned.
"""
function reduce_full(A::SMat{T}, g::SRow{T, S}, with_transform_val::Val{with_transform} = Val(false); full_hnf::Bool = true, limit::Int = typemax(Int), new_g::Bool = false) where {T, S, with_transform}
#  @hassert :HNF 1  is_upper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A

  g = deepcopy(g)
  if with_transform
    trafos = SparseTrafoElem{T, dense_matrix_type(T)}[]
  end
  piv = Int[]

  if length(A.rows) == 0
    if length(g) > 0 && is_negative(g.values[1])
      scale_row!(g, -1)
      if with_transform
        trafos = [sparse_trafo_scale(1, ZZ(-1))]
      end
    end
    return with_transform ? (g, piv, trafos) : (g, piv)
  end

  tmpa = get_tmp(A)
  tmpb = get_tmp(A)
  p_v, A_v, sca, r, a, b, x = tmp_scalar = get_tmp_scalar(A, 7)
  is_Z = base_ring(A) == ZZ

  nrA = nrows(A)
  local Aj::SRow{T, S} = tmpa

  @inbounds while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= nrA && A.rows[j].pos[1] < s
      j += 1
    end
    j <= nrA && (Aj = A[j])
    if j > nrA || Aj.pos[1] > s || s > limit
      A_v = getindex!(A_v, g.values, 1)
      if (is_Z && is_negative(A_v)) || (!is_Z && !isone(canonical_unit(A_v)))
        # Multiply row g by -1
        if with_transform
          push!(trafos, sparse_trafo_scale(nrA + 1, base_ring(A)(inv(canonical_unit(g.values[1])))))
        end
        if !new_g
          g = deepcopy(g)
          new_g = true
        end
        if is_Z
          scale_row!(g, -1)
        else
          scale_row!(g, base_ring(A)(inv(canonical_unit(g.values[1]))))
        end
      end

      _g = g
      if full_hnf
        if with_transform
          g, new_trafos  = reduce_right(A, g, 1, with_transform_val; limit, new_g)
          append!(trafos, new_trafos)
        else
          g = reduce_right(A, g; limit, new_g)
        end
      end
      if _g !== g
        new_g = true
      else 
        g = deepcopy(g)
        new_g = true
      end

      if A.r == A.c
        @hassert :HNF 1  length(g) == 0 || minimum(g) >= 0
      end

      release_tmp(A, tmpa)
      release_tmp(A, tmpb)
      release_tmp_scalar(A, tmp_scalar)
      @assert new_g
      with_transform ? (return g, piv, trafos) : (return g, piv)

    end
    p_v = getindex!(p_v, g.values, 1)
    A_v = getindex!(A_v, Aj.values, 1)
    if !new_g
      g = deepcopy(g)
      new_g = true
    end
    sca, r = divrem!(sca, r, p_v, A_v)
#    sca, r = divrem(p_v, A_v)
    if iszero(r)
      sca = neg!(sca)
      @assert !iszero(sca)
      @assert new_g
      Hecke.add_scaled_row!(Aj, g, sca, tmpa)
      with_transform ? push!(trafos, sparse_trafo_add_scaled(j, nrows(A) + 1, sca)) : nothing
      @hassert :HNF 1  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
#      x, a, b = gcdx(A_v, p_v)
      x, a, b = gcdx!(x, a, b, A_v, p_v)
      @hassert :HNF 1  x > 0
      c = div(p_v, x)
      c = neg!(c)
      d = div(A_v, x)
      @assert new_g
      Hecke.transform_row!(Aj, g, a, b, c, d, tmpa, tmpb)
      if with_transform
        push!(trafos, sparse_trafo_para_add_scaled(j, nrA + 1, a, b, c, d))
      end
      @hassert :HNF 1  A[j].values[1] == x
      @hassert :HNF 1  length(g)==0 || g.pos[1] > A[j].pos[1]
      push!(piv, Aj.pos[1])
      if full_hnf
        if with_transform
          A[j], new_trafos = reduce_right(A, Aj, Aj.pos[1]+1, with_transform_val; limit, new_g = true)
          # We are updating the jth row
          # Have to adjust the transformations
          for t in new_trafos
            t.j = j
          end
          # Now append
          append!(trafos, new_trafos)
        else
          A[j] = reduce_right(A, Aj, Aj.pos[1]+1, with_transform_val; limit)
        end
      end

      if A.r == A.c
        @hassert :HNF 1  minimum(A[j]) >= 0
      end
    end
  end
  if !new_g
    g = deepcopy(g)
    new_g = true
  end
  if with_transform
    g, new_trafos = reduce_right(A, g, 1, with_transform_val; limit, new_g)
    append!(trafos, new_trafos)
  else
    g = reduce_right(A, g; limit)
  end
  if length(g.values) > 0 && is_negative(getindex!(p_v, g.values, 1))
    scale_row!(g, -1)
    with_transform ? push!(trafos, sparse_trafo_scale!{ZZRingElem}(nrows(A) + 1, ZZRingElem(-1))) : nothing
  end

  if A.r == A.c
    @hassert :HNF 1  length(g) == 0 || minimum(g) >= 0
  end
  release_tmp(A, tmpa)
  release_tmp(A, tmpb)
  release_tmp_scalar(A, tmp_scalar)
  @assert new_g
  with_transform ? (return g, piv, trafos) : (return g, piv)
end

divrem!(q, r, a, b) = divrem(a, b)

function divrem!(q::ZZRingElem, r::ZZRingElem, a::ZZRingElem, b::ZZRingElem)
  @ccall libflint.fmpz_tdiv_qr(q::Ref{ZZRingElem}, r::Ref{ZZRingElem}, a::Ref{ZZRingElem}, b::Ref{ZZRingElem})::Nothing
  return q, r
end

function reduce_right(A::SMat{T}, b::SRow{T}, start::Int = 1, with_transform_val::Val{with_transform} = Val(false); limit::Int = typemax(Int), new_g::Bool = false) where {T, with_transform}
 
  new_g || (b = deepcopy(b))
  with_transform ? trafos = [] : nothing
  lb = length(b.pos)
  if lb == 0
    with_transform ? (return b, trafos) : return b
  end
  j = 1
  @inbounds while j <= lb && b.pos[j] < start
    j += 1
  end
  if j > lb
    if is_negative(b.values[1])
      scale_row!(b, -1)
      if with_transform
        push!(trafos, sparse_trafo_scale(nrows(A) + 1), ZZ(-1))
      end
    end
    with_transform ? (return b, trafos) : return b
  end
  p = find_row_starting_with(A, b.pos[j])
  if p > nrows(A)
    if is_negative(b.values[1])
      scale_row!(b, -1)
      if with_transform
        push!(trafos, sparse_trafo_scale(nrows(A) + 1), ZZ(-1))
      end
    end

    with_transform ? (return b, trafos) : return b
  end
  @hassert :HNF 1  A[p] != b
  tmpa = get_tmp(A)
  R = base_ring(A)
  b_v, A_v, q, r = tmp_scalar = get_tmp_scalar(A, 4)
  @inbounds while j <= length(b.pos)
    while p<nrows(A) && length(A[p])>0 && A[p].pos[1] < b.pos[j]
      p += 1
    end
    if p > length(A.rows) || length(A[p]) == 0 || A[p].pos[1] > limit
      break
    end

    if A[p].pos[1] == b.pos[j]
      b_v = getindex!(b_v, b.values, j)
      A_v = getindex!(A_v, A[p].values, 1)
      @hassert :HNF 1 !is_negative(A_v)
      q, r = divrem!(q, r, b_v, A_v)
      if T == ZZRingElem && is_negative(r)
        add!(q, q, -1)
        add!(r, r, A_v)
        @hassert :HNF 1  r >= 0
#        @assert q*A_v + r == b_v
      end
      if !iszero(q)
        q = neg!(q)
        Hecke.add_scaled_row!(A[p], b, q, tmpa)

        with_transform ? push!(trafos, sparse_trafo_add_scaled(p, nrows(A) + 1, q)) : nothing
        if r == 0
          j -= 1
        else
          @hassert :HNF 1  b.values[j] == r
        end
      end
    end
    j += 1
  end
  if length(b) > 0 && is_negative(getindex!(A_v, b.values, 1)) 
    @assert new_g
    scale_row!(b, -1)
    if with_transform
      push!(trafos, sparse_trafo_scale(nrows(A) + 1), ZZ(-1))
    end
  end
  release_tmp(A, tmpa)
  release_tmp_scalar(A, tmp_scalar)
  with_transform ? (return b, trafos) : return b
end

@doc raw"""
    hnf_extend!(A::SMat{ZZRingElem}, b::SMat{ZZRingElem}, offset::Int = 0) -> SMat{ZZRingElem}

Given a matrix $A$ in HNF, extend this to get the HNF of the concatenation
with $b$.
"""
function hnf_extend!(A::SMat{T}, b::SMat{T}, with_transform_val::Val{with_transform} = Val(false); truncate::Bool = false, offset::Int = 0) where {T, with_transform}
  rA = nrows(A)
  @vprintln :HNF 1 "Extending HNF by:"
  @vprint :HNF 1 b
  @vprint :HNF 1 "density $(density(A)) $(density(b))"

  with_transform ? trafos = SparseTrafoElem{T, dense_matrix_type(T)}[] : nothing

  A_start_rows = nrows(A)  # for the offset stuff

  nc = 0
  for i=b
    if with_transform
      q, w, new_trafos = reduce_full(A, i, with_transform_val)
      append!(trafos, new_trafos)
    else
      q, w = reduce_full(A, i)
    end

    if length(q) > 0
      p = find_row_starting_with(A, q.pos[1])
      if p > length(A.rows)
        # Appending row q to A
        # Do not need to track a transformation
        push!(A, q)
      else
        # Inserting row q at position p
        insert!(A.rows, p, q)
        A.r += 1
        A.nnz += length(q)
        A.c = max(A.c, q.pos[end])
        # The transformation is swapping pairwise from nrows(B) to p.
        # This should be the permutation matrix corresponding to
        # (k k-1)(k-1 k-2) ...(p+1 p) where k = nrows(B)
        if with_transform
          for j in nrows(A):-1:(p+1)
            push!(trafos, sparse_trafo_swap(T, j, j - 1))
          end
        end
      end
      push!(w, q.pos[1])
    else
      # Row i was reduced to zero
      with_transform ? push!(trafos, sparse_trafo_move_row(T, nrows(A) + 1, rA + nrows(b))) : nothing
    end
    if length(w) > 0
      if with_transform
        new_trafos = reduce_up(A, w, with_transform_val)
        append!(trafos, new_trafos)
      else
        reduce_up(A, w)
      end
    end
    @v_do :HNF 1 begin
      if nc % 10 == 0
        println("Now at $nc rows of $(nrows(b)), HNF so far $(nrows(A)) rows")
        println("Current density: $(density(A))")
        @vprintln :HNF 2 "and size of largest entry: $(nbits(maximum(abs, A))) bits $(sum(nbits, A))"
        @vtime :HNF 1 Base.GC.gc(false)
      end
    end
    nc += 1
  end
  if !truncate
    for i in 1:nrows(b)
      push!(A, sparse_row(base_ring(A)))
    end
  end

  if with_transform && offset != 0
    change_indices!(trafos, A_start_rows, offset)
  end

  with_transform ? (return A, trafos) : (return A)
end

function nbits(s::SRow{ZZRingElem})
  return sum(nbits, s.values)
end

function upper_triag_to_hnf!(B::SMat{T}, with_transform_val::Val{with_transform} = Val(false); limit::Int = typemax(Int)) where {T, with_transform}
  with_transform ? trafos = SparseTrafoElem{T, dense_matrix_type(T)}[] : nothing
  @inbounds for i = nrows(B)-1:-1:1
    if B[i].pos[1] > limit
      continue
    end
    if with_transform
      B[i], new_trafos = reduce_right(B, B[i], B[i].pos[1]+1, with_transform_val; limit, new_g = true)
      # We are updating the ith row
      # Have to adjust the transformations
      for t in new_trafos
        t.j = i
      end
      # Now append
      append!(trafos, new_trafos)
    else
      B[i] = reduce_right(B, B[i], B[i].pos[1]+1; limit, new_g = true)
    end
  end
  with_transform ? (return B, trafos) : B
end

@doc raw"""
    hnf_kannan_bachem(A::SMat{ZZRingElem}) -> SMat{ZZRingElem}

Compute the Hermite normal form of $A$ using the Kannan-Bachem algorithm.
"""
function hnf_kannan_bachem(A::SMat{T}, with_transform_val::Val{with_transform} = Val(false); truncate::Bool = false, full_hnf::Bool = true, auto::Bool = false, limit::Int = typemax(Int)) where {T, with_transform}

  @vprintln :HNF 1 "Starting Kannan Bachem HNF on:"
  @vprint :HNF 1 A
  @vprintln :HNF 1 " with density $(density(A)); truncating $truncate"
  @v_do :HNF 1 trt = rt = time_ns()
  if auto
    @req full_hnf "auto can only be used with full hnf"
    full_hnf = false #we don't start with full reduction
  end

  full_hnf = true
  auto = false

  with_transform ? trafos = SparseTrafoElem{T, dense_matrix_type(T)}[] : nothing

  B = sparse_matrix(base_ring(A))
  B.c = A.c
  nc = 0
  stable_piv = 0
  local new_row::Bool
  @inbounds for i=A
    if with_transform
      q, w, new_trafos = reduce_full(B, i, with_transform_val; full_hnf, limit)
      append!(trafos, new_trafos)
    else
      q, w = reduce_full(B, i; full_hnf, limit)
    end

    if length(q) > 0 && q.pos[1] <= limit
      p = find_row_starting_with(B, q.pos[1])
      if p > length(B.rows)
        # Appending row q to B
        # Do not need to track a transformation
        push!(B, q)
      else
        # Inserting row q at position p
        insert!(B.rows, p, q)
        B.r += 1
        B.nnz += length(q)
        B.c = max(B.c, q.pos[end])
        # The transformation is swapping pairwise from nrows(B) to p.
        # This should be the permutation matrix corresponding to
        # (k k-1)(k-1 k-2) ...(p+1 p) where k = nrows(B)
        if with_transform
          for j in nrows(B):-1:(p+1)
            push!(trafos, sparse_trafo_swap(T, j, j - 1))
          end
        end
      end
      push!(w, q.pos[1])
      new_row = true
    else
      # Row i was reduced to zero
      with_transform ? push!(trafos, sparse_trafo_move_row(T, nrows(B) + 1, nrows(A))) : nothing
      new_row = false 
      if length(q) > 0 
        push!(B, q)
      end
    end
   
    if limit < ncols(A)
      ws = [x for x = w if x <= limit]
    else
      ws = w
    end

    if new_row && length(ws) == 1
      #do nothing new
    elseif length(ws) == 0 
      stable_piv += 1
      if stable_piv > 2 && auto && !full_hnf 
        @vprintln :HNF 1 "switching to full HNF, at rows $(nrows(B)), and bitsize $(maximum(nbits, B))"
        if with_transform
          @vtime :HNF 1 B, new_trafos = upper_triag_to_hnf!(B, with_transform_val; limit)
          append!(trafos, new_trafos)
        else
          @vtime :HNF 1 B = upper_triag_to_hnf!(B, with_transform_val; limit)
        end
        full_hnf = true
      end
    else
      stable_piv = 0
      if auto 
        full_hnf && @vprintln :HNF 1 "switching full HNF off again"
        full_hnf = false
      end
    end
    if full_hnf && length(w) > 0
      if with_transform
        new_trafos = reduce_up(B, w, with_transform_val; limit)
        append!(trafos, new_trafos)
      else
        reduce_up(B, w; limit)
      end
    end

    @v_do :HNF 1 begin
      if nc % 10 == 0
        st = time_ns()
        if (st - rt)*1e-9 > 10
          println("Now at $nc rows of $(nrows(A)), HNF so far $(nrows(B)) rows")
          println("Current density: $(density(B))")
          println("and size of largest entry: $(maximum(nbits, B)) bits")
          println("used $((st-rt)*1e-9) sec. for last block, $((st-trt)*1e-9) sec. total")
          rt = st
        end
      end
    end
    nc += 1
  end
  if auto && !full_hnf
    @vprintln :HNF 1 "final full HNF, $(nrows(B)), $(maximum(nbits, B))"
    if with_transform
      @vtime :HNF 1 B, new_trafos = upper_triag_to_hnf!(B, with_transform_val; limit)
      append!(trafos, new_trafos)
    else
      @vtime :HNF 1 B = upper_triag_to_hnf!(B, with_transform_val; limit)
    end
  end

  if !truncate
    for i in 1:(nrows(A) - nrows(B))
      push!(B, sparse_row(base_ring(A)))
    end
  end

  with_transform ? (return B, trafos) : (return B)
end

@doc raw"""
    hnf(A::SMat{ZZRingElem}) -> SMat{ZZRingElem}

Return the upper right Hermite normal form of $A$.

$truncate$ indicates if zero rows should be returned or disgarded,
when $full_hnf$ is set to $false$ only an upper triangular matrix is computed,
ie. the upwards reduction is not performed.

$auto$ if set to true selects a different elemination strategy - here the
upwards reduction is temporarily switched off.

$limit$ marks the last column where size reduction happens, so
calling $hnf$ on $hcat(A, identity_matrix(SMat, ZZ, nrows(A)))$ with 
$limit$ set to $ncols(A)$ should produce a non-reduced transformation matrix
in the right. If $limit$ is not set, the transformation matrix will also be
partly triangular.
"""
function hnf(A::SMat{ZZRingElem}; truncate::Bool = false, full_hnf::Bool = true, auto::Bool = false, limit::Int=typemax(Int))
  return hnf_kannan_bachem(A; truncate, full_hnf, auto, limit)
end

@doc raw"""
    hnf!(A::SMat{ZZRingElem})

Inplace transform of $A$ into upper right Hermite normal form.
"""
function hnf!(A::SMat{ZZRingElem}; truncate::Bool = false, full_hnf::Bool = true, auto::Bool = false)
  B = hnf(A; truncate, full_hnf, auto)
  A.rows = B.rows
  A.nnz = B.nnz
  A.r = B.r
  A.c = B.c
end

@doc raw"""
    diagonal_form(A::SMat{ZZRingElem}) -> SMat{ZZRingElem}

A matrix $D$ that is diagonal and obtained via unimodular row and column operations.
Like a snf without the divisibility condition.
"""
function diagonal_form(A::SMat{ZZRingElem})
  sa = size(A)
  if nrows(A) < ncols(A)
    A = transpose(A)
  else
    A = deepcopy(A)
  end
  el_div = ZZRingElem[]
  while true
    r = nrows(A)
    hnf!(A; auto = true, truncate = true)
    #find the essential art of the hnf: the 1st row not starting with 1
    #the top part will automatically give eldivs of 1, the hnf would just
    #reduce the part to zero...
    i = 1
    while i <= nrows(A) && A[i].values.ar[1] == 1
      i += 1
    end
    append!(el_div, [ZZ(1) for j = 1:i-1])
    if i > 1
      A = sub(A, i:nrows(A), 1:ncols(A))
    end
    if all(x->length(x) == 1, A.rows)
      for x = A.rows
        push!(el_div, x.values[1])
      end
      D = sparse_matrix(ZZ, sa[1], sa[2])
      for i = 1:length(el_div)
        push!(D.rows[i].pos, i)
        push!(D.rows[i].values, el_div[i])
      end
      D.nnz = length(el_div)
      return D
    end
    A = transpose(A)
  end
end

function reduce_right!(A::SMat{ZZRingElem}, b::SRow{ZZRingElem})
  c = reduce_right(A, b)
  b.pos, c.pos = c.pos, b.pos
  b.values, c.values = c.values, b.values
  return b
end
