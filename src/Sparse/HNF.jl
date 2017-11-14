function reduce(A::SMat{nmod}, g::SRow{nmod})
  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  # supposed to be a field...
  if A.r == A.c
    return SRow{nmod}()
  end
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
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
    for i=1:length(g)
      g.values[i] *= li
    end
  end
  return g
end

function reduce(A::SMat{fmpz}, g::SRow{fmpz})
  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  #until the 1st (pivot) change in A
  new_g = false
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      if g.values[1] < 0
        if !new_g
          g = copy(g)
        end
        for i=1:length(g.values)
          g.values[i] *= -1
        end
      end
      return g
    end
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      g = Hecke.add_scaled_row(A[j], g, - divexact(p, A.rows[j].values[1]))
      new_g = true
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @hassert :HNF 2  x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      new_g = true
      @hassert :HNF 2  A[j].values[1] == x
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    end
  end
  if length(g.values) > 0 && g.values[1] < 0
    if !new_g
      g = copy(g)
    end
    for i=1:length(g.values)
      g.values[i] *= -1
    end
  end
  return g
end

function reduce(A::SMat{fmpz}, g::SRow{fmpz}, m::fmpz)
  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  new_g = false
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      if !new_g
        g = copy(g)
      end
      if mod_sym(g.values[1], m) < 0 
        for i=1:length(g.values)
          g.values[i] *= -1
        end
        @hassert :HNF 3  mod_sym(g.values[1], m) > 0
      end
      mod_sym!(g, m)
      return g
    end
    st_g = 2
    st_A = 2
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      g = add_scaled_row(A[j], g, - divexact(p, A.rows[j].values[1]))
      new_g = true
      mod_sym!(g, m)
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @hassert :HNF 2  x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      new_g = true
#      @hassert :HNF 2  A[j].values[1] == x
      mod_sym!(g, m)
      mod_sym!(A[j], m)
#      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
#      @hassert :HNF 2  A[j].values[1] > 0
    end
  end
  if !new_g
    g = copy(g)
  end
  if length(g.values) > 0 && mod_sym(g.values[1], m) < 0
    for i=1:length(g.values)
      g.values[i] *= -1
    end
  end
  Hecke.mod_sym!(g, m)
#  @hassert :HNF 1  length(g.pos) == 0 || g.values[1] >= 0
  return g
end

doc"""
    saturate(A::fmpz_mat) -> fmpz_mat
    saturate(A::SMat{fmpz}) -> SMat{fmpz}

> Computes the \code{saturation} of $A$, ie. a basis for $Q\otimes [A] \meet Z^n$.
> Equivalently, $TA$ for $T \in \Gl(n, Q)$ s.th. $TA\in Z^{n\times m}$ and
> the elementary divisors of $TA$ are all trivial.
> The SMat-case is using the dense code.
"""
function saturate(A::fmpz_mat)
  #row saturation: want
  #  TA in Z, T in Q and elem_div TA = [1]
  #
  #  AT = H (in HNF), then A = HT^-1 and H^-1A = T^-1
  # since T is uni-mod, H^-1 A is in Z with triv. elm. div

  H = hnf(A')
  H = H'
  Hi, d = pseudo_inv(sub(H, 1:rows(H), 1:rows(H)))
  S = Hi*A
  Sd = divexact(S, d)
#  @hassert :HNF 1  d*Sd == S
  return Sd
end

function saturate(A::SMat{fmpz})
  return SMat(saturate(fmpz_mat(A)))
end

################################################################################
#
#  Hermite normal form using Kannan-Bachem algorithm
#
################################################################################

doc"""
    find_row_starting_with(A::SMat, p::Int)
 
> Tries to find the index $i$ s.th. $A[i,p] != 0$ and $A[i, p-j] = 0$
> holds for all $j$.
> Assumes $A$ to be upper-triangular.
> If such an index does not exist, find the smallest index
> larger.
"""
function find_row_starting_with(A::SMat, p::Int)
#  @hassert :HNF 1  isupper_triangular(A)
  start = 0
  stop = rows(A)+1
  while start < stop - 1
    mid = div((stop + start), 2)
    if A[mid].pos[1] == p
      return mid
    elseif A[mid].pos[1] < p
      start = mid 
    else
      stop = mid 
    end
  end
  return stop
end

# If trafo is set to Val{true}, then additionaly an Array of transformations
# is returned.
function reduce_up(A::SMat{fmpz}, piv::Array{Int, 1},
                                  trafo::Type{Val{N}} = Val{false}) where N

  with_trafo = (trafo == Val{true})
  if with_trafo
    trafos = []
  end

  sort!(piv)
  p = find_row_starting_with(A, piv[end])

  for red=p-1:-1:1
    # the last argument should be the smallest pivot larger then pos[1]
    if with_trafo
      A[red], new_trafos = reduce_right(A, A[red], max(A[red].pos[1]+1, piv[1]), trafo)
      for t in new_trafos
        t.j = red
      end
      append!(trafos, new_trafos)
    else
      A[red] = reduce_right(A, A[red], max(A[red].pos[1]+1, piv[1]))
    end
  end
  with_trafo ? (return trafos) : nothing
end

# If trafo is set to Val{true}, then additionaly an Array of transformations
# is returned.
doc"""
    reduce_full(A::SMat{fmpz}, g::SRow{fmpz}, trafo::Type{Val{Bool}} = Val{false})

> Reduces $g$ modulo $A$, that is, all entries in $g$ in columns where $A$ has
> pivot elements for those columns, reduce $g$ modulo the pivots.
> Assumes $A$ to be upper-triangular.  
>
> The second return value is the array of pivot element of $A$ that
> changed.
>
> If `trafo` is set to `Val{true}`, then additionally an array of transformations
> is returned.
"""
function reduce_full(A::SMat{fmpz}, g::SRow{fmpz}, trafo::Type{Val{T}} = Val{false}) where T
#  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A

  with_trafo = (trafo == Val{true})
  no_trafo = (trafo == Val{false})

  if with_trafo
    trafos = []
  end 

  new_g = false

  piv = Int[]
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      if g.values[1] < 0
        # Multiply row g by -1
        if with_trafo
          push!(trafos, TrafoScale{fmpz}(rows(A) + 1, fmpz(-1)))
        end
        if !new_g
          g = copy(g)
        end
        for i=1:length(g.values)
          g.values[i] *= -1
        end
      end

      if with_trafo
        g, new_trafos  = reduce_right(A, g, 1, trafo)
        append!(trafos, new_trafos)
      else
        g = reduce_right(A, g)
      end
      new_g = true

      if A.r == A.c
        @hassert :HNF 1  length(g) == 0 || min(g) >= 0
      end

      with_trafo ? (return g, piv, trafos) : (return g, piv)

    end
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      sca =  -divexact(p, A.rows[j].values[1])
      g = Hecke.add_scaled_row(A[j], g, sca)
      new_g = true
      with_trafo ? push!(trafos, TrafoAddScaled(j, rows(A) + 1, sca)) : nothing
      @hassert :HNF 1  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @hassert :HNF 1  x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      new_g = true
      if with_trafo
        push!(trafos, TrafoParaAddScaled(j, rows(A) + 1, a, b, c, d))
      end
      @hassert :HNF 1  A[j].values[1] == x
      @hassert :HNF 1  length(g)==0 || g.pos[1] > A[j].pos[1]
      push!(piv, A[j].pos[1])
      if with_trafo
        A[j], new_trafos = reduce_right(A, A[j], A[j].pos[1]+1, trafo)
        # We are updating the jth row
        # Have to adjust the transformations
        for t in new_trafos
          t.j = j
        end
        # Now append
        append!(trafos, new_trafos)
      else
        A[j] = reduce_right(A, A[j], A[j].pos[1]+1, trafo)
      end

      if A.r == A.c
        @hassert :HNF 1  min(A[j]) >= 0
      end
    end
  end
  if length(g.values) > 0 && g.values[1] < 0
    if !new_g
      g = copy(g)
    end
    for i=1:length(g.values)
      g.values[i] *= -1
    end
    with_trafo ? push!(trafos, TrafoScale{fmpz}(rows(A) + 1, fmpz(-1))) : nothing
  end
  if with_trafo
    g, new_trafos = reduce_right(A, g, 1, trafo)
    append!(trafos, new_trafos)
  else
    g = reduce_right(A, g)
  end
  if A.r == A.c
    @hassert :HNF 1  length(g) == 0 || min(g) >= 0
  end
  with_trafo ? (return g, piv, trafos) : (return g, piv)
end

function reduce_right(A::SMat{fmpz}, b::SRow{fmpz}, start::Int = 1, trafo::Type{Val{N}} = Val{false}) where N
  with_trafo = (trafo == Val{true})
  with_trafo ? trafos = [] : nothing
  if length(b.pos) == 0
    with_trafo ? (return b, trafos) : return b
  end
  j = 1
  while j <= length(b.pos) && b.pos[j] < start
    j += 1
  end
  if j > length(b.pos)
    with_trafo ? (return b, trafos) : return b
  end
  p = find_row_starting_with(A, b.pos[j])
  if p > rows(A)
    with_trafo ? (return b, trafos) : return b
  end
  @hassert :HNF 1  A[p] != b
  while j <= length(b.pos)
    while p<rows(A) && A[p].pos[1] < b.pos[j]
      p += 1
    end
    if A[p].pos[1] == b.pos[j]
      q, r = divrem(b.values[j], A[p].values[1])
      if r < 0
        q -= 1
        r += A[p].values[1]
        @hassert :HNF 1  r >= 0
      end
      if q != 0
        b = Hecke.add_scaled_row(A[p], b, -q)
        with_trafo ? push!(trafos, TrafoAddScaled(p, rows(A) + 1, -q)) : nothing
        if r == 0
          j -= 1
        else
          @hassert :HNF 1  b.values[j] == r
        end
      end
    end
    j += 1
  end
  with_trafo ? (return b, trafos) : return b
end

doc"""
    hnf_kannan_bachem(A::SMat{fmpz})

> Hermite Normal Form of $A$ using the Kannan-Bachem algorithm to avoid
> intermediate coefficient swell.
"""
function hnf_kannan_bachem(A::SMat{fmpz}, trafo::Type{Val{N}} = Val{false}) where N
  @vprint :HNF 1 "Starting Kannan Bachem HNF on:\n"
  @vprint :HNF 1 A
  @vprint :HNF 1 "with density $(A.nnz/(A.c*A.r))"

  with_trafo = (trafo == Val{true})
  with_trafo ? trafos = [] : nothing

  B = SMat(FlintZZ)
  B.c = A.c
  nc = 0
  for i=A
    if with_trafo 
      q, w, new_trafos = reduce_full(B, i, trafo)
      append!(trafos, new_trafos)
    else
      q, w = reduce_full(B, i)
    end

    if length(q) > 0
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
        # The transformation is swapping pairwise from rows(B) to p.
        # This should be the permutation matrix corresponding to
        # (k k-1)(k-1 k-2) ...(p+1 p) where k = rows(B)
        if with_trafo
          for j in rows(B):-1:(p+1)
            push!(trafos, TrafoSwap{fmpz}(j, j - 1))
          end
        end
      end
      push!(w, q.pos[1])
    else
      # Row i was reduced to zero
      with_trafo ? push!(trafos, TrafoDeleteZero{fmpz}(rows(B) + 1)) : nothing
    end
    if length(w) > 0
      if with_trafo
        new_trafos = reduce_up(B, w, trafo)
        append!(trafos, new_trafos)
      else
        reduce_up(B, w)
      end
    end
    @v_do :HNF 1 begin
      if nc % 10 == 0
        println("Now at $nc rows of $(A.r), HNF so far $(B.r) rows")
        println("Current density: $(B.nnz/(B.c*B.r))")
        println("and size of largest entry: $(nbits(maxabs(B))) bits")
      end
    end
    nc += 1
  end
  with_trafo ? (return B, trafos) : (return B)
end

doc"""
    hnf(A::SMat{fmpz}) -> SMat{fmpz}

> The Hermite Normal Form of $A$, ie. an upper triangular matrix with non-negative
> entries in echelon form that is row-equivalent to $A$.
> Currently, Kannan-Bachem is used.
"""
function hnf(A::SMat{fmpz})
  return hnf_kannan_bachem(A)
end

doc"""
    hnf!(A::SMat{fmpz})

> In-place reduction of $A$ into Hermite Normal Form.
> Currently, Kannan-Bachem is used.
"""
function hnf!(A::SMat{fmpz})
  B = hnf(A)
  A.rows = B.rows
  A.nnz = B.nnz
  A.r = B.r
  A.c = B.c
end

