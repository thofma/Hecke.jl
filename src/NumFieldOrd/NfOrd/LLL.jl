add_verbosity_scope(:LLL)
add_assertion_scope(:LLL)

################################################################################
#
#  Special functions for real fields and quadratic fields
#
################################################################################

function _lll_gram(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  K = nf(order(A))
  @assert is_totally_real(K)
  g = trace_matrix(A)
  @hassert :LLL 1 !iszero(det(g))
  @hassert :LLL 1 is_positive_definite(g)
  l, t = lll_gram_with_transform(g)
  return FakeFmpqMat(l, ZZRingElem(1)), t::ZZMatrix
end

function _lll_quad(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  K = nf(order(A))
  @assert degree(K) == 2 && discriminant(order(A)) < 0
  b = basis(A)
  a1 = 2*numerator(norm(b[1]))
  a2 = 2*numerator(norm(b[2]))
  a12 = numerator(trace(b[1] * conjugate_quad(K(b[2]))))
  g = matrix(FlintZZ, 2, 2, [a1, a12, a12, a2])
  @hassert :LLL 1 is_positive_definite(g)
  l, t = lll_gram_with_transform(g)
  return FakeFmpqMat(l, ZZRingElem(1)), t::ZZMatrix
end

function _lll_CM(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  OK = order(A)
  @vprintln :LLL 3 "Reduction"
  M = _minkowski_matrix_CM(OK)
  @vtime :LLL 3 BM, T = lll_with_transform(basis_matrix(A, copy = false), LLLContext(0.3, 0.51))
  g = BM*M*transpose(BM)
  @hassert :LLL 1 is_positive_definite(g)
  @vtime :LLL 3 l, t = lll_gram_with_transform(g)
  return FakeFmpqMat(l, ZZRingElem(1)), t*T::ZZMatrix
end

################################################################################
#
#  lll for ideals
#
################################################################################

function lll(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::ZZMatrix = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)

  K = nf(order(A))

  if iszero(v)
    if is_totally_real(K)
      #in this case the gram-matrix of the minkowski lattice is the trace-matrix
      #which is exact.
      return _lll_gram(A)
    elseif degree(K) == 2 && discriminant(order(A)) < 0
       #in this case the gram-matrix of the minkowski lattice is related to the
      #trace-matrix which is exact.
      return _lll_quad(A)
    end
    if is_cm_field_known(K) || is_automorphisms_known(K)
      if is_cm_field(K)[1]
        return _lll_CM(A)
      end
    end
  end
  #General case. _lll could fail, we need a try and catch in a loop
  local t::ZZMatrix
  local l::FakeFmpqMat
  while true
    if prec > 2^18
      error("Something wrong in short_elem")
    end
    try
      l, t = _lll(A, v, prec = prec)
      break
    catch e
      if !(e isa LowPrecisionLLL || e isa InexactError)
        rethrow(e)
      end
    end
    prec = 2 * prec
  end
  return l, t

end


function _lll(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::ZZMatrix = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)
  K = nf(order(A))
  n = degree(order(A))
  prec = max(prec, 4*n)

  ctx1 = LLLContext(0.5, 0.51)
  l, t1 = lll_with_transform(basis_matrix(A, copy = false), ctx1)

  if iszero(v)
    d = minkowski_gram_mat_scaled(order(A), prec)
    ccall((:fmpz_mat_mul, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZMatrix}), d, d, transpose(l))
    ccall((:fmpz_mat_mul, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{ZZMatrix}), d, l, d)
    g = zero_matrix(FlintZZ, n, n)
    den = ZZRingElem(1)
    sv = ZZRingElem(0)
  else
    c = minkowski_matrix(nf(order(A)), prec) ## careful: current iteration
                                          ## c is NOT a copy, so don't change.
    b = l*basis_matrix(FakeFmpqMat, order(A), copy = false)


    rt_c = roots_ctx(K)
    if !isdefined(rt_c, :cache_z1)
      rt_c.cache_z1 = zero_matrix(FlintZZ, n, n)
      rt_c.cache_z2 = zero_matrix(FlintZZ, n, n)
    end

    d::ZZMatrix = rt_c.cache_z1
    g::ZZMatrix = rt_c.cache_z2

    round_scale!(g, c, prec)

    @v_do :ClassGroup 2 println("using inf val", v)
    c = deepcopy(c)
    mult_by_2pow_diag!(c, v)
    sv = max(ZZRingElem(0), sum(v[1,i] for i=1:ncols(l)))


    round_scale!(d, c, prec)
    ccall((:fmpz_mat_mul, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix},  Ref{ZZMatrix}), g, (b.num), d)
    den = b.den

    ccall((:fmpz_mat_gram, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}), d, g)
    shift!(d, -prec)
  end

  prec = div(prec, 2)
  shift!(d, -prec)  #TODO: remove?

  for i=1:n
    fmpz_mat_entry_add_ui!(d, i, i, UInt(nrows(d)))
  end

  ctx = Nemo.LLLContext(0.99, 0.51, :gram)

  ccall((:fmpz_mat_one, libflint), Nothing, (Ref{ZZMatrix}, ), g)
  ccall((:fmpz_lll, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{Nemo.LLLContext}), d, g, ctx)

  l, t = d, g
  ## test if entries in l are small enough, if not: increase precision
  ## or signal that prec was too low
  @v_do :ClassGroup 2 printstyled("lll basis length profile\n", color=:green);
  @v_do :ClassGroup 2 for i = 1:nrows(l)
    print(Float64(div(l[i,i], ZZRingElem(2)^prec*den*den)*1.0), " : ")
  end
  @v_do :ClassGroup 2 println("")
  if nbits(maximum(abs, t)) >  div(prec, 2)
    @v_do :ClassGroup 2 printstyled("lll trafo too large\n", color=:red);
    throw(LowPrecisionLLL())
  end
  ## lattice has lattice disc = order_disc * norm^2
  ## lll needs to yield a basis sth
  ## l[1,1] = |b_i|^2 <= 2^((n-1)/2) disc^(1/n)
  ## and prod(l[i,i]) <= 2^(n(n-1)/2) disc
  n = nrows(l)
  disc = abs(discriminant(order(A)))*norm(A)^2 * den^(2*n) * ZZRingElem(2)^(2*sv)
  di = iroot(disc, n) + 1
  di *= ZZRingElem(2)^(div(n+1,2)) * ZZRingElem(2)^prec

  if compare_index(l, 1, 1, di) > 0
    @v_do :ClassGroup 2 printstyled("LLL basis too large\n", color = :red);
    @v_do :ClassGroup 3 println("bound is ", di, " value at ", 1, " is ", l[1,1]);
    throw(LowPrecisionLLL())
  end
  pr = prod_diagonal(l)
  if pr > ZZRingElem(2)^(div(n*(n-1), 2)) * disc * ZZRingElem(2)^(n*prec)
    @v_do :ClassGroup 2 printstyled("LLL basis too large\n", color = :red)
    @v_do :ClassGroup 2 println("prod too large: ", nbits(pr), " > 2^(n(n-1)/2) disc = ", nbits(ZZRingElem(2)^(div(n*(n-1), 2)) * disc * ZZRingElem(2)^(n*prec)))
    throw(LowPrecisionLLL())
  end

  return FakeFmpqMat(deepcopy(l), ZZRingElem(2)^prec), t*t1
end


###############################################################################
#
#  LLL computation for orders
#
###############################################################################

@doc raw"""
    lll(M::AbsNumFieldOrder) -> AbsNumFieldOrder

The same order, but with the basis now being LLL reduced wrt. the Minkowski metric.
"""
function lll(M::AbsNumFieldOrder; prec::Int = 100)

  if isdefined(M, :lllO)
    return M.lllO::typeof(M)
  end
  K = nf(M)

  if is_totally_real(K)
    On =  _lll_gram(M)
    M.lllO = On
    return On::typeof(M)
  end

  if degree(K) == 2
    On = _lll_quad(M)
    M.lllO = On
    return On::typeof(M)
  end

  if is_cm_field_known(K) || is_automorphisms_known(K)
    fl, f_conj = is_cm_field(K)
    if fl
      On = _lll_CM(M)
      M.lllO = On
      return On::typeof(M)
    end
  end

  return _lll(M, prec)
end


#for totally real field, the T_2-Gram matrix is the trace matrix, hence exact.
function _lll_gram(M::AbsNumFieldOrder)
  K = nf(M)
  @assert is_totally_real(K)
  g = trace_matrix(M)
  w = lll_gram_with_transform(g)[2]
  On = AbsNumFieldOrder(K, w*basis_matrix(FakeFmpqMat, M, copy = false))
  On.is_maximal = M.is_maximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  return On
end

function _minkowski_matrix_CM(M::AbsNumFieldOrder)
  if isdefined(M,  :minkowski_gram_CMfields)
    return M.minkowski_gram_CMfields
  end
  B = basis(M, nf(M))
  g = _exact_minkowski_matrix(B)
  M.minkowski_gram_CMfields = g
  return g
end

function _exact_minkowski_matrix(B::Vector{T}) where T <: NumFieldElem
  K = parent(B[1])
  if is_totally_real(K)
    return trace_matrix(B)
  else
    return _minkowski_via_approximation(B)
  end
end

function _minkowski_via_approximation(B::Vector{T}) where T <: NumFieldElem
  K = parent(B[1])
  n = length(B)
  g = zero_matrix(FlintZZ, n, n)
  prec = 16
  imgs = Vector{Vector{ArbFieldElem}}(undef, n)
  for i = 1:n
    imgs[i] = minkowski_map(B[i], prec)
  end
  i = 1
  t = ArbFieldElem()
  while i <= n
    j = i
    while j <= n
      el = imgs[i][1]*imgs[j][1]
      for k = 2:n
        mul!(t, imgs[i][k], imgs[j][k])
        add!(el, el, t)
      end
      fl, r = unique_integer(el)
      if fl
        g[i, j] = r
        g[j, i] = r
        j += 1
      else
        prec *= 2
        for k = i:n
          imgs[k] = minkowski_map(B[k], prec)
        end
      end
    end
    i += 1
  end
  return g
end

function trace_matrix(b::Vector{T}) where T <: NumFieldElem
  K = parent(b[1])
  n = absolute_degree(K)
  g = zero_matrix(FlintZZ, n, n)
  aux = K()
  for i = 1:n
    mul!(aux, b[i], b[i])
    t = absolute_tr(aux)
    @assert isinteger(t)
    g[i, i] = numerator(t)
    for j in (i + 1):n
      mul!(aux, b[i], b[j])
      t = absolute_tr(aux)
      @assert isinteger(t)
      g[i, j] = numerator(t)
      g[j, i] = numerator(t)
    end
  end
  return g
end


function _lll_CM(M::AbsNumFieldOrder)
  K = nf(M)
  g = _minkowski_matrix_CM(M)
  @vprintln :LLL 1 "Now LLL"
  @hassert :LLL 1 is_positive_definite(g)
  w = lll_gram_with_transform(g)[2]
  On = AbsNumFieldOrder(K, w*basis_matrix(FakeFmpqMat, M, copy = false))
  On.is_maximal = M.is_maximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  return On
end


function _lll_quad(M::AbsNumFieldOrder)
  K = nf(M)
  b = basis(M)
  a1 = 2*numerator(norm(b[1]))
  a2 = 2*numerator(norm(b[2]))
  a12 = numerator(trace(b[1] * conjugate_quad(K(b[2]))))
  g = matrix(FlintZZ, 2, 2, ZZRingElem[a1, a12, a12, a2])
  @hassert :ClassGroup 1 is_positive_definite(g)
  w = lll_gram_with_transform(g)[2]
  On = AbsNumFieldOrder(K, w*basis_matrix(FakeFmpqMat, M, copy = false))
  On.is_maximal = M.is_maximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  return On
end

function _lll(M::AbsNumFieldOrder, prec::Int)

  K = nf(M)
  n = degree(K)
  M1 = _ordering_by_T2(M)
  prec = max(prec, 10*n)
  prec = max(prec, 100 + 25*div(degree(M), 3) + Int(round(log(abs(discriminant(M))))))

  if n > 10
    if n > 100
      prec, M1 = lll_precomputation(M1, prec)
    end
    prec, M1 = lll_precomputation(M1, prec)
  end
  M1, prec = _lll_with_parameters(M1, (0.73, 0.51), prec)
  M1 = _lll_with_parameters(M1, (0.99, 0.51), prec)[1]
  M.lllO = M1
  return M1
end

function _ordering_by_T2(M::AbsNumFieldOrder, prec::Int = 32)

  K = nf(M)
  B = basis(M, K)
  ints = ZZRingElem[lower_bound(t2(x, prec), ZZRingElem) for x in B]
  p = sortperm(ints)
  On = AbsNumFieldOrder(B[p])
  On.is_maximal = M.is_maximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  return On
end


function subsets_it(n::Int, k::Int)
  if n < k
    return (Vector{Int}[])
  end
  if k == 0
    return ([Int[]])
  end
  if n == k
    return ([Int[i for i = 1:n]])
  end
  if k == 1
    return ([Int[i] for i = 1:n])
  end
  res = subsets_it(n-1, k-1)
  res1 = (push!(x, n) for x in res)
  res2 = subsets_it(n-1, k)
  res3 = [res1, res2]
  return (x for y in res3 for x in y)
end


#Inefficient, but at least it works.
@doc raw"""
    subsets(n::Int, k::Int)

Return a vector of all ordered `k`-element subsets of `1..n`.
"""
function subsets(n::Int, k::Int)
  if n < k
    return Vector{Int}[]
  end
  if k == 0
    return Vector{Int}[Int[]]
  end
  if n == k
    return Vector{Int}[Int[i for i = 1:n]]
  end
  if k == 1
    return Vector{Int}[Int[i] for i = 1:n]
  end
  res = subsets(n-1, k-1)
  for x in res
    push!(x, n)
  end
  append!(res, subsets(n-1, k))
  return res
end


@doc raw"""
    subsets(v::Vector{T}, k::Int) where T

Return a vector of all ordered `k`-element sub-vectors of `v`.
"""
function subsets(v::Vector{T}, k::Int) where T
  indices = subsets(length(v), k)
  res = Vector{T}[]
  for i in indices
    si = Vector{T}(undef, k)
    ind = 1
    for j in i
      si[ind] = v[j]
      ind += 1
    end
    push!(res, si)
  end
  return res
end

function _has_trivial_intersection(v::Vector{Vector{Int}}, V::Vector{Vector{Int}})
  for z in v
    for w in V
      if !isempty(intersect(z, w))
        return false
      end
    end
  end
  return true
end

function lll_precomputation(M::AbsNumFieldOrder, prec::Int, nblocks::Int = 4)
  n = degree(M)
  K = nf(M)
  dimension_blocks = div(n, nblocks)
  blocks = Vector{Int}[]
  for i = 1:nblocks-1
    int = (dimension_blocks*(i-1)+1):dimension_blocks*i
    push!(blocks, collect(int))
  end
  int = (dimension_blocks*(nblocks-1)+1):n
  push!(blocks, collect(int))
  g = identity_matrix(FlintZZ, n)
  new_prec = prec
  to_do = subsets(blocks, 2)
  done = falses(length(to_do))
  blocks_selection = Vector{Int}[]
  while !all(done)
    block = 1
    while block < length(to_do)+1 && (done[block] || !_has_trivial_intersection(to_do[block], blocks_selection))
      block += 1
    end
    if block == length(to_do)+1
      blocks_selection = Vector{Int}[]
      On = AbsNumFieldOrder(K, g*basis_matrix(FakeFmpqMat, M, copy = false))
      On.is_maximal = M.is_maximal
      if isdefined(M, :index)
      On.index = M.index
      end
      if isdefined(M, :disc)
        On.disc = M.disc
      end
      if isdefined(M, :gen_index)
        On.gen_index = M.gen_index
      end
      M = On
      g = identity_matrix(FlintZZ, n)
      continue
    end
    indices = vcat(to_do[block][1], to_do[block][2])
    @vprintln :LLL 3 "Simplifying block $(block)"
    prec, g1 = _lll_sublattice(M, indices, prec = prec)
    _copy_matrix_into_matrix(g, indices, indices, g1)
    done[block] = true
    push!(blocks_selection, indices)
    @vprintln :LLL 3 "Precision: $(prec)"
  end
  @vprintln :LLL 3 "Precomputation finished with precision $(prec)"
  return prec, M
end



function _lll_sublattice(M::AbsNumFieldOrder, u::Vector{Int}; prec = 100)
  K = nf(M)
  n = degree(M)
  l = length(u)
  @vprintln :LLL 3 "Block of dimension $(l)"
  prec = max(prec, 10*n)
  local g::ZZMatrix

  bas = basis(M, K)[u]
  profile_sub = nbits(prod(Hecke.upper_bound(ZZRingElem, t2(x)) for x in bas))
  @vprintln :LLL 3 "Starting with profile $(profile_sub)"
  while true
    local d::ZZMatrix
    @vprintln :LLL 3 "Computing Minkowski matrix"
    while true
      @vprintln :LLL 3 "Precision: $(prec)"
      try
        d = minkowski_gram_mat_scaled(M, prec)
        break
      catch e
        prec = prec*2
      end
    end
    @vprintln :LLL 3 "Minkowski matrix computed"
    g = identity_matrix(FlintZZ, l)
    d1 = sub(d, u, u)
    prec = div(prec, 2)
    shift!(d1, -prec)  #TODO: remove?
    for i=1:l
      fmpz_mat_entry_add_ui!(d1, i, i, UInt(l))
    end
    ctx = Nemo.LLLContext(0.99, 0.51, :gram)
    @vtime :LLL 3 ccall((:fmpz_lll, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{Nemo.LLLContext}), d1, g, ctx)

    if nbits(maximum(abs, g)) <= div(prec, 2)
      prec *= 2
      break
    end
    @vprintln :LLL 3 "Still in the loop"
    prec *= 4
  end
  @vprintln :LLL 3 "Computing the profile of the new basis"
  new_basis = g*basis_matrix(bas, FakeFmpqMat)
  els = elem_type(K)[elem_from_mat_row(K, new_basis.num, i, new_basis.den) for i = 1:nrows(new_basis)]
  new_profile = nbits(prod(Hecke.upper_bound(ZZRingElem, t2(x)) for x in els))
  if new_profile <= profile_sub
    @vprintln :LLL 3 "Output a better basis!"
    @vprintln :LLL 3 "New profile: $(new_profile)"
    return prec, g
  else
    @vprintln :LLL 3 "Output the same basis :("
    return prec, identity_matrix(FlintZZ, l)
  end
end


function _lll_with_parameters(M::AbsNumFieldOrder, parameters::Tuple{Float64, Float64}, prec; steps::Int = -1)

  K = nf(M)
  n = degree(M)
  prec = max(prec, 10*n)
  disc = abs(discriminant(M))
  local g::ZZMatrix
  local d::ZZMatrix
  ctx = Nemo.LLLContext(parameters[1], parameters[2], :gram)
  dM = sum(nbits(Hecke.upper_bound(ZZRingElem, t2(x))) for x in basis(M, K))
  @vprintln :LLL 1 "Input profile: $(dM)"
  @vprintln :LLL 1 "Target profile: $(nbits(disc^2)+divexact(n*(n-1), 2))"
  att = 0
  while steps == -1 || att < steps
    att += 1
    if att > 3
      @vprintln :LLL "Having a hard time computing a LLL basis"
    end
    @vprintln :LLL 3 "Attempt number : $(att)"
    while true
      try
        d = minkowski_gram_mat_scaled(M, prec)
        break
      catch e
        if isa(e, InterruptException)
          rethrow(e)
        end
        #TODO: see which are the legal errors here (low prec, ...)
        prec = prec*2
      end
    end

    @vprintln :LLL 3 "Minkowski matrix computed"
    diag_d = prod_diagonal(d)
    g = identity_matrix(FlintZZ, n)

    prec = div(prec, 2)
    shift!(d, -prec)  #TODO: remove?

    for i=1:n
      fmpz_mat_entry_add_ui!(d, i, i, UInt(nrows(d)))
    end
    @vtime :LLL 3 ccall((:fmpz_lll, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}, Ref{Nemo.LLLContext}), d, g, ctx)

    if nbits(maximum(abs, g)) <= div(prec, 2)
      fl = true
      disc = abs(discriminant(M))
      di = iroot(disc, n) + 1
      di *= ZZRingElem(2)^(div(n+1,2)+prec)
      if compare_index(d, 1, 1, di) > 0
        fl = false
      else
        pr = prod_diagonal(d)
        if pr > ZZRingElem(2)^(div(n*(n-1), 2)+(n*prec)) * disc
          fl = false
        end
      end
      if fl
        break
      end
    end
    On = AbsNumFieldOrder(K, g*basis_matrix(FakeFmpqMat, M, copy = false))
    On.is_maximal = M.is_maximal
    if isdefined(M, :index)
      On.index = M.index
    end
    if isdefined(M, :disc)
      On.disc = M.disc
    end
    if isdefined(M, :gen_index)
      On.gen_index = M.gen_index
    end
    prec *= 2
    dOn = nbits(prod(Hecke.upper_bound(ZZRingElem, t2(x)) for x in basis(On, K)))
    if dOn < dM
      @vprintln :LLL 3 "I use the transformation"
      @vprintln :LLL 3 "New profile: $(dOn), was $dM"
      M = On
      dM = dOn
    else
      prec *= 2
    end
    if att == steps
      return M, prec
    end
    @vprintln :LLL 3 "Still in the loop"
  end
  On = AbsNumFieldOrder(K, g*basis_matrix(FakeFmpqMat, M, copy = false))
  On.is_maximal = M.is_maximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  @vprintln :LLL 3 "LLL finished with parameters $(parameters)"
  return On, prec
end

################################################################################
#
#  Applications
#
################################################################################

@doc raw"""
    lll_basis(M::NumFieldOrder) -> Vector{NumFieldElem}

A basis for $M$ that is reduced using the LLL algorithm for the Minkowski metric.
"""
function lll_basis(M::AbsNumFieldOrder)
  M1 = lll(M)
  return basis(M1, nf(M1))
end

@doc raw"""
    lll_basis(I::NumFieldOrderIdeal) -> Vector{NumFieldElem}

A basis for $I$ that is reduced using the LLL algorithm for the Minkowski metric.
"""
function lll_basis(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, v::ZZMatrix = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)
  L, T = lll(A, v, prec=prec)
  S = FakeFmpqMat(T)*basis_matrix(FakeFmpqMat, A, copy = false)*basis_matrix(FakeFmpqMat, order(A), copy = false)
  K = nf(order(A))
  nS = numerator(S)
  dS = denominator(S)
  q = AbsSimpleNumFieldElem[elem_from_mat_row(K, nS, i, dS) for i=1:degree(K)]
  return q
end

function lll_basis(A::AbsSimpleNumFieldOrderFractionalIdeal, v::ZZMatrix = zero_matrix(FlintZZ, 1, 1); prec::Int = 100)
  assure_has_numerator_and_denominator(A)
  L, T = lll(A.num, v, prec=prec)
  S = FakeFmpqMat(T)*basis_matrix(A.num)*basis_matrix(FakeFmpqMat, order(A))
  K = nf(order(A))
  nS = numerator(S)
  dS = denominator(S)
  q = AbsSimpleNumFieldElem[elem_from_mat_row(K, nS, i, dS*A.den) for i=1:degree(K)]
  return q
end

################################################################################
#
#  Short element in ideals
#
################################################################################

function short_elem(A::AbsSimpleNumFieldOrderFractionalIdeal,
                v::ZZMatrix=zero_matrix(FlintZZ, 1,1); prec::Int = 100)
  assure_has_numerator_and_denominator(A)
  return divexact(short_elem(A.num, v, prec = prec), A.den)
end


function short_elem(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},
                v::ZZMatrix = zero_matrix(FlintZZ, 1,1); prec::Int = 100)
  K = nf(order(A))
  t = lll(A, v, prec = prec)[2]
  w = view(t, 1:1, 1:ncols(t))
  mul!(w, w, basis_matrix(A, copy = false))
  c = w*basis_matrix(FakeFmpqMat, order(A), copy = false)
  q = elem_from_mat_row(K, c.num, 1, c.den)
  return q
end

################################################################################
#
#  Reduction of ideals
#
################################################################################

function reduce_ideal(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  B = inv(A)
  b = short_elem(B)
  C = b*A
  simplify(C)
  @assert C.den == 1
  return C.num, b
end

function reduce_product(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, B::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  I = inv(A)
  J = inv(B)
  @vtime :LLL 3 bIJ = _lll_product_basis(I.num, J.num)
  pp = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(order(A), bIJ)
  @vtime :LLL 3 b = divexact(short_elem(pp), I.den * J.den)
  AB = A*B
  C = b*AB
  simplify(C)
  @assert isone(C.den)
  return C.num, b
end


function reduce_ideal(A::AbsSimpleNumFieldOrderFractionalIdeal)
  B = inv(A)
  b = short_elem(B.num)
  C = divexact(b, B.den)*A
  simplify(C)
  @assert C.den == 1
  return C.num, divexact(b, B.den)
end


@doc raw"""
    reduce_ideal(A::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FacElem{AbsSimpleNumFieldElem}

Computes $B$ and $\alpha$ in factored form, such that $\alpha B = A$.
"""
function reduce_ideal(I::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  @assert !isempty(I.fac)
  O = order(first(keys(I.fac)))
  K = nf(O)
  fst = true
  a = FacElem(Dict{AbsSimpleNumFieldElem, ZZRingElem}(one(K) => ZZRingElem(1)))
  A = ideal(O, 1)
  for (k, v) = I.fac
    @assert order(k) === O
    if iszero(v)
      continue
    end
    if fst
      A, a = power_reduce(k, v)
      @hassert :PID_Test 1 (v>0 ? fractional_ideal(O, k)^Int(v) : inv(k)^Int(-v)) == A*evaluate(a)
      fst = false
    else
      B, b = power_reduce(k, v)
      mul!(a, a, b)
      @hassert :PID_Test (v>0 ? fractional_ideal(O, k)^Int(v) : inv(k)^Int(-v)) == B*evaluate(b)
      if norm(A, copy = false)*norm(B, copy = false) > abs(discriminant(O))
        A, c = reduce_product(A, B)
        add_to_key!(a.fac, c, -1)
      else
        A = A*B
      end
    end
  end
  @hassert :PID_Test 1 A*evaluate(a) == evaluate(I)
  return A, a
end


# The bound should be sqrt(disc) (something from LLL)
@doc raw"""
    power_reduce(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, e::ZZRingElem) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FacElem{AbsSimpleNumFieldElem}

Computes $B$ and $\alpha$ in factored form, such that $\alpha B = A^e$
$B$ has small norm.
"""
function power_reduce(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, e::ZZRingElem)
  O = order(A)
  K= nf(O)
  if norm(A, copy = false) > abs(discriminant(O))
    A1, a = reduce_ideal(A)
    @hassert :PID_Test 1 a*A == A1
    A = A1
    al = FacElem(Dict(a=>-e))
  else
    al = FacElem(Dict(K(1) => ZZRingElem(1)))
  end

  #we have A_orig^e = (A*a)^e = A^e*a^e = A^e*al and A is now small

  if e < 0
    B = inv(A)
    A = numerator(B)
    add_to_key!(al.fac, K(denominator(B)), ZZRingElem(e))
    e = -e
  end

  if isone(e)
    return A, al
  end
  # A^e = A^(e/2)^2 A or A^(e/2)^2
  # al * A^old^(e/2) = A_new
  C, cl = power_reduce(A, div(e, 2))
  @hassert :PID_Test 1 C*evaluate(cl) == A^Int(div(e, 2))
  mul!(al, al, cl^2)
  if norm(C, copy = false)^2 > abs(discriminant(O))
    @vtime :CompactPresentation :4 C2, a = reduce_product(C, C)
    add_to_key!(al.fac, a, -1)
  else
    C2 = C^2
  end

  if isodd(e)
    if norm(A, copy = false)*norm(C2, copy = false) > abs(discriminant(O))
      @vtime :CompactPresentation :4 A1, a = reduce_product(C2, A)
      A = A1
      add_to_key!(al.fac, a, -1)
    else
      A = C2*A
    end
  else
    A = C2
  end
  return A, al
end


function new_power_reduce(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, e::ZZRingElem)
  O = order(A)
  if iszero(e)
    return ideal(O, 1)
  end
  K = nf(O)
  al = FacElem(Dict(K(1) => ZZRingElem(1)))
  if e < 0
    A1 = inv(A)
    A = A1.num
    add_to_key!(al.fac, K(A1.den), e)
    e = -e
  end

  if norm(A)^e <= abs(discriminant(O))
    return A^e, al
  end
  Ainvtot = inv(A)
  Ainv = Ainvtot.num
  d = Ainvtot.den
  res = _new_power_reduce(A, e, Ainv, d)
  mul!(al, al, res[2])
  return res[1], al
end

function _new_power_reduce(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, e::ZZRingElem, Ainv::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, d::ZZRingElem)
  #Ainv//d is the inverse of A
  #We want to reduce A^e
  O = order(A)
  K = nf(O)
  bdisc = abs(discriminant(O))
  if norm(A) > bdisc
    a = divexact(basis(Ainv)[1].elem_in_nf, d)
    A1 = a*A
    simplify(A1)
    A = A1.num
    al = FacElem(Dict(a=>-e))
    #I need to update Ainv!
    Ainvtot = inv(A)
    Ainv = Ainvtot.num
    d = Ainvtot.den
    newb = lll(Ainv)[2]
    mul!(newb, newb, basis_matrix(Ainv, copy = false))
    Ainv.basis_matrix = newb
  else
    al = FacElem(Dict(K(1) => ZZRingElem(1)))
  end


  if isone(e)
    return A, al, Ainv, d
  end

  # A^e = A^(e/2)^2 A or A^(e/2)^2
  # al * A^old^(e/2) = A_new
  C, cl, Cinv, dCinv = _new_power_reduce(A, div(e, 2), Ainv, d)
  @hassert :PID_Test 1 C*evaluate(cl) == A^Int(div(e, 2))
  mul!(al, al, cl^2)
  if norm(C)^2 > bdisc
    a = divexact(short_elem_product(Cinv, Cinv), dCinv^2)
    C21 = a*(C^2)
    simplify(C21)
    C2 = C21.num
    C2invtot = inv(C2)
    C2inv = C2invtot.num
    C2d = C2invtot.den
    newb = lll(C2inv)[2]
    mul!(newb, newb, basis_matrix(C2inv, copy = false))
    C2inv.basis_matrix = newb
    add_to_key!(al.fac, a, -1)
  else
    C2 = C^2
    basis_IJ = _lll_product_basis(Cinv, Cinv)
    IJ = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(O, basis_IJ)
    newb = lll(IJ)[2]
    mul!(newb, newb, basis_matrix(IJ, copy = false))
    IJ.basis_matrix = newb
    C2inv = IJ
    C2d = dCinv*dCinv
  end

  if isodd(e)
    if norm(A)*norm(C2) > bdisc
      a = divexact(short_elem_product(C2inv, Ainv), C2d*d)
      A1 = a*C2*A
      simplify(A1)
      A = A1.num
      add_to_key!(al.fac, a, -1)
      Ainvtot = inv(A)
      d = Ainvtot.den
      Ainv = Ainvtot.num
      bnew = lll(Ainv)[2]
      mul!(bnew, bnew, basis_matrix(Ainv, copy = false))
      Ainv.basis_matrix = bnew
    else
      A = C2*A
      basis_IJ = _lll_product_basis(C2inv, Ainv)
      IJ = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(O, basis_IJ)
      newb = lll(IJ)[2]
      mul!(newb, newb, basis_matrix(IJ, copy = false))
      IJ.basis_matrix = newb
      Ainv = IJ
      d = d*C2d
    end
  else
    A = C2
    d = C2d
    Ainv = C2inv
  end
  return A, al, Ainv, d
end

function short_elem_product(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, B::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return lll_basis_product(A, B)[1]
end


################################################################################
#
#  Short basis of product of ideals
#
################################################################################

# Claus and Tommy:
# We express the basis of IJ in terms of the basis of I (I contains IJ)
# Then we compute the lll of the matrix of the coordinates. This way we get a
# better basis to start the computation of LLL
#We compute the hnf to have a guaranteed bound on the entries
function _lll_product_basis(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, J::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  A = lll(I)[2]
  mul!(A, A, basis_matrix(I, copy = false))
  IJ = I*J
  C = basis_matrix(IJ, copy = false)
  @vtime :LLL 3 iA, de = pseudo_inv(A)
  mul!(iA, C, iA)
  divexact!(iA, iA, de)
  hnf_modular_eldiv!(iA, minimum(J))
  @vtime :LLL 3 lll!(iA, LLLContext(0.3, 0.51))
  @vtime :LLL 3 lll!(iA)
  mul!(iA, iA, A)
  return iA
end



function lll_basis_product(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, J::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})

  basis_IJ = _lll_product_basis(I, J)
  IJ = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(order(I), basis_IJ)
  res = lll_basis(IJ)
  return res
end
