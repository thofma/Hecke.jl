export overorders, isbass, isgorenstein

################################################################################
#
#  Defines minimal overorder
#
################################################################################
#H must be in lower left hnf form
function iszero_mod_hnf!(a::fmpz_mat, H::fmpz_mat)
  j = ncols(H)
  for i = min(nrows(H), ncols(H)):-1:1
    if iszero(a[i])
      continue
    end
    while j >= 1 && iszero(H[i, j])
      j -= 1 
    end
    if iszero(j) 
      return iszero(a)
    end
    q, r = divrem(a[1, j], H[i, j])
    if r != 0
      return false
    end
    a[1, j] = r
    for k=1:(j-1)
      a[1, k] = a[1, k] - q * H[i, k]
    end
  end
  return iszero(a)
end

function defines_minimal_overorder(B::Vector{nf_elem}, l::Vector{nf_elem})
  M = hnf(basis_mat(B))
  x = M.den * l[1]^2
  if denominator(x) != 1
    return false, M
  end
  m = zero_matrix(FlintZZ, 1, ncols(M))
  for i = 1:ncols(M)
    m[1, i] = numerator(coeff(x, i - 1))
  end
  fl = iszero_mod_hnf!(m, M.num)
  return fl, M  
end

################################################################################
#
#  Quotients of two orders
#
################################################################################

# For convenience, there is a quotient constructor for an extension of orders.
# The quotient will be represented as an abelian group.
mutable struct GrpAbFinGenToNfOrdQuoNfOrd <: Map{GrpAbFinGen, NfOrd, HeckeMap, GrpAbFinGenToNfOrdQuoNfOrd}
  domain::GrpAbFinGen
  codomain::NfOrd
  bottom::NfOrd
  offset::Int
  top_snf_basis::Vector{nf_elem}
  top_snf_basis_in_order::Vector{NfOrdElem}
  bottom_snf_basis::Vector{nf_elem}
  top_basis_mat_inv::FakeFmpqMat

  function GrpAbFinGenToNfOrdQuoNfOrd(M::NfOrd, O::NfOrd)
    z = new()
    d = degree(O)
    K = nf(O)
    B = zero_matrix(FlintZZ, d, d)
    for i in 1:d
      v = elem_in_basis(M(elem_in_nf(basis(O)[i])))
      for j in 1:d
        B[i, j] = v[j]
      end
    end
    S, U, V = snf_with_transform(B, true, true)
    Vinv = inv(V)
    basis_O = basis(O)
    basis_M = basis(M)
    new_basis_O = Vector{nf_elem}(undef, d)
    new_basis_M = Vector{nf_elem}(undef, d)
    for i in 1:d
      new_basis_O[i] = elem_in_nf(sum(U[i, j] * basis_O[j] for j in 1:d))
    end

    for i in 1:d
      new_basis_M[i] = elem_in_nf(sum(Vinv[i, j] * basis_M[j] for j in 1:d))
    end

    offset = 1
    while offset <= d && isone(S[offset, offset])
      offset += 1
    end

    offset -= 1

    # offset is the first index - 1, where the diagonal of S is not one.

    A = DiagonalGroup(fmpz[S[i, i] for i in (offset + 1):d])

    z.offset = offset
    z.domain = A
    z.codomain = M
    z.bottom = O
    z.top_snf_basis = new_basis_M
    z.bottom_snf_basis = new_basis_O
    z.top_basis_mat_inv = inv(basis_mat(new_basis_M))
    z.top_snf_basis_in_order = map(M, z.top_snf_basis)

    return z
  end
end

domain(f::GrpAbFinGenToNfOrdQuoNfOrd) = f.domain

codomain(f::GrpAbFinGenToNfOrdQuoNfOrd) = f.codomain

function image(f::GrpAbFinGenToNfOrdQuoNfOrd, x::GrpAbFinGenElem)
  t = zero(codomain(f))
  z = deepcopy(f.top_snf_basis_in_order[1 + f.offset])
  mul!(z, x.coeff[1], z)
  for i in 2:length(x.coeff)
    mul!(t, x.coeff[i], f.top_snf_basis_in_order[i + f.offset])
    add!(z, z, t)
  end
  return z
end

function preimage(f::GrpAbFinGenToNfOrdQuoNfOrd, x::NfOrdElem)
  v = elem_in_nf(x)
  t = f.codomain.tcontain
  elem_to_mat_row!(t.num, 1, t.den, v)
  t = mul!(t, t, f.top_basis_mat_inv)
  @assert isone(t.den)
  return domain(f)(sub(t, 1:1, (1 + f.offset):ncols(t)).num)
end

function quo(M::NfOrd, O::NfOrd)
  f = GrpAbFinGenToNfOrdQuoNfOrd(M, O)
  return domain(f), f
end

################################################################################
#
#  Inducing an endomorphism of the quotient
#
################################################################################

# Let f : A -> M/O be a quotient of orders and g: M -> M an endomorphism of
# O-modules (so g(x) is in O for all x in O).
# This functions computes an endomorphism h: A -> A such that
#
# A <- M/O
# |     |
# v     v
# A <- M/O
#
# commutes. The horizontal maps is the section of f.

function induce(f::GrpAbFinGenToNfOrdQuoNfOrd, g)
  G = domain(f)
  imgs = Vector{GrpAbFinGenElem}(undef, ngens(G))
  d = degree(codomain(f))
  m = zero_matrix(FlintZZ, d, d)
  for i in 1:ngens(G)
    imgs[i] = f\(g(f(G[i])))
  end
  return hom(G, G, imgs)
end

################################################################################
#
#  Minimal overorders
#
################################################################################

# Compute the minimal overorders of O in M by computing the orders generated
# by minimal O-submodules of M.
function _minimal_overorders_meataxe(O::NfOrd, M::NfOrd)

  orders = NfOrd[]
  A, mA = quo(M, O)
  if order(A) == 1
    return orders
  end
  B = mA.bottom_snf_basis
  @assert isone(B[1])
  autos = Vector{GrpAbFinGenMap}(undef, degree(O) - 1)
  # We skip the first basis element, since it acts trivially
  for i in 1:(degree(O) - 1)
    autos[i] = induce(mA, x -> M(elem_in_nf(B[i + 1]))*x)
  end

  d = degree(O)
  K = nf(O)

  potential_basis = Vector{nf_elem}(undef, d)

  

  subs = stable_subgroups(A, autos, minimal = true, op = (G, z) -> sub(G, z, false))

  for i in 1:mA.offset
    potential_basis[i] = mA.bottom_snf_basis[i]
  end

  offset = mA.offset

  for s in subs
    T = image(s[2], false)
    G = domain(T[2])
    for i in 1:(d - offset)
      v = T[2](G[i]).coeff
      if iszero(v)
        potential_basis[i + offset] = mA.bottom_snf_basis[i + offset]
      else
        @assert ncols(v) == d - offset
        potential_basis[i + offset] = sum(v[1, j] * mA.top_snf_basis[j + offset] for j in 1:(d - offset))
      end
    end
    #L = _Order(K, potential_basis)
    # A minimal overorder must be a minimal submodule
    fl, bL = defines_order(K, potential_basis)
    if !fl
      continue
    end
    bL = hnf(bL)
    #bL = basis_mat(L, Val{false})
    if any(x -> basis_mat(x, Val{false}) == bL, orders)
      continue
    else
      push!(orders, Order(K, bL, false, false))
    end
  end
  return orders
end

function _minimal_poverorders(O::NfOrd, P::NfOrdIdl, excess = Int[], use_powering::Bool = false)
  M = ring_of_multipliers(P)
  p = minimum(P)
  A, mA = quo(M, O)
  orders = NfOrd[]
  if order(A) == 1
    return orders
  end
  B = mA.bottom_snf_basis
  d = degree(O)
  K = nf(O)
  @assert isone(B[1])
  if use_powering
    autos = Vector{GrpAbFinGenMap}(undef, d)
    autos[d] = induce(mA, x -> x^p)
  else
    autos = Vector{GrpAbFinGenMap}(undef, d - 1)
  end
  # We skip the first basis element, since it acts trivially
  for i in 1:(d - 1)
    autos[i] = induce(mA, x -> M(elem_in_nf(B[i + 1]))*x)
  end

  d = degree(O)
  K = nf(O)

  potential_basis = Vector{nf_elem}(undef, d)
  orders = NfOrd[]

  subs = stable_subgroups(A, autos, minimal = true, op = (G, z) -> sub(G, z, false))

  for i in 1:mA.offset
    potential_basis[i] = mA.bottom_snf_basis[i]
  end

  offset = mA.offset

  for s in subs
    T = image(s[2], false)
    G = domain(T[2])
    new_element = 0
    for i in 1:(d - offset)
      v = T[2](G[i]).coeff
      if iszero(v)
        potential_basis[i + offset] = mA.bottom_snf_basis[i + offset]
      else
        @assert ncols(v) == d - offset
        potential_basis[i + offset] = sum(v[1, j] * mA.top_snf_basis[j + offset] for j in 1:(d - offset))
        new_element = i + offset
      end
    end
    @assert new_element != 0
    b, bL = defines_minimal_overorder(potential_basis, nf_elem[potential_basis[new_element]])
    if !b
      excess[] = excess[] + 1
      continue
    end
    L = Order(K, bL, false, false)
    push!(orders, L)
  end
  return orders
end

################################################################################
#
#  Primary overorders
#
################################################################################

function new_poverorders(O::NfOrd, p::fmpz)
  lP = prime_ideals_over(O, p)
  res = typeof(O)[O]
  for P in lP
    nres = typeof(O)[]
    Pprim = pprimary_overorders(O, P)
    for R in Pprim
      for S in res
        push!(nres, R + S)
      end
    end
    res = nres
  end
  return res
end

function new_overorders(O::NfOrd)
  orders = Vector{typeof(O)}[]
  M = maximal_order(O)
  for (p, ) in factor(div(index(M), index(O)))
    print("Time for $p: ")
    tp = @elapsed new_p = new_poverorders(O, p)
    push!(orders, new_p)
    println(tp)
    #@show p, length(orders[end])
  end

  if length(orders) == 0
    return typeof(O)[O]
  end

  res = Vector{typeof(O)}(undef, prod(length(orders[i]) for i in 1:length(orders)))

  if length(orders) == 1
    return orders[1]
  else
    I = Iterators.product(orders...)
    tsum = @elapsed for (j, i) in enumerate(I)
      res[j] = sum(i)
    end
    println("summing: $tsum")
    return res
  end
end

function pprimary_overorders(O::NfOrd, P::NfOrdIdl)
  to_enlarge = typeof(O)[O]
  current = Dict{fmpq, Dict{FakeFmpqMat, typeof(O)}}()
  excess = Int[0]
  while length(to_enlarge) > 0
    #@show length(to_enlarge)
    #if length(current) > 0
    #  @show sum(length(x) for x in values(current))
    #  @show collect(keys(current))
    #end

    N = popfirst!(to_enlarge)
    #lQ = [ Q for Q in prime_ideals_over(N, minimum(P)) if contract(Q, O) == P]
    lQ = prime_ideals_over(N, P)
    new = typeof(O)[]
    for Q in lQ
      #new = append!(new, _minimal_overorders_meataxe(N, ring_of_multipliers(Q)))
      #@show isbass(N, Q)
      new = append!(new, _minimal_poverorders(N, Q, excess))
    end
    for S in new
      #@show ishnf(basis_mat(S).num, :lowerleft)
      #t += @elapsed H = hnf(basis_mat(S, Val{false}))
      H = basis_mat(S, Val{false})
      ind = prod(H.num[i, i] for i in 1:degree(O))//(H.den)^degree(O)
      if haskey(current, ind)
        c = current[ind]
        if !haskey(c, H)
          c[H] = S
          push!(to_enlarge, S)
        end
      else
        c = Dict{FakeFmpqMat, typeof(O)}()
        current[ind] = c
        c[H] = S
        push!(to_enlarge, S)
      end
    end
  end
  push!(to_enlarge, O)
  for d in values(current)
    for e in values(d)
      push!(to_enlarge, e)
    end
  end
  println("excess: $(excess[])")
  return to_enlarge
end

function pprimary_overorders_old(O::NfOrd, P::NfOrdIdl)
  #if isbass(O, P)
  #  return pprimary_overorders_bass(O, P)
  #end

  if index(E) != index(O)
    minimaloverorders = _minimal_poverorders(O, P)#_minimal_overorders_meataxe(O, E)
  else
    return typeof(O)[O]
  end

  res = typeof(O)[O]

  for R in minimaloverorders
    primes = prime_ideals_over(R, P)

    if length(primes) == 1
      rres = pprimary_overorders(R, primes[1])
    else
      rres1 = pprimary_overorders(R, primes[1])
      rres2 = pprimary_overorders(R, primes[2])
      rres = typeof(rres1)()
      for R1 in rres1
        for R2 in rres2
          push!(rres, R1 + R2)
        end
      end
    end
    nres = typeof(res)()
    for C in res
      for T in rres
        push!(nres, C + T)
      end
    end
    append!(res, nres)
    res = unique(OO -> basis_mat(OO, Val{false}), res)
  end
  @show length(res)
  return res
end


function overorders_naive(O::NfOrd, M::NfOrd = maximal_order(nf(O)))
  d = degree(O)
  K = nf(O)
  B = zero_matrix(FlintZZ, d, d)
  for i in 1:d
    v = elem_in_basis(M(elem_in_nf(basis(O)[i])))
    for j in 1:d
      B[i, j] = v[j]
    end
  end
  S, U, V = snf_with_transform(B, true, true)
  Vinv = inv(V)
  basis_O = basis(O)
  basis_M = basis(M)
  new_basis_O = Vector{nf_elem}(undef, d)
  new_basis_M = Vector{nf_elem}(undef, d)
  for i in 1:d
    new_basis_O[i] = elem_in_nf(sum(U[i, j] * basis_O[j] for j in 1:d))
  end

  for i in 1:d
    new_basis_M[i] = elem_in_nf(sum(Vinv[i, j] * basis_M[j] for j in 1:d))
  end

  A = AbelianGroup(S)
  
  if order(A) == 1
    return typeof(O)[O]
  end

  # Don't put things in the subgroup lattice
  subs = subgroups(A, fun = (G, z) -> sub(G, z, false))
  potential_basis = Vector{nf_elem}(undef, d)
  oorders = typeof(O)[]
  println("#subgroups: $(length(collect(subs)))")
  for (i, s) in enumerate(subs)
    #@show i
    T = image(s[2], false)
    G = domain(T[2])
    for i in 1:d
      v = T[2](G[i]).coeff
      if iszero(v)
        potential_basis[i] = new_basis_O[i]
      else
        potential_basis[i] = sum(v[1, j] * new_basis_M[j] for j in 1:d)
      end
    end
    b, bmat = defines_order(K, potential_basis)
    if b 
      push!(oorders, Order(K, hnf(bmat)))
    end
  end
  return oorders
end

function poverorders_meataxe(O::NfOrd, p::Integer)
  return poverorders_meataxe(O, fmpz(p))
end

function minimal_poverorders_naive(O::NfOrd, p::fmpz)
  orders = poverorders_meataxe(O, p)
  res = Vector{typeof(O)}()
  for S in orders
    if length(overorders_meataxe(O, S)) == 2
      push!(res, S)
    end
  end
  return res
end

function poverorders_from_multipliers(O, p::fmpz)
  M = MaximalOrder(O)
  lP = prime_ideals_over(O, p)
  orders = typeof(O)[]
  for P in lP
    E = ring_of_multipliers(P)
    if index(E) != index(O)
      append!(orders, _overorders_meataxe(O, E))
    end
  end
  if length(orders) == 0
    push!(orders, O)
  end
  return orders
end

function poverorders(O, p::fmpz)
  to_enlarge = typeof(O)[O]
  current = Dict{fmpq, Dict{FakeFmpqMat, typeof(O)}}()
  while length(to_enlarge) > 0
    N = pop!(to_enlarge)
    new = poverorders_from_multipliers(N, p)
    for S in new
      H = hnf(basis_mat(S, Val{false}))
      ind = prod(H.num[i, i] for i in 1:degree(O))//H.den
      if haskey(current, ind)
        c = current[ind]
        if haskey(c, H)
          continue
        else
          c[H] = S
          push!(to_enlarge, S)
        end
      else
        c = Dict{FakeFmpqMat, typeof(O)}()
        current[ind] = c
        c[H] = S
        push!(to_enlarge, S)
      end
    end
  end
  for d in values(current)
    for e in values(d)
      push!(to_enlarge, e)
    end
  end
  return to_enlarge
end

function _overorders_meataxe(O::NfOrd, M::NfOrd)
  K = nf(O)
  d = degree(O)
  B = zero_matrix(FlintZZ, d, d)
  orders = Vector{typeof(O)}()
  for i in 1:d
    v = elem_in_basis(M(elem_in_nf(basis(O)[i])))
    for j in 1:d
      B[i, j] = v[j]
    end
  end
  S::fmpz_mat, U::fmpz_mat, V::fmpz_mat = snf_with_transform(B, true, true)
  Vinv = inv(V)
  basis_O = basis(O)
  basis_M = basis(M)
  new_basis_O = Vector{nf_elem}(undef, d)
  new_basis_M = Vector{nf_elem}(undef, d)
  for i in 1:d
    new_basis_O[i] = elem_in_nf(sum(U[i, j] * basis_O[j] for j in 1:d))
  end


  for i in 1:d
    new_basis_M[i] = elem_in_nf(sum(Vinv[i, j] * basis_M[j] for j in 1:d))
  end

  new_basis_mat_M_inv = inv(basis_mat(new_basis_M))

  autos = GrpAbFinGenMap[]

  A = DiagonalGroup(fmpz[ S[i, i] for i in 1:d])

  for i in 1:d
    b = new_basis_O[i]
    m = zero_matrix(FlintZZ, d, d)
    for j in 1:d
      v = elem_in_nf(M(b* new_basis_M[j]))
      t = O.tcontain
      elem_to_mat_row!(t.num, 1, t.den, v)
      t = mul!(t, t, new_basis_mat_M_inv)
      # I need the representation with respect to new_basis_M
      for k in 1:d
        m[j, k] = t.num[1, k]
      end
    end
    push!(autos, hom(A, A, m))
  end

  potential_basis = Vector{nf_elem}(undef, d)

  subs = stable_subgroups(A, autos, op = (G, z) -> sub(G, z, false))
  for s in subs
    T = image(s[2], false)
    G = domain(T[2])
    for i in 1:d
      v = T[2](G[i]).coeff
      if iszero(v)
        potential_basis[i] = new_basis_O[i]
      else
        potential_basis[i] = sum(v[1, j] * new_basis_M[j] for j in 1:d)
      end
    end
    b, bmat = defines_order(K, deepcopy(potential_basis))
    if b 
      push!(orders, Order(K, hnf(bmat)))
    end
  end
  return orders
end

function poverorders_meataxe(O::NfOrd, p::fmpz, N::NfOrd = pmaximal_overorder(O, p))
  K = nf(O)
  d = degree(O)
  M = intersect(N, pmaximal_overorder(O, p))
  A, mA = quo(M, O)
  orders = NfOrd[O]
  if order(A) == 1
    return orders
  end
  B = mA.bottom_snf_basis
  d = degree(O)
  K = nf(O)
  @assert isone(B[1])
  autos = Vector{GrpAbFinGenMap}(undef, d - 1)
  # We skip the first basis element, since it acts trivially
  for i in 1:(d - 1)
    autos[i] = induce(mA, x -> M(elem_in_nf(B[i + 1]))*x)
  end

  d = degree(O)
  K = nf(O)

  potential_basis = Vector{nf_elem}(undef, d)
  orders = NfOrd[]

  for i in 1:mA.offset
    potential_basis[i] = mA.bottom_snf_basis[i]
  end

  offset = mA.offset

  #B = zero_matrix(FlintZZ, d, d)
  #orders = Vector{typeof(O)}()
  #for i in 1:d
  #  v = elem_in_basis(M(elem_in_nf(basis(O)[i])))
  #  for j in 1:d
  #    B[i, j] = v[j]
  #  end
  #end
  #S::fmpz_mat, U::fmpz_mat, V::fmpz_mat = snf_with_transform(B, true, true)
  #Vinv = inv(V)
  #basis_O = basis(O)
  #basis_M = basis(M)
  #new_basis_O = Vector{nf_elem}(undef, d)
  #new_basis_M = Vector{nf_elem}(undef, d)
  #for i in 1:d
  #  new_basis_O[i] = elem_in_nf(sum(U[i, j] * basis_O[j] for j in 1:d))
  #end

  #for i in 1:d
  #  new_basis_M[i] = elem_in_nf(sum(Vinv[i, j] * basis_M[j] for j in 1:d))
  #end

  #new_basis_mat_M_inv = inv(basis_mat(new_basis_M))

  #autos = GrpAbFinGenMap[]

  #A = DiagonalGroup(fmpz[ S[i, i] for i in 1:d])

  #for i in 1:d
  #  b = new_basis_O[i]
  #  m = zero_matrix(FlintZZ, d, d)
  #  for j in 1:d
  #    v = elem_in_nf(M(b* new_basis_M[j]))
  #    t = O.tcontain
  #    elem_to_mat_row!(t.num, 1, t.den, v)
  #    t = mul!(t, t, new_basis_mat_M_inv)
  #    # I need the representation with respect to new_basis_M
  #    for k in 1:d
  #      m[j, k] = t.num[1, k]
  #    end
  #  end
  #  push!(autos, hom(A, A, m))
  #end
  #  
  #potential_basis = Vector{nf_elem}(undef, d)

  excess = 0

  subs = stable_subgroups(A, autos, op = (G, z) -> sub(G, z, false))

  for s in subs
    T = image(s[2], false)
    G = domain(T[2])
    new_element = 0
    for i in 1:(d - offset)
      v = T[2](G[i]).coeff
      if iszero(v)
        potential_basis[i + offset] = mA.bottom_snf_basis[i + offset]
      else
        @assert ncols(v) == d - offset
        potential_basis[i + offset] = sum(v[1, j] * mA.top_snf_basis[j + offset] for j in 1:(d - offset))
        new_element = i + offset
      end
    end
    b, bmat = defines_order(K, deepcopy(potential_basis))
    if b 
      push!(orders, Order(K, bmat))
    else
      excess += 1
    end
  end
  @show excess, length(orders)
  return orders
end

function overorders_meataxe(O::NfOrd, M::NfOrd = maximal_order(O))
  orders = Vector{typeof(O)}[]

  k = 1

  for (p, ) in factor(div(index(M), index(O)))
    push!(orders, poverorders_meataxe(O, p, M))
  end

  if length(orders) == 0
    return typeof(O)[O]
  end

  res = Vector{typeof(O)}(undef, prod(length(orders[i]) for i in 1:length(orders)))

  if length(orders) == 1
    return orders[1]
  else
    I = Iterators.product(orders...)
    for (j, i) in enumerate(I)
      res[j] = sum(i)
    end
    return res
  end
end

@doc Markdown.doc"""
    overorders(O::NfOrd)

Returns all overorders of $\mathcal O$.
"""
function overorders(O::NfOrd)
  return overorders_meataxe(O)
end

function new_pprimary_overorder_bass(O::NfOrd, P::NfOrdIdl)
  res = NfOrd[O]
  O1 = ring_of_multipliers(P)
  if index(O1) == index(O)
    return res
  end
  push!(res, O1)
  primes = prime_ideals_over(O1, P)
  while length(primes) == 1
    O2 = ring_of_multipliers(primes[1])
    if index(O2) == index(O1)
      return res
    end
    push!(res, O2)
    O1 = O2
    primes = prime_ideals_over(O1, primes[1])
  end
  
  #There was branching.
  res1 = NfOrd[]
  O3 = O1
  O2 = ring_of_multipliers(O1, primes[1])
  while index(O3) != index(O2)
    push!(res1, O2)
    O3 = O2
    P = prime_ideals_over(O2, primes[1])[1]
    O2 = ring_of_multipliers(P) 
  end
  
  res2 = NfOrd[]
  O3 = O1
  O2 = ring_of_multipliers(O1, primes[2])
  while index(O3) != index(O2)
    push!(res2, O2)
    O3 = O2
    P = prime_ideals_over(O2, primes[2])[1]
    O2 = ring_of_multipliers(P) 
  end
  append!(res, res1)
  append!(res, res2)
  for N in res1
    for M in res2
      push!(res, N + M)
    end
  end
  return res
  
end


function pprimary_overorders_bass(O::NfOrd, P::NfOrdIdl; branching::Bool = true)
  res = NfOrd[]
  R = ring_of_multipliers(P)
  if index(R) == index(O)
    return typeof(O)[O]
  end
  lQ = prime_ideals_over(R, P)
  if !branching
    res = typeof(O)[O]
    for Q in lQ
      if intersect(Q, O) == P
        return append!(res, pprimary_overorders_bass(R, Q, branching = false))
      end
    end
  end

  res = typeof(O)[O]

  primes = NfOrdIdl[]

  k = 0
  for Q in lQ
    if k == 2 
      break
    end
    if intersect(Q, O) == P
      push!(primes, Q)
      k = k + 1
    end
  end

  if k == 1
    append!(res, pprimary_overorders_bass(R, primes[1], branching = false))
    return res
  else
    @assert k == 2
    S1 = pprimary_overorders_bass(R, primes[1], branching = false)
    S2 = pprimary_overorders_bass(R, primes[2], branching = false)
    for T1 in S1
      for T2 in S2
        push!(res, T1 + T2)
      end
    end
    return res
  end
end

function isbass(O::NfOrd, P::NfOrdIdl)
  M = maximal_order(O)
  Q = extend(P, M)
  p = minimum(P)
  resfield_dim = valuation(norm(P), p)
  ext_dim = valuation(norm(Q), p)
  @assert mod(ext_dim, resfield_dim) == 0
  return div(ext_dim, resfield_dim) <= 2
end

function isbass(O::NfOrd, p::fmpz)
  M = maximal_order(O)
  p_critical_primes = Set{ideal_type(O)}()
  lp = prime_decomposition(M, p)
  for (P, e) in lp
    push!(p_critical_primes, contract(P, O))
  end
  for Q in p_critical_primes
    resfield_dim = valuation(norm(Q), p)
    ext_dim = valuation(norm(Q * M), p)
    @assert mod(ext_dim, resfield_dim) == 0
    if div(ext_dim, resfield_dim) > 2
      return false
    end
  end
  return true
end

function isbass(O::NfOrd)
  f = minimum(conductor(O))
  M = maximal_order(nf(O))
  for (p, ) in factor(f)
    if !isbass(O, p)
      return false
    end
  end
  return true
end

function isgorenstein(O)
  codiff = codifferent(O)
  R = simplify(simplify(colon(1*O, codiff.num) * codiff) * codiff.den)
  return isone(norm(R))
end

function isgorenstein(O::NfOrd, p::Int)
  return isgorenstein(O, fmpz(p))
end

function isgorenstein(O::NfOrd, p::fmpz)
  codiff = codifferent(O)
  R = simplify(simplify(colon(1*O, codiff.num) * codiff) * codiff.den)
  v = valuation(norm(R), p)
  return v == 0
end

# This is very slow!
function intersect(x::NfOrd, y::NfOrd)
  d = degree(x)
  g = lcm(denominator(basis_mat(x)), denominator(basis_mat(y)))
  H = vcat(divexact(g * basis_mat(x).num, basis_mat(x).den), divexact(g * basis_mat(y).num, basis_mat(y).den))
  K = _kernel(H)
  return Order(nf(x), FakeFmpqMat(_hnf(sub(K, 1:d, 1:d)*divexact(g * basis_mat(x).num, basis_mat(x).den), :lowerleft), g))
end

################################################################################
#
#  Goursat
#
################################################################################

function ideals_with_norm(O::NfOrd, p::fmpz, n::Int)
  pn = p^n
  pInt = Int(p)
  K = nf(O)
  d = degree(O)
  ideals = []
  B = basis(O)

  autos = GrpAbFinGenMap[]

  A = DiagonalGroup(fmpz[pn for i in 1:d])

  for i in 1:d
    m = representation_matrix(B[i])
    push!(autos, hom(A, A, m))
  end

  potential_basis = Vector{elem_type(O)}(d)
  ideals = Vector{Tuple{Vector{Int}, ideal_type(O)}}()

  for par in AllParts(n)
    ppar = Vector(par)

    subs = stable_subgroups(A, autos, quotype=[pInt^y for y in ppar], op = (G, z) -> sub(G, z, false))

    for s in subs
      new_basis_mat = zero_matrix(FlintZZ, d, d)
      T = image(s[2], false)
      G = domain(T[2])
      for i in 1:d
        v = T[2](G[i]).coeff
        if iszero(v)
          new_basis_mat[i, i] = pn
        else
          for j in 1:d
            new_basis_mat[i, j] = v[1, j]
          end
        end
      end
      push!(ideals, ([pInt^y for y in ppar], ideal(O, new_basis_mat)))
    end
  end
  return ideals
end

function index(R::NfOrd, S::NfOrd)
  r = gen_index(R)
  s = gen_index(S)
  i = r^-1 * s
  @assert isinteger(i)
  return FlintZZ(i)
end

function poverorders_goursat(O1::NfOrd, O2::NfOrd, p::fmpz)
  l1 = poverorders(O1, p)
  l2 = poverorders(O2, p)
  data_from_l2 = Dict{Vector{Int}, Vector{Tuple{typeof(O1), ideal_type(O1)}}}()
  d = degree(O2)
  for O in l2
    i = index(O2, O)
    e, _ = ispower(i)
    for k in 1:e
      ideals = ideals_with_norm(O, p, k)
      for (typ, I) in ideals
        if haskey(data_from_l2, typ)
          push!(data_from_l2[typ], (O, I))
        else
          data_from_l2[typ] = [(O, I)]
        end
      end
    end
  end

  return data_from_l2
end

function abelian_group(Q::NfOrdQuoRing)
  A = AbelianGroup(Q.basis_mat)
  S, mS = snf(A)
  B = basis(Q.base_ring, Val{false})
  f = a -> begin aa = mS(a); Q(sum(aa.coeff[i] * B[i] for i in 1:degree(Q.base_ring))) end
  g = b -> mS\A(elem_in_basis(b.elem))
  return S, f, g
end

function isisomorphic(Q1::NfOrdQuoRing, Q2::NfOrdQuoRing)
  Q1_A, Q1_mA, Q1_mA_inv = abelian_group(Q1)
  Q2_A, Q2_mA, Q2_mA_inv = abelian_group(Q2)

  if Q1_A.snf != Q2_A.snf
    return false
  end

  Q1_U, Q1_mU = multiplicative_group(Q1)
  Q2_U, Q2_mU = multiplicative_group(Q2)

  if Q1_U.snf != Q2_U.snf
    return false
  end

  Q1_gens = [ Q1_mA(g) for g in gens(Q1_A) ]

  orders = [ order(g) for g in gens(Q1_A) ]

  l = length(Q1_A.snf)

  elements_with_correct_order = Dict{fmpz, Vector{GrpAbFinGenElem}}()

  for g in Q2_A
    o = order(g)
    if o in orders
      #elem_g = Q2_mA(g)
      if !haskey(elements_with_correct_order, o)
        elements_with_correct_order[o] = GrpAbFinGenElem[g]
      else
        push!(elements_with_correct_order[o], g)
      end
    end
  end

  isos = []

  genQ1A = gens(Q1_A)

  O1 = base_ring(Q1)
  O2 = base_ring(Q2)

  basis_O1 = basis(O1)

  for poss in Iterators.product([ elements_with_correct_order[o] for o in orders]...)
    #@show poss
    h = hom(Q1_A, collect(poss))
    if !isbijective(h)
      continue
    end
    if h(Q1_mA_inv(one(Q1))) != Q2_mA_inv(one(Q2))
      continue
    end
    multiplicative = true
    for i in 1:l
      for j in i:l
        @assert h(genQ1A[i]) == poss[i]
        @assert h(genQ1A[j]) == poss[j]
        if h(Q1_mA_inv(Q1_mA(genQ1A[i]) * Q1_mA(genQ1A[j]))) != Q2_mA_inv(Q2_mA(poss[i]) * Q2_mA(poss[j]))
          multiplicative = false
          break
        end
      end
      if !multiplicative
        break
      end
    end
    if multiplicative
      M = Array{fmpz}(degree(O1), degree(O2))
      for i in 1:degree(O1)
        v = elem_in_basis(Q2_mA(h(Q1_mA_inv(Q1(basis_O1[i])))).elem)
        for j in 1:degree(O2)
          M[i, j] = v[j]
        end
      end
      push!(isos, M)
    end
  end
  return isos
end

