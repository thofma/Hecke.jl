################################################################################
#
#  Defines minimal overorder
#
################################################################################

#H must be in lower left hnf form
function is_zero_mod_hnf!(a::ZZMatrix, H::ZZMatrix)
  reduce_mod_hnf_ll!(a, H)
  return iszero(a)
end

function defines_minimal_overorder(B::Vector, l::Vector)
  M = basis_matrix(B, FakeFmpqMat)
  _hnf!_integral(M)
  x = M.den * l[1]^2
  if denominator(x) != 1
    return false, M
  end
  m = zero_matrix(ZZ, 1, ncols(M))
  for i = 1:ncols(M)
    m[1, i] = numerator(x.coeffs[i])
  end
  fl = is_zero_mod_hnf!(m, M.num)
  return fl, M
end

function defines_minimal_overorder(B::Vector{AbsSimpleNumFieldElem}, l::Vector{AbsSimpleNumFieldElem})
  M = basis_matrix(B, FakeFmpqMat)
  _hnf!_integral(M)
  x = M.den * l[1]^2
  if denominator(x) != 1
    return false, M
  end
  m = zero_matrix(ZZ, 1, ncols(M))
  for i = 1:ncols(M)
    m[1, i] = numerator(coeff(x, i - 1))
  end
  fl = is_zero_mod_hnf!(m, M.num)
  return fl, M
end

################################################################################
#
#  Quotients of two orders
#
################################################################################

# For convenience, there is a quotient constructor for an extension of orders.
# The quotient will be represented as an abelian group.
mutable struct GrpAbFinGenToNfOrdQuoNfOrd{T1, T2, S, U} <: Map{FinGenAbGroup, T2, HeckeMap, HeckeMap}
              #Map{FinGenAbGroup, T2, HeckeMap, GrpAbFinGenToNfOrdQuoNfOrd{T1, T2, S, U}}
  domain::FinGenAbGroup
  codomain::T1
  bottom::T2
  offset::Int
  top_snf_basis::Vector{S}
  top_snf_basis_in_order::Vector{U}
  bottom_snf_basis::Vector{S}
  top_basis_mat_inv::FakeFmpqMat

  function GrpAbFinGenToNfOrdQuoNfOrd(M::T1, N::T2) where { T1 <: Union{ AbsNumFieldOrder, AlgAssAbsOrd }, T2 <: Union{ AbsNumFieldOrder, AlgAssAbsOrd, AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl } }
    TT = elem_type(_algebra(M))
    z = new{T1, T2, TT, elem_type(T1)}()
    d = degree(M)
    K = _algebra(M)
    B = zero_matrix(ZZ, d, d)
    for i in 1:d
      v = coordinates(M(_elem_in_algebra(basis(N)[i])), copy = false)
      for j in 1:d
        B[i, j] = v[j]
      end
    end
    S, U, V = snf_with_transform(B, true, true)
    Vinv = inv(V)
    new_basis_N = Vector{TT}(undef, d)
    new_basis_M = Vector{TT}(undef, d)

    for i in 1:d
      new_basis_N[i] = _elem_in_algebra(sum(U[i, j] * basis(N, copy = false)[j] for j in 1:d))
    end

    for i in 1:d
      new_basis_M[i] = _elem_in_algebra(sum(Vinv[i, j] * basis(M, copy = false)[j] for j in 1:d))
    end

    offset = 1
    while offset <= d && isone(S[offset, offset])
      offset += 1
    end

    offset -= 1

    # offset is the first index - 1, where the diagonal of S is not one.

    A = abelian_group(ZZRingElem[S[i, i] for i in (offset + 1):d])

    z.offset = offset
    z.domain = A
    z.codomain = M
    z.bottom = N
    z.top_snf_basis = new_basis_M
    z.bottom_snf_basis = new_basis_N
    z.top_basis_mat_inv = inv(basis_matrix(new_basis_M, FakeFmpqMat))
    z.top_snf_basis_in_order = map(M, z.top_snf_basis)

    return z
  end
end

domain(f::GrpAbFinGenToNfOrdQuoNfOrd) = f.domain

codomain(f::GrpAbFinGenToNfOrdQuoNfOrd) = f.codomain

function show(io::IO, f::GrpAbFinGenToNfOrdQuoNfOrd)
  print(io, "Section from ")
  print(io, domain(f))
  print(io, "\n")
  print(io, "to\n")
  print(io, codomain(f))
  print(io, "\n(kernel with basis: ", basis(f.bottom), ")")
end

function image(f::GrpAbFinGenToNfOrdQuoNfOrd{S1, S2, T, U}, x::FinGenAbGroupElem) where {S1, S2, T, U}
  t = zero(codomain(f))
  z = deepcopy(f.top_snf_basis_in_order[1 + f.offset])
  mul!(z, x.coeff[1], z)
  for i in 2:length(x.coeff)
    mul!(t, x.coeff[i], f.top_snf_basis_in_order[i + f.offset])
    add!(z, z, t)
  end
  return z
end

function preimage(f::GrpAbFinGenToNfOrdQuoNfOrd{S1, S2, T, U}, x) where {S1, S2, T, U}
  v = _elem_in_algebra(x)
  t = FakeFmpqMat(f.codomain.tcontain)
  elem_to_mat_row!(t.num, 1, t.den, v)
  t = mul!(t, t, f.top_basis_mat_inv)
  @assert isone(t.den)
  return domain(f)(sub(t, 1:1, (1 + f.offset):ncols(t)).num)
end

function preimage(f::GrpAbFinGenToNfOrdQuoNfOrd{<: AbsSimpleNumFieldOrder, S2, T, U}, x) where {S2, T, U}
  v = _elem_in_algebra(x)
  t = f.codomain.tcontain
  elem_to_mat_row!(t.num, 1, t.den, v)
  t = mul!(t, t, f.top_basis_mat_inv)
  @assert isone(t.den)
  return domain(f)(sub(t, 1:1, (1 + f.offset):ncols(t)).num)
end

function quo(M::AbsSimpleNumFieldOrder, O::AbsSimpleNumFieldOrder)
  f = GrpAbFinGenToNfOrdQuoNfOrd(M, O)
  return domain(f), f
end

function quo(M::AlgAssAbsOrd, O::AlgAssAbsOrd)
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
  imgs = Vector{FinGenAbGroupElem}(undef, ngens(G))
  d = degree(codomain(f))
  m = zero_matrix(ZZ, d, d)
  for i in 1:ngens(G)
    imgs[i] = f\(g(f(G[i])))
  end
  return hom(G, G, imgs)
end

################################################################################
#
#  High level functions
#
################################################################################

poverorders(O, p::Int) = poverorders(O, ZZRingElem(p))

@doc raw"""
    poverorders(O, p) -> Vector{Ord}

Returns all `p`-overorders of `O`, that is all overorders `M`, such that the
index of `O` in `M` is a `p`-power.
"""
function poverorders(O, p::ZZRingElem)
  if is_commutative(O)
    return poverorders_etale(O, p)
  end
  return poverorders_recursive_generic(O, p)
end

@doc raw"""
    overorders(O::AbsSimpleNumFieldOrder, type = :all) -> Vector{Ord}

Returns all overorders of `O`. If `type` is `:bass` or `:gorenstein`, then
only Bass and Gorenstein orders respectively are returned.
"""
function overorders(O; type = :all)
  if type == :all
    if is_commutative(O)
      return overorders_etale(O)
    else
      return overorders_by_prime_splitting_generic(O)
    end
  elseif type == :bass
    if is_commutative(O)
      return _overorders_with_local_property(O, is_bass)
    else
      error("Type :bass not supported for non-commutative orders")
    end
  elseif type == :gorenstein
    if is_commutative(O)
      return _overorders_with_local_property(O, is_gorenstein)
    else
      error("Type :gorenstein not supported for non-commutative orders")
    end
  else
    error("Type $type not supported")
  end
end

################################################################################
#
#  Minimal overorders
#
################################################################################

# Compute the minimal overorders of O in M by computing the orders generated
# by minimal O-submodules of M.
function _minimal_overorders_nonrecursive_meataxe(O, M)

  orders = typeof(O)[]
  A, mA = quo(M, O)

  if order(A) == 1
    return orders
  end

  B = mA.bottom_snf_basis

  autos = FinGenAbGroupHom[]

  for i in 1:degree(O)
    if isone(B[i])
      continue
    else
      push!(autos, induce(mA, x -> M(B[i] * _elem_in_algebra(x))))
      if !is_commutative(M)
        push!(autos, induce(mA, x -> M(_elem_in_algebra(x) * B[i])))
      end
    end
  end

  d = degree(O)
  K = _algebra(O)

  filter!(x -> !iszero(x.map), autos)

  potential_basis = Vector{elem_type(K)}(undef, d)
  subs = stable_subgroups(A, autos, minimal = true, op = (G, z) -> sub(G, z, false))

  for i in 1:mA.offset
    potential_basis[i] = mA.bottom_snf_basis[i]
  end

  offset = mA.offset

  #subs = stable_subgroups(A, autos, minimal = true, op = (G, z) -> sub(G, z, false))

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
    bL = _hnf!_integral(bL)
    #bL = basis_matrix(L, copy = false)
    if any(x -> basis_matrix(FakeFmpqMat, x, copy = false) == bL, orders)
      continue
    else
      push!(orders, order(K, bL, check = false, cached = false))
    end
  end
  return orders
end

# Compute all minimal poverorders contained in the ring of multipliers (P : P)
function _minimal_poverorders_in_ring_of_multipliers(O, P, excess = Int[0], use_powering::Bool = false)
  M = ring_of_multipliers(P)
  p = minimum(P)
  f = valuation(norm(P), p)
  if p == 2
    return _minimal_poverorders_at_2(O, P, excess)
  end
  A, mA = quo(M, O)
  orders = typeof(O)[]
  if order(A) == 1
    return orders
  end
  if order(A) == p^f
    O1 = order(_algebra(O), _hnf_integral(basis_matrix(FakeFmpqMat, M)), check = false, cached = false)
    @hassert :AbsNumFieldOrder is_hnf(basis_matrix(FakeFmpqMat, O1).num, :lowerleft)
    push!(orders, O1)
    return orders
  end
  B = mA.bottom_snf_basis
  d = degree(O)
  K = _algebra(O)
  #@assert isone(B[1])

  autos = FinGenAbGroupHom[]

  for i in 1:degree(O)
    if isone(B[i])
      continue
    else
      push!(autos, induce(mA, x -> M(B[i] * _elem_in_algebra(x))))
      if !is_commutative(M)
        push!(autos, induce(mA, x -> M(_elem_in_algebra(x) * B[i])))
      end
    end
  end

  if use_powering
    push!(autos, induce(mA, x -> x^p))
  end

  filter!( x -> !iszero(x.map), autos)

  potential_basis = Vector{elem_type(K)}(undef, d)


  if iszero(length(autos))
    subs = subgroups(A, subtype = [Int(p) for i = 1:f], fun = (G, z) -> sub(G, z, false))
  else
    subs = stable_subgroups(A, autos, minimal = true, op = (G, z) -> sub(G, z, false))
  end

  for i in 1:mA.offset
    potential_basis[i] = mA.bottom_snf_basis[i]
  end

  offset = mA.offset

  #The degree of the extension divides the degree of a prime of M lying over P
  lQ = prime_ideals_over(M, P)
  rel_fs = ZZRingElem[divexact(valuation(norm(Q), p), f) for Q in lQ]
  fac = factor(lcm(rel_fs))
  for (q, _) in fac
    if q == 2
      continue
    else
      subs1 = subgroups(A, subtype = [Int(p) for j in 1:Int(f*(Int(q) - 1))], fun = (G, z) -> sub(G, z, false))
      for s in subs1
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
        b, bL = defines_order(K, potential_basis)
        if !b
          excess[] = excess[] + 1
          continue
        end
        L = order(K, _hnf!_integral(bL, :lowerleft), check = false, cached = false)
        @hassert :AbsNumFieldOrder is_hnf(basis_matrix(FakeFmpqMat, L).num, :lowerleft)
        lQL = prime_ideals_over(L, P)
        if length(lQL) == 1 && norm(lQL[1]) == norm(P)^q
          push!(orders, L)
        end
      end
    end
  end

  if !(2 in fac) && length(lQ) == 1 && norm(P)^rel_fs[1] == order(A)
    return orders
  end

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
    b, bL = defines_minimal_overorder(potential_basis, elem_type(K)[potential_basis[new_element]])
    if !b
      excess[] = excess[] + 1
      continue
    end
    L = order(K, _hnf!_integral(bL, :lowerleft), check = false, cached = false)
    @hassert :AbsNumFieldOrder is_hnf(basis_matrix(FakeFmpqMat, L).num, :lowerleft)
    push!(orders, L)
  end


  return orders
end

# Compute minimal 2 overorders of O in (P : P) where 2 = min(P)
function _minimal_poverorders_at_2(O, P, excess = Int[])
  M = ring_of_multipliers(P)
  A, mA = quo(M, O)
  orders = typeof(O)[]
  if order(A) == 1
    return orders
  end
  B = mA.bottom_snf_basis
  d = degree(O)
  K = _algebra(O)
  if norm(P) == order(A)
    O1 = order(K, _hnf_integral(basis_matrix(FakeFmpqMat, M, copy = false)), check = false, cached = false)
    @hassert :AbsNumFieldOrder is_hnf(basis_matrix(FakeFmpqMat, O1).num, :lowerleft)
    push!(orders, O1)
    return orders
  end

  f = valuation(norm(P), 2)

  autos = FinGenAbGroupHom[]

  for i in 1:degree(O)
    if isone(B[i])
      continue
    else
      push!(autos, induce(mA, x -> M(B[i] * _elem_in_algebra(x))))
      if !is_commutative(M)
        push!(autos, induce(mA, x -> M(_elem_in_algebra(x) * B[i])))
      end
    end
  end

  push!(autos, induce(mA, x -> x^2))

  filter!(x -> !iszero(x.map), autos)

  potential_basis = Vector{elem_type(K)}(undef, d)

  offset = mA.offset
  for i in 1:offset
    potential_basis[i] = mA.bottom_snf_basis[i]
  end

  if iszero(length(autos))
    subs = subgroups(A, subtype = [2 for i = 1:f], fun = (G, z) -> sub(G, z, false))
  else
    R = Native.GF(2)
    V = Amodule(fpMatrix[map_entries(R, l.map) for l in autos])
    subm = minimal_submodules(V, f)
    subs = (sub(A, lift(x), false) for x in subm)
  end

  lQ = prime_ideals_over(M, P)
  rel_fs = ZZRingElem[divexact(valuation(norm(Q), 2), f) for Q in lQ]
  fac = factor(lcm(rel_fs))
  for (q, _) in fac
    if q == 2
      continue
    else
      if iszero(length(autos))
        subs1 = subgroups(A, subtype = [2 for i = 1:Int(f)*(Int(q) - 1)], fun = (G, z) -> sub(G, z, false))
      else
        R = Native.GF(2)
        V = Amodule(fpMatrix[map_entries(R, l.map) for l in autos])
        subm1 = submodules(V, dim(V)-Int(f)*(Int(q) - 1))
        subs1 = (sub(A, lift(x), false) for x in subm1)
      end
      for s in subs1
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
        b, bL = defines_order(K, potential_basis)
        if !b
          excess[] = excess[] + 1
          continue
        end
        _hnf!_integral(bL, :lowerleft)
        bL = 
        L = order(K, bL, check = false, cached = false)
        @hassert :AbsNumFieldOrder is_hnf(basis_matrix(FakeFmpqMat, L).num, :lowerleft)
        lQL = prime_ideals_over(L, P)
        if length(lQL) == 1 && norm(lQL[1]) == norm(P)^q
          push!(orders, L)
        end
      end
    end
  end

  if !(2 in fac) && length(lQ) == 1 && norm(P)^rel_fs[1] == order(A)
    return orders
  end

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
    bL = _hnf!_integral(basis_matrix(potential_basis, FakeFmpqMat))
    L = order(K, bL, check = false, cached = false)
    @hassert :AbsNumFieldOrder is_hnf(basis_matrix(FakeFmpqMat, L).num, :lowerleft)
    push!(orders, L)
  end


  return orders
end

################################################################################
#
#  Primary overorders of etale algebras
#
################################################################################

function poverorders_etale(O, p::ZZRingElem)
  lP = prime_ideals_over(O, p)
  res = typeof(O)[O]
  K = _algebra(O)
  tz = zero_matrix(ZZ, 2 * degree(O), degree(O))
  for P in lP
    nres = typeof(O)[]
    Pprim = pprimary_overorders(O, P)
    for R in Pprim
      for S in res
        push!(nres, sum_as_Z_modules(R, S, tz))
      end
    end
    res = nres
  end
  return res
end

################################################################################
#
#  Computation of overorders with local properties
#
################################################################################

function _overorders_with_local_property(O, pred)
  orders = typeof(O)[]
  M = maximal_order(O)
  n, f = is_perfect_power_with_data(divexact(discriminant(O), discriminant(M)))
  @assert n % 2 == 0
  for (p, ) in factor(f)
    lp = prime_ideals_over(O, p)
    for P in lp
      Pprim = pprimary_overorders(O, P)
      bassP = Vector{typeof(O)}()
      for A in Pprim
        add = true
        pabove = prime_ideals_over(A, P)
        for Q in pabove
          if !pred(A, Q)
            add = false
            break
          end
        end
        if add
          push!(bassP, A)
        end
      end
      if isempty(orders)
        append!(orders, bassP)
      else
        orders1 = Vector{typeof(O)}(undef, length(orders) * length(bassP))
        z = zero_matrix(ZZ, 2*degree(O), degree(O))
        kk = 1
        for O1 in orders
          for O2 in bassP
            orders1[kk] = sum_as_Z_modules(O1, O2, z)
            kk += 1
          end
        end
        orders = orders1
      end
    end
  end

  if length(orders) == 0
    return typeof(O)[O]
  end
  return orders
end

################################################################################
#
#  Overorders for étale algebras
#
################################################################################

function overorders_etale(O)
  orders = typeof(O)[]
  M = maximal_order(O)
  n, f = is_perfect_power_with_data(divexact(discriminant(O), discriminant(M)))
  @assert n % 2 == 0
  for (p, ) in factor(f)
    new_p = poverorders_etale(O, p)
    if isempty(orders)
      append!(orders, new_p)
    else
      orders1 = Vector{typeof(O)}(undef, length(orders) * length(new_p))
      sizehint!(orders1, length(orders) * length(new_p))
      z = zero_matrix(ZZ, 2*degree(O), degree(O))
      kk = 1
      for O1 in orders
        for O2 in new_p
          orders1[kk] = sum_as_Z_modules(O1, O2, z)
          kk += 1
        end
      end
      orders = orders1
    end
  end

  if length(orders) == 0
    return typeof(O)[O]
  end
  return orders
end

function pprimary_overorders(O, P)
  to_enlarge = typeof(O)[O]
  current = Dict{QQFieldElem, Dict{FakeFmpqMat, typeof(O)}}()
  excess = Int[0]
  while length(to_enlarge) > 0
    N = popfirst!(to_enlarge)
    lQ = prime_ideals_over(N, P)
    for Q in lQ
      if length(lQ) == 1 && is_bass(N, Q)
        new = pprimary_overorders_bass(N, Q)
        for S in new
          H = basis_matrix(FakeFmpqMat, S, copy = false)
          @hassert :AbsNumFieldOrder is_hnf(H.num, :lowerleft)
          ind = prod(H.num[i, i] for i in 1:degree(O))//(H.den)^degree(O)
          if haskey(current, ind)
            c = current[ind]
            if !haskey(c, H)
              c[H] = S
            end
          else
            c = Dict{FakeFmpqMat, typeof(O)}()
            current[ind] = c
            c[H] = S
          end
        end
      else
        new = _minimal_poverorders_in_ring_of_multipliers(N, Q, excess)
        for S in new
          H = basis_matrix(FakeFmpqMat, S, copy = false)
          @hassert :AbsNumFieldOrder is_hnf(H.num, :lowerleft)
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
    end
  end

  push!(to_enlarge, O)

  for d in values(current)
    for e in values(d)
      push!(to_enlarge, e)
    end
  end

  return to_enlarge
end

################################################################################
#
#  Generic implementation
#
################################################################################

function poverorders_one_step_generic(O, p::ZZRingElem)
  K = _algebra(O)
  d = degree(O)
  B = basis(O)
  M = order(K, [inv(K(p)) * _elem_in_algebra(b) for b in B ], check = false, isbasis = true)
  A, mA = quo(M, O)
  orders = typeof(O)[O]
  if order(A) == 1
    return orders
  end

  B = mA.bottom_snf_basis

  autos = FinGenAbGroupHom[]

  for i in 1:d
    if isone(B[i])
      continue
    end

    push!(autos, induce(mA, x -> M(B[i]*_elem_in_algebra(x))))

    if !is_commutative(M)
      push!(autos, induce(mA, x -> M((_elem_in_algebra(x) * B[i]))))
    end
  end

  potential_basis = Vector{elem_type(K)}(undef, d)
  orders = typeof(O)[]

  for i in 1:mA.offset
    potential_basis[i] = mA.bottom_snf_basis[i]
  end

  offset = mA.offset

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
    bmat = _hnf!_integral(bmat)
    if b
      push!(orders, order(K, bmat))
    else
      excess += 1
    end
  end
  return orders
end

function poverorders_recursive_generic(O, p::ZZRingElem)
  to_enlarge = typeof(O)[O]
  current = Dict{QQFieldElem, Dict{FakeFmpqMat, typeof(O)}}()
  while length(to_enlarge) > 0
    N = pop!(to_enlarge)
    new = poverorders_one_step_generic(N, p)
    for S in new
      H = basis_matrix(FakeFmpqMat, S, copy = false)
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

function overorders_by_prime_splitting_generic(O)
  orders = Vector{typeof(O)}[]

  for (p, ) in factor(discriminant(O))
    push!(orders, poverorders_recursive_generic(O, p))
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

################################################################################
#
#  Naive overorders
#
################################################################################

# Get all poveroders of O in N by looking at the quotient N/O (after intersecting with pmaximal_overoder)
# and the use the MeatAxe
function poverorders_nonrecursive_meataxe(O, N, p::ZZRingElem)
  K = _algebra(O)
  d = degree(O)
  M = N
  A, mA = quo(M, O)
  orders = typeof(O)[O]
  if order(A) == 1
    return orders
  end

  B = mA.bottom_snf_basis

  autos = FinGenAbGroupHom[]

  for i in 1:d
    if isone(B[i])
      continue
    end

    push!(autos, induce(mA, x -> M(B[i]*_elem_in_algebra(x))))

    if !is_commutative(M)
      push!(autos, induce(mA, x -> M((_elem_in_algebra(x) * B[i]))))
    end
  end

  potential_basis = Vector{elem_type(K)}(undef, d)
  orders = typeof(O)[]

  for i in 1:mA.offset
    potential_basis[i] = mA.bottom_snf_basis[i]
  end

  offset = mA.offset

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
    bmat = _hnf!_integral(bmat)
    if b
      push!(orders, order(K, bmat))
    else
      excess += 1
    end
  end
  return orders
end

# Compute all overorders of O in M
function overorders_by_prime_splitting_nonrecursive(O, M)
  orders = Vector{typeof(O)}[]

  for (p, ) in factor(div(index(M), index(O)))
    push!(orders, poverorders_nonrecursive_meataxe(O, M, p))
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

function pprimary_overorders_bass(O, P)
  res = typeof(O)[]
  O1 = ring_of_multipliers(P)
  if discriminant(O1) == discriminant(O)
    return res
  end
  K = _algebra(O)
  O1n = order(K, _hnf_integral(basis_matrix(FakeFmpqMat, O1, copy = false)), check = false, cached = false)
  push!(res, O1n)
  primes = prime_ideals_over(O1, P)
  while length(primes) == 1
    O2 = ring_of_multipliers(primes[1])
    if discriminant(O2) == discriminant(O1)
      return res
    end
    O2n = order(K, _hnf_integral(basis_matrix(FakeFmpqMat, O2, copy = false)), check = false, cached = false)
    push!(res, O2n)
    O1 = O2
    primes = prime_ideals_over(O1, primes[1])
  end
  @assert length(primes) == 2
  #There was branching.
  res1 = typeof(O)[]
  O3 = O1
  O2 = ring_of_multipliers(primes[1])
  while discriminant(O3) != discriminant(O2)
    O2n = order(K, _hnf_integral(basis_matrix(FakeFmpqMat, O2, copy = false)), check = false, cached = false)
    push!(res1, O2n)
    O3 = O2
    P = prime_ideals_over(O2, primes[1])[1]
    O2 = ring_of_multipliers(P)
  end

  res2 = typeof(O)[]
  O3 = O1
  O2 = ring_of_multipliers(primes[2])
  while discriminant(O3) != discriminant(O2)
    O2n = order(K, _hnf_integral(basis_matrix(FakeFmpqMat, O2, copy = false)), check = false, cached = false)
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

################################################################################
#
#  IsBass function
#
################################################################################

function is_bass(O, P)
  M = maximal_order(O)
  Q = extend(P, M)
  p = minimum(P)
  resfield_dim = valuation(norm(P), p)
  ext_dim = valuation(norm(Q), p)
  @assert mod(ext_dim, resfield_dim) == 0
  return div(ext_dim, resfield_dim) <= 2
end

function is_bass(O::AbsSimpleNumFieldOrder, p::ZZRingElem)
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

@doc doc"""
    is_bass(O::AbsSimpleNumFieldOrder) -> Bool

Return whether the order `\mathcal{O}` is Bass.
"""
function is_bass(O::AbsSimpleNumFieldOrder)
  f = minimum(conductor(O))
  M = maximal_order(nf(O))
  for (p, ) in factor(f)
    if !is_bass(O, p)
      return false
    end
  end
  return true
end

function is_bass(O::AlgAssAbsOrd)
  @assert is_commutative(O)
  n, f = is_perfect_power_with_data(divexact(discriminant(O), discriminant(maximal_order(O))))
  @assert n % 2 == 0
  for (p, _) in factor(f)
    for P in prime_ideals_over(O, p)
      if !is_bass(O, P)
        return false
      end
    end
  end
  return true
end

################################################################################
#
#  IsGorenstein function
#
################################################################################

@doc doc"""
    is_gorenstein(O::AbsSimpleNumFieldOrder) -> Bool

Return whether the order `\mathcal{O}` is Gorenstein.
"""
function is_gorenstein(O::AbsSimpleNumFieldOrder)
  codiff = codifferent(O)
  R = simplify(simplify(colon(1*O, codiff.num) * codiff) * codiff.den)
  return isone(norm(R))
end

function is_gorenstein(O::AlgAssAbsOrd)
  @assert is_commutative(O)
  n, f = is_perfect_power_with_data(divexact(discriminant(O), discriminant(maximal_order(O))))
  @assert n % 2 == 0
  for (p, _) in factor(f)
    for P in prime_ideals_over(O, p)
      if !is_gorenstein(O, P)
        return false
      end
    end
  end
  return true
end

function is_gorenstein(O, p::Int)
  return is_gorenstein(O, ZZRingElem(p))
end

function is_gorenstein(O, p::ZZRingElem)
  codiff = codifferent(O)
  R = simplify(simplify(colon(1*O, codiff.num) * codiff) * codiff.den)
  v = valuation(norm(R), p)
  return v == 0
end

function is_gorenstein(O, P)
  J = colon(1 * O, P)
  return isone(norm(P)*det(basis_matrix_wrt(J, O, copy = false)))
end

# This is very slow!
function intersect(x::AbsSimpleNumFieldOrder, y::AbsSimpleNumFieldOrder)
  d = degree(x)
  g = lcm(denominator(basis_matrix(FakeFmpqMat, x, copy = false)), denominator(basis_matrix(FakeFmpqMat, y)))
  H = vcat(divexact(g * basis_matrix(FakeFmpqMat, x).num, basis_matrix(FakeFmpqMat, x).den), divexact(g * basis_matrix(FakeFmpqMat, y).num, basis_matrix(FakeFmpqMat, y).den))
  K = kernel(H, side = :left)
  return order(nf(x), FakeFmpqMat(_hnf_integral(sub(K, 1:d, 1:d)*divexact(g * basis_matrix(FakeFmpqMat, x).num, basis_matrix(FakeFmpqMat, x).den), :lowerleft), g))
end

function intersect(x::AlgAssAbsOrd, y::AlgAssAbsOrd)
  d = degree(x)
  g = lcm(denominator(basis_matrix(FakeFmpqMat, x)), denominator(basis_matrix(FakeFmpqMat, y)))
  H = vcat(divexact(g * basis_matrix(FakeFmpqMat, x).num, basis_matrix(FakeFmpqMat, x).den), divexact(g * basis_matrix(FakeFmpqMat, y).num, basis_matrix(FakeFmpqMat, y).den))
  K = kernel(H, side = :left)
  return order(_algebra(x), FakeFmpqMat(_hnf_integral(sub(K, 1:d, 1:d)*divexact(g * basis_matrix(FakeFmpqMat, x).num, basis_matrix(FakeFmpqMat, x).den), :lowerleft), g))
end

################################################################################
#
#  Goursat
#
################################################################################

function ideals_with_norm(O::AbsSimpleNumFieldOrder, p::ZZRingElem, n::Int)
  pn = p^n
  pInt = Int(p)
  K = nf(O)
  d = degree(O)
  ideals = []
  B = basis(O)

  autos = FinGenAbGroupHom[]

  A = abelian_group(ZZRingElem[pn for i in 1:d])

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
      new_basis_matrix = zero_matrix(ZZ, d, d)
      T = image(s[2], false)
      G = domain(T[2])
      for i in 1:d
        v = T[2](G[i]).coeff
        if iszero(v)
          new_basis_matrix[i, i] = pn
        else
          for j in 1:d
            new_basis_matrix[i, j] = v[1, j]
          end
        end
      end
      push!(ideals, ([pInt^y for y in ppar], ideal(O, new_basis_matrix)))
    end
  end
  return ideals
end

function index(R::AbsSimpleNumFieldOrder, S::AbsSimpleNumFieldOrder)
  r = gen_index(R)
  s = gen_index(S)
  i = r^-1 * s
  @assert isinteger(i)
  return ZZ(i)
end

function poverorders_goursat(O1::AbsSimpleNumFieldOrder, O2::AbsSimpleNumFieldOrder, p::ZZRingElem)
  l1 = poverorders(O1, p)
  l2 = poverorders(O2, p)
  data_from_l2 = Dict{Vector{Int}, Vector{Tuple{typeof(O1), ideal_type(O1)}}}()
  d = degree(O2)
  for O in l2
    i = index(O2, O)
    e, _ = is_perfect_power_with_data(i)
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

function abelian_group(Q::AbsOrdQuoRing)
  A = abelian_group(Q.basis_matrix)
  S, mS = snf(A)
  B = basis(Q.base_ring, copy = false)
  f = a -> begin aa = mS(a); Q(sum(aa.coeff[i] * B[i] for i in 1:degree(Q.base_ring))) end
  g = b -> mS\A(coordinates(b.elem))
  return S, f, g
end

function is_isomorphic(Q1::AbsSimpleNumFieldOrderQuoRing, Q2::AbsSimpleNumFieldOrderQuoRing)
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

  elements_with_correct_order = Dict{ZZRingElem, Vector{FinGenAbGroupElem}}()

  for g in Q2_A
    o = order(g)
    if o in orders
      #elem_g = Q2_mA(g)
      if !haskey(elements_with_correct_order, o)
        elements_with_correct_order[o] = FinGenAbGroupElem[g]
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
    h = hom(Q1_A, collect(poss))
    if !is_bijective(h)
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
      M = Array{ZZRingElem}(degree(O1), degree(O2))
      for i in 1:degree(O1)
        v = coordinates(Q2_mA(h(Q1_mA_inv(Q1(basis_O1[i])))).elem)
        for j in 1:degree(O2)
          M[i, j] = v[j]
        end
      end
      push!(isos, M)
    end
  end
  return isos
end

################################################################################
#
#  Clean up
#
################################################################################

contains_equation_order(O) = false

################################################################################
#
#  Idempotent splitting
#
################################################################################

function _overorders_via_idempotent_splitting(M)
  A = _algebra(M)
  d = dim(A)
  wd = decompose(A)

  if length(wd) == 1
    return overorders(M)
  end

  ba = basis(M)
  oorders = Vector{Vector{elem_type(A)}}[]
  for (B, mB) in wd
    e = mB(one(B))
    @assert e in M
    MinB = order(B, sub(_hnf_integral(basis_matrix([ mB\_elem_in_algebra(b) for b in ba ]), :lowerleft), (d - dim(B) + 1):d, 1:dim(B)))
    @assert defines_order(B, _elem_in_algebra.(basis(MinB)))[1]
    @assert one(B) in MinB
    orders = overorders(MinB)
    bases = Vector{Vector{elem_type(A)}}(undef, length(orders))
    for (i, O) in enumerate(orders)
      bases[i] = [ mB(_elem_in_algebra(b)) for b in basis(O) ]
    end

    push!(oorders, bases)
  end

  println("Computing all products ... ")

  res = Vector{typeof(M)}(undef, prod(length(oorders[i]) for i in 1:length(oorders)))

  I = Iterators.product(oorders...)
  @time for (j, i) in enumerate(I)
    H = _hnf!_integral(basis_matrix(FakeFmpqMat, vcat(i...)))
    res[j] = order(A, H)
  end
  return res
end
