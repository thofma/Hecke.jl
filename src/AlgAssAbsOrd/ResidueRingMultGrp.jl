################################################################################
#
#  Top level functions
#
################################################################################

@doc raw"""
    multiplicative_group(Q::AlgAssAbsOrdQuoRing)
      -> FinGenAbGroup, GrpAbFinGenToAbsOrdMap
    unit_group(Q::AlgAssAbsOrdQuoRing) -> FinGenAbGroup, GrpAbFinGenToAbsOrdMap

Returns the group $Q^\times$ and the injection $Q^\times -> Q$.
"""
function multiplicative_group(Q::AlgAssAbsOrdQuoRing{S, T}) where {S, T}
  if !isdefined(Q, :multiplicative_group)
    O = base_ring(Q)
    OO = maximal_order(algebra(O))
    if O == OO
      G, GtoQ = _multgrp(Q)
    else
      G, GtoQ = _multgrp_non_maximal(Q)
    end
    Q.multiplicative_group = GtoQ
  end
  mQ = Q.multiplicative_group::GrpAbFinGenToAbsOrdQuoRingMultMap{typeof(base_ring(Q)), ideal_type(base_ring(Q)), elem_type(base_ring(Q))}
  return domain(mQ), mQ
end

unit_group(Q::AlgAssAbsOrdQuoRing) = multiplicative_group(Q)

function _multgrp_non_maximal(Q::AbsOrdQuoRing{U, T}) where {U, T}
  O = base_ring(Q)
  a = ideal(Q)
  A = algebra(O)
  OO = maximal_order(A)

  primary_ideals = primary_decomposition(a, O)
  groups = Vector{FinGenAbGroup}()
  maps = Vector{GrpAbFinGenToAbsOrdQuoRingMultMap{U, T, elem_type(OO)}}()
  ideals = Vector{ideal_type(O)}() # values of primary_ideals, but in the "right" order
  for (q, p) in primary_ideals
    G, GtoQ = _multgrp_mod_q(p, q, prime_ideals_over(OO, p)[1])
    push!(groups, G)
    push!(maps, GtoQ)
    push!(ideals, q)
  end

  G, GtoQ = _direct_product(groups, maps, ideals, Q)
  S, StoG, StoQ = snf(G, GtoQ)
  return S, StoQ
end

function _multgrp(Q::AbsOrdQuoRing{U, T}) where {U, T}
  O = base_ring(Q)
  OtoQ = AbsOrdQuoMap(O, Q)
  a = ideal(Q)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)
  groups = Vector{Tuple{FinGenAbGroup, GrpAbFinGenToAbsOrdQuoRingMultMap{AbsSimpleNumFieldOrder, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsSimpleNumFieldOrderElem}}}()
  for i = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[i]
    ai = _as_ideal_of_number_field(a, AtoK)
    push!(groups, multiplicative_group(quo(maximal_order(K), ai)[1]))
  end

  G = groups[1][1]
  for i = 2:length(groups)
    G = direct_product(G, groups[i][1]; task = :none)::FinGenAbGroup
  end
  S, StoG = snf(G)

  generators = Vector{elem_type(Q)}()
  for i = 1:ngens(S)
    x = StoG(S[i])
    y = zero(Q)
    offset = 1
    for j = 1:length(groups)
      H, HtoQK = groups[j]
      n = ngens(H)
      if iszero(n)
        continue
      end

      s = H([ x.coeff[1, k] for k = offset:(offset + n - 1) ])
      K, AtoK = fields_and_maps[j]
      QK = codomain(HtoQK)
      OK = base_ring(QK)
      OKtoQK = NfOrdQuoMap(OK, QK)
      t = K(OKtoQK\(HtoQK(s)))
      y += OtoQ(O(AtoK\t))
      offset += n
    end
    push!(generators, y)
  end

  local disc_log
  let fields_and_maps = fields_and_maps, groups = groups, OtoQ = OtoQ, StoG = StoG, G = G, S = S
    function disc_log(x::AbsOrdQuoRingElem)
      y = zero_matrix(FlintZZ, 1, 0)
      for i = 1:length(groups)
        K, AtoK = fields_and_maps[i]
        H, HtoQK = groups[i]
        QK = codomain(HtoQK)
        OK = base_ring(QK)
        h = HtoQK\(QK(OK(AtoK(elem_in_algebra(OtoQ\x, copy = false)))))
        y = hcat(y, h.coeff)
      end
      s = StoG\G(y)
      return ZZRingElem[ s.coeff[1, i] for i = 1:ngens(S) ]
    end
  end

  return S, GrpAbFinGenToAbsOrdQuoRingMultMap(S, Q, generators, disc_log)
end

################################################################################
#
#  Order modulo primary ideal
#
################################################################################

# p should be a prime ideal in a non-maximal order, q a p-primary ideal and
# P a prime ideal above p in the maximal order
function _multgrp_mod_q(p::AlgAssAbsOrdIdl, q::AlgAssAbsOrdIdl, P::AlgAssAbsOrdIdl)

  Q, OtoQ = quo(order(q), q)
  G1, G1toO = _multgrp_mod_p(p, P)

  if p == q
    function disc_log1(x::AbsOrdQuoRingElem)
      return G1toO.discrete_logarithm(OtoQ\x)
    end
    GtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(G1, Q, map(OtoQ, G1toO.generators), disc_log1)
    return G1, GtoQ
  end

  G2, G2toO = _1_plus_p_mod_1_plus_q(p, q)

  if ngens(G1) == 0
    function disc_log2(x::AbsOrdQuoRingElem)
      return G2toO.discrete_logarithm(OtoQ\x)
    end
    GtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(G2, Q, map(OtoQ, G2toO.generators), disc_log2)
    return G2, GtoQ
  end

  gen1 = G1toO(G1[1])
  @assert is_snf(G1) && is_snf(G2)
  rel1 = G1.snf[1]
  gen1_obcs = powermod(gen1, G2.snf[end], q)
  gens = map(OtoQ, [ gen1_obcs ; G2toO.generators ])
  G1toO.generators[1] = gen1_obcs

  G = direct_product(G1, G2)[1]

  obcs_inv = gcdx(G2.snf[end], rel1)[2]
  function disc_log(x::AbsOrdQuoRingElem)
    y = OtoQ\x
    r = mod((G1toO.discrete_logarithm(y))[1]*obcs_inv, rel1)
    y *= gen1_obcs^mod(-r, rel1)
    return append!([ r ], G2toO.discrete_logarithm(y))
  end

  GtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(G, Q, gens, disc_log)
  S, StoG, StoQ = snf(G, GtoQ)
  return S, StoQ
end

################################################################################
#
#  Order modulo prime ideal
#
################################################################################

# p should be a prime ideal in a non-maximal order and P a prime ideal above
# p in the maximal order
function _multgrp_mod_p(p::AlgAssAbsOrdIdl, P::AlgAssAbsOrdIdl)
  O = order(p)
  OA = order(P) # the maximal order

  q = norm(p, O)
  @assert isone(denominator(q))
  q = numerator(q)
  q = q - 1 # the cardinality of (O/p)^\times
  if isone(q)
    G = FinGenAbGroup(ZZRingElem[])
    function disc_log2(x::AlgAssAbsOrdElem)
      return ZZRingElem[]
    end
    GtoO = GrpAbFinGenToAbsOrdMap(G, O, elem_type(O)[], disc_log2, p)
    return G, GtoO
  end

  OAP, OAtoOAP = quo(OA, P)
  G, GtoOAP = _multgrp(OAP)
  qq = order(G)
  @assert ngens(G) <= 1

  a = O()
  g = G[1]
  if qq == q
    # Maybe we are lucky and don't need to search for another generator
    aa = OAtoOAP\GtoOAP(G[1])
    x = _check_elem_in_order(elem_in_algebra(aa, copy = false), O, Val(true))
    if x
      a = O(aa, false)
    end
  end

  # Search for a generator of (O/p)^times.
  # See Bley, Endres "Picard Groups and Refined Discrete Logarithms".
  if iszero(a)
    b, r = divides(qq, q)
    @assert b

    while true
      a = rand(O, q)
      if a in p
        continue
      end

      aa = OAtoOAP(OA(a))
      g = GtoOAP\aa
      n = g.coeff[1]
      if gcd(n, qq) == r
        break
      end
    end
  end

  if qq == q
    function disc_log3(x::AlgAssAbsOrdElem)
      xx = OAtoOAP(OA(x))
      return GtoOAP.discrete_logarithm(xx)
    end
    return G, GrpAbFinGenToAbsOrdMap(G, O, [ a ], disc_log3, p)
  end

  H, HtoG = sub(G, [ g ])
  S, StoH = snf(H)

  function disc_log(x::AlgAssAbsOrdElem)
    xx = OAtoOAP(OA(x))
    g = GtoOAP\xx
    b, h = has_preimage_with_preimage(HtoG, g)
    @assert b
    b, s = has_preimage_with_preimage(StoH, h)
    @assert b
    return [ s.coeff[1, i] for i = 1:ngens(S) ]
  end

  return S, GrpAbFinGenToAbsOrdMap(S, O, [ a ], disc_log, p)
end

################################################################################
#
#  Computation of (1 + p)/(1 + q)
#
################################################################################

# Much of this is taken from the implementation in AbsSimpleNumFieldOrder/ResidueRingMultGrp.jl

# Computes (1 + p)/(1 + q) where q is a p-primary ideal (in a non-maximal order)
function _1_plus_p_mod_1_plus_q(p::AlgAssAbsOrdIdl, q::AlgAssAbsOrdIdl)
  @assert q != p

  O = order(p)
  g = Vector{elem_type(O)}()
  M = zero_matrix(FlintZZ, 0, 0)
  dlogs = Vector{Function}()

  l = 1
  pl = p
  plq = pl + q
  while plq != q
    k = l
    pk, pkq = pl, plq
    l = 2*k
    pl = pl^2
    plq = pl + q

    h, N, disc_log = _1_plus_pu_plus_q_mod_1_plus_pv_plus_q(pkq, plq)
    g, M = _expand(g, M, h, N, disc_log, q)
    push!(dlogs, disc_log)
  end

  Q, OtoQ = quo(order(q), q)
  # Cohen "Advanced Topics in Computational Number Theory" Algorithm 4.2.16
  function disc_log(b::AlgAssAbsOrdElem)
    b = OtoQ(b)
    a = ZZRingElem[]
    gQ = map(OtoQ, g)
    k = 1
    for i in 1:length(dlogs)
      aa = dlogs[i](OtoQ\b)
      prod = one(Q)
      for j in 1:length(aa)
        prod = prod*gQ[k]^aa[j]
        k += 1
      end
      a = ZZRingElem[ a ; aa ]
      b = divexact(b, prod)
    end
    return a
  end

  toO = GrpAbFinGenToAbsOrdMap(O, g, M, disc_log, q)
  S, mS, StoO = snf(toO, OtoQ)
  return S, StoO
end

function _1_plus_p_mod_1_plus_q_generators(p::AlgAssAbsOrdIdl, q::AlgAssAbsOrdIdl)
  @assert p != q

  O = order(p)
  g = Vector{elem_type(O)}()

  l = 1
  pl = p
  plq = pl + q
  while plq != q
    k = l
    pk, pkq = pl, plq
    l = 2*k
    pl = pl^2
    plq = pl + q
    append!(g, _1_plus_pu_plus_q_mod_1_plus_pv_plus_q(pkq, plq, Val(true)))
  end

  return g
end

# Given the groups (1 + p)/(1 + p^k + q) (via g and M) and
# (1 + p^k + q)/(1 + p^(2*k) + q) (via h and N) and a discrete logarithm in the
# second group this function computes the group (1 + p)/(1 + p^(2*k) + q).
function _expand(g::Vector{T}, M::ZZMatrix, h::Vector{T}, N::ZZMatrix, disc_log::Function, q::AlgAssAbsOrdIdl) where { T <: AlgAssAbsOrdElem }
  isempty(g) && return h, N
  isempty(h) && return g, M

  @assert is_snf(N)
  O = order(q)
  Z = zero_matrix(FlintZZ, nrows(M) + nrows(N), ncols(M) + ncols(N))
  for i = 1:nrows(M)
    for j = 1:ncols(M)
      Z[i, j] = M[i, j]
    end
  end
  for i = 1:nrows(N)
    Z[i + nrows(M), i + nrows(M)] = N[i, i]
  end
  for i = 1:nrows(M)
    el = one(O)
    for j = 1:ncols(M)
      el = mod(el*powermod(g[j], M[i, j], q), q)
    end
    alpha = disc_log(el)
    for j in 1:ncols(N)
      Z[i, j + ncols(M)] = -alpha[j]
    end
  end

  append!(g, h)
  return g, Z
end

# Compute the group (1 + puq)/(1 + pvq), where it should hold puq = p^u + q and
# pvq = p^v + q with v <= 2*u.
# Cohen "Advanced Topics in Computational Number Theory" Algorithm 4.2.15.
function _1_plus_pu_plus_q_mod_1_plus_pv_plus_q(puq::AlgAssAbsOrdIdl, pvq::AlgAssAbsOrdIdl, ::Val{only_generators} = Val(false)) where only_generators
  O = order(puq)
  b = [ O(x) for x in basis(puq, copy = false) ]

  # Compute (p^u + q)/(p^v + q)
  N = basis_matrix(pvq, copy = false)*basis_mat_inv(puq, copy = false)
  @assert denominator(N, copy = false) == 1
  G = abelian_group(numerator(N, copy = false))
  S, StoG = snf(G)

  gens = Vector{elem_type(O)}(undef, ngens(S))
  for i = 1:ngens(S)
    x = StoG(S[i])
    gens[i] = O()
    for j = 1:ngens(G)
      gens[i] += mod(x[j], S.snf[end])*b[j]
    end
  end

  # We want generators of (1 + p^u + q)/(1 + p^v + q)
  map!(x -> x + one(O), gens, gens)

  if only_generators
    return gens
  end

  # The first part of Algorithm 4.2.16 in Cohen "Advanced Topics..."
  M = basis_matrix(FakeFmpqMat, O, copy = false)*basis_mat_inv(puq, copy = false)*StoG.imap
  y_fakemat2 = FakeFmpqMat(zero_matrix(FlintZZ, 1, ncols(M)), ZZRingElem(1))
  function disc_log(x::AlgAssAbsOrdElem)
    y = mod(x - one(O), pvq)
    y_fakemat = FakeFmpqMat(matrix(FlintZZ, 1, degree(O), coordinates(y)), ZZRingElem(1))
    mul!(y_fakemat2, y_fakemat, M)
    #@assert y_fakemat2 == y_fakemat * M
    denominator(y_fakemat2) != 1 && error("Element is in the ideal")
    return vec(Array(numerator(y_fakemat2)))
  end

  return gens, rels(S), disc_log
end
