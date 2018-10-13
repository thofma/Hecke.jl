################################################################################
#
#  Top level functions
#
################################################################################

function _multgrp_mod_ideal(O::AlgAssAbsOrd, a::AlgAssAbsOrdIdl)
  A = algebra(O)
  OO = maximal_order(A)

  if OO == O
    return _multgrp_mod_ideal_maximal(O, a)
  end

  aOO = a*OO

  fac_of_aOO = factor(aOO)
  prime_ideals = Dict{ideal_type(O), Vector{ideal_type(OO)}}()
  for (p, e) in fac_of_aOO
    q = contract(p, O)
    if haskey(prime_ideals, q)
      push!(prime_ideals[q], p)
    else
      prime_ideals[q] = [ p ]
    end
  end

  # keys are the same as in prime_ideals
  primary_ideals = Dict{ideal_type(O), ideal_type(O)}()
  for p in keys(prime_ideals)
    primes_above = prime_ideals[p]
    q = primes_above[1]^fac_of_aOO[primes_above[1]]
    for i = 2:length(primes_above)
      q = intersection(q, primes_above[i]^fac_of_aOO[primes_above[i]])
    end
    primary_ideals[p] = contract(q, O)
  end

  groups = Vector{GrpAbFinGen}()
  maps = Vector{GrpAbFinGenToAlgAssAbsOrdMap}()
  ideals = Vector{ideal_type(O)}() # values of primary_ideals, but in the "right" order
  for (p, q) in primary_ideals
    G, GtoO = _multgrp_mod_q(p, q, prime_ideals[p][1])
    push!(groups, G)
    push!(maps, GtoO)
    push!(ideals, q)
  end

  G, GtoO = _direct_product(groups, maps, ideals, a)
  S, StoG, StoO = snf(G, GtoO)
  return S, StoO
end

function _multgrp_mod_ideal_maximal(O::AlgAssAbsOrd, a::AlgAssAbsOrdIdl)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)
  groups = Vector{Tuple{GrpAbFinGen, GrpAbFinGenToNfOrdQuoRingMultMap}}()
  for i = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[i]
    ai = _as_ideal_of_number_field(a, AtoK)
    push!(groups, multiplicative_group(quo(maximal_order(K), ai)[1]))
  end

  G = groups[1][1]
  for i = 2:length(groups)
    G = direct_product(G, groups[i][1])[1]
  end

  S, StoG = snf(G)

  generators = Vector{elem_type(O)}()
  for i = 1:ngens(S)
    x = StoG(S[i])
    y = O()
    offset = 1
    for j = 1:length(groups)
      H, HtoQ = groups[j]
      n = ngens(H)
      if iszero(n)
        continue
      end

      t = H([ x.coeff[1, k] for k = offset:(offset + n - 1) ])
      K, AtoK = fields_and_maps[j]
      Q = codomain(HtoQ)
      OK = base_ring(Q)
      OKtoQ = NfOrdQuoMap(OK, Q)
      y += O(AtoK\(K(OKtoQ\(HtoQ(t)))))
      offset += n
    end
    push!(generators, y)
  end

  function disc_log(x::AlgAssAbsOrdElem)
    y = zero_matrix(FlintZZ, 1, 0)
    for i = 1:length(groups)
      K, AtoK = fields_and_maps[i]
      H, HtoQ = groups[i]
      Q = codomain(HtoQ)
      OK = base_ring(Q)
      h = HtoQ\(Q(OK(AtoK(elem_in_algebra(x, Val{false})))))
      y = hcat(y, h.coeff)
    end
    s = StoG\G(y)
    return [ s.coeff[1, i] for i = 1:ngens(S) ]
  end

  return S, GrpAbFinGenToAlgAssAbsOrdMap(S, O, generators, disc_log, a)
end

################################################################################
#
#  Order modulo primary ideal
#
################################################################################

# p should be a prime ideal in a non-maximal order, q a p-primary ideal and
# P a prime ideal above p in the maximal order
function _multgrp_mod_q(p::AlgAssAbsOrdIdl, q::AlgAssAbsOrdIdl, P::AlgAssAbsOrdIdl)
  G1, G1toO = _multgrp_mod_p(p, P)

  if p == q
    return G1, G1toO
  end

  G2, G2toO = _1_plus_p_mod_1_plus_q(p, q)

  if ngens(G1) == 0
    return G2, G2toO
  end

  gen1 = G1toO(G1[1])
  @assert issnf(G1) && issnf(G2)
  rel1 = G1.snf[1]
  gen1_obcs = powermod(gen1, G2.snf[end], q)
  gens = [ gen1_obcs ; G2toO.generators ]
  G1toO.generators[1] = gen1_obcs

  G = direct_product(G1, G2)[1]

  obcs_inv = gcdx(G2.snf[end], rel1)[2]
  function disc_log(x::AlgAssAbsOrdElem)
    r = mod((G1toO.discrete_logarithm(x))[1]*obcs_inv, rel1)
    x *= gen1_obcs^mod(-r, rel1)
    return append!([ r ], G2toO.discrete_logarithm(x))
  end

  GtoO = GrpAbFinGenToAlgAssAbsOrdMap(G, order(p), gens, disc_log, q)
  S, StoG, StoO = snf(G, GtoO)
  return S, StoO
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

  q = det(basis_mat(p, Val{false}))
  q = q - 1 # the cardinality of (O/p)^\times
  if isone(q)
    G = GrpAbFinGen(fmpz[])
    function disc_log2(x::AlgAssAbsOrdElem)
      return fmpz[]
    end
    GtoO = GrpAbFinGenToAlgAssAbsOrdMap(G, O, elem_type(O)[], disc_log2, p)
    return G, GtoO
  end

  G, GtoOA = _multgrp_mod_ideal_maximal(OA, P)
  qq = order(G)
  @assert ngens(G) <= 1

  a = O()
  g = G[1]
  if qq == q
    # Maybe we are lucky and don't need to search for another generator
    aa = GtoOA(G[1])
    x = _check_elem_in_order(elem_in_algebra(aa, Val{false}), O, Val{true})
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

      aa = OA(a)
      g = GtoOA\aa
      n = g.coeff[1]
      if gcd(n, qq) == r
        break
      end
    end
  end

  if qq == q
    function disc_log3(x::AlgAssAbsOrdElem)
      xOA = OA(x)
      return GtoOA.discrete_logarithm(xOA)
    end
    return G, GrpAbFinGenToAlgAssAbsOrdMap(G, O, [ a ], disc_log3, p)
  end

  H, HtoG = sub(G, [ g ])
  S, StoH = snf(H)

  function disc_log(x::AlgAssAbsOrdElem)
    xOA = OA(x)
    g = GtoOA\xOA
    b, h = haspreimage(HtoG, g)
    @assert b
    b, s = haspreimage(StoH, h)
    @assert b
    return [ s.coeff[1, i] for i = 1:ngens(S) ]
  end

  return S, GrpAbFinGenToAlgAssAbsOrdMap(S, O, [ a ], disc_log, p)
end

################################################################################
#
#  Computation of (1 + p)/(1 + q)
#
################################################################################

# Much of this is taken from the implementation in NfOrd/ResidueRingMultGrp.jl

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

  # Cohen "Advanced Topics in Computational Number Theory" Algorithm 4.2.16
  function disc_log(b::AlgAssAbsOrdElem)
    a = fmpz[]
    k = 1
    for i in 1:length(dlogs)
      aa = dlogs[i](b)
      prod = one(O)
      for j in 1:length(aa)
        prod = mod(prod*powermod(g[k], aa[j], q), q)
        k += 1
      end
      a = fmpz[ a ; aa ]
      bb, b = isdivisible_mod_ideal(b, prod, q)
      @assert bb
    end
    return a
  end

  toO = GrpAbFinGenToAlgAssAbsOrdMap(O, g, M, disc_log, q)
  S, mS, StoO = snf(toO)
  return S, StoO
end

# Given the groups (1 + p)/(1 + p^k + q) (via g and M) and
# (1 + p^k + q)/(^ + p^(2*k) + q) (via h and N) and a discrete logarithm in the
# second group this function computes the group (1 + p)/(1 + p^(2*k) + q).
function _expand(g::Vector{T}, M::fmpz_mat, h::Vector{T}, N::fmpz_mat, disc_log::Function, q::AlgAssAbsOrdIdl) where { T <: AlgAssAbsOrdElem }
  isempty(g) && return h, N
  isempty(h) && return g, M

  @assert issnf(N)
  O = order(q)
  Z = zero_matrix(FlintZZ, rows(M) + rows(N), cols(M) + cols(N))
  for i = 1:rows(M)
    for j = 1:cols(M)
      Z[i, j] = M[i, j]
    end
  end
  for i = 1:rows(N)
    Z[i + rows(M), i + rows(M)] = N[i, i]
  end
  for i = 1:rows(M)
    el = one(O)
    for j = 1:cols(M)
      el = mod(el*powermod(g[j], M[i, j], q), q)
    end
    alpha = disc_log(el)
    for j in 1:cols(N)
      Z[i, j + cols(M)] = -alpha[j]
    end
  end

  append!(g, h)
  return g, Z
end

# Compute the group (1 + puq)/(1 + pvq), where it should hold puq = p^u + q and
# pvq = p^v + q with v <= 2*u.
# Cohen "Advanced Topics in Computational Number Theory" Algorithm 4.2.15.
function _1_plus_pu_plus_q_mod_1_plus_pv_plus_q(puq::AlgAssAbsOrdIdl, pvq::AlgAssAbsOrdIdl)
  O = order(puq)
  b = basis(puq, Val{false})

  # Compute (p^u + q)/(p^v + q)
  N = basis_mat(pvq, Val{false})*basis_mat_inv(puq, Val{false})
  @assert denominator(N) == 1
  G = AbelianGroup(numerator(N))
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

  # The first part of Algorithm 4.2.16 in Cohen "Advanced Topics..."
  M = basis_mat_inv(puq, Val{false})*StoG.imap
  function disc_log(x::AlgAssAbsOrdElem)
    y = mod(x - one(O), pvq)
    y_fakemat = FakeFmpqMat(matrix(FlintZZ, 1, degree(O), elem_in_basis(y)), fmpz(1))
    mul!(y_fakemat, y_fakemat, M)
    denominator(y_fakemat) != 1 && error("Element is in the ideal")
    return vec(Array(numerator(y_fakemat)))
  end

  return gens, rels(S), disc_log
end

################################################################################
#
#  SNF and direct product (which transform the map too)
#
################################################################################

# Returns the SNF S of G and a map from S to G and one from S to codomain(GtoR).
# Some computations are done modulo GtoR.modulus, if this is defined.
function snf(G::GrpAbFinGen, GtoR::GrpAbFinGenToAlgAssAbsOrdMap)
  S, StoG = snf(G)

  R = codomain(GtoR)
  modulo = isdefined(GtoR, :modulus)

  if ngens(G) == 0
    if modulo
      StoR = typeof(GtoR)(S, R, GtoR.generators, GtoR.discrete_logarithm, GtoR.modulus)
    else
      StoR = typeof(GtoR)(S, R, GtoR.generators, GtoR.discrete_logarithm)
    end
    return S, StoG, StoR
  end

  function disclog(x)
    @assert parent(x) == R
    y = GtoR.discrete_logarithm(x)
    a = StoG\(G(y))
    return fmpz[ a[j] for j = 1:ngens(S) ]
  end

  gens_snf = Vector{elem_type(R)}(undef, ngens(S))
  for i = 1:ngens(S)
    x = StoG(S[i]).coeff
    for j = 1:ngens(G)
      x[1, j] = mod(x[1, j], S.snf[end])
    end
    y = one(R)
    for j = 1:ngens(G)
      if modulo
        y = mod(y*powermod(GtoR.generators[j], x[1, j], GtoR.modulus), GtoR.modulus)
      else
        y *= GtoR.generators[j]^(x[1, j])
      end
    end
    gens_snf[i] = y
  end

  if modulo
    StoR = typeof(GtoR)(S, R, gens_snf, disclog, GtoR.modulus)
  else
    StoR = typeof(GtoR)(S, R, gens_snf, disclog)
  end

  return S, StoG, StoR
end

snf(GtoR::GrpAbFinGenToAlgAssAbsOrdMap) = snf(domain(GtoR), GtoR)

# It is assumed that the ideals are coprime and the codomains of the maps should
# all be the same order.
function _direct_product(groups::Vector{GrpAbFinGen}, maps::Vector{S}, ideals::Vector{T}, modulus::AlgAssAbsOrdIdl...) where { S <: GrpAbFinGenToAlgAssAbsOrdMap, T <: AlgAssAbsOrdIdl }
  @assert length(groups) == length(maps)
  @assert length(groups) != 0
  @assert length(ideals) >= length(groups)

  if length(groups) == 1 && length(ideals) == 1
    if length(modulus) == 1
      if !isdefined(maps[1], :modulus) || maps[1].modulus != modulus[1]
        m = GrpAbFinGenToAlgAssAbsOrdMap(groups[1], O, maps[1].generators, maps[1].discrete_logarithm, modulus...)
        return groups[1], m
      end
    end
    return groups[1], maps[1]
  end

  G = groups[1]
  for i = 2:length(groups)
    G = direct_product(G, groups[i])[1]
  end

  O = codomain(maps[1])
  oneO = one(O)
  generators = Vector{elem_type(O)}()
  t = [ oneO for i = 1:length(ideals) ]
  for i = 1:length(groups)
    for j = 1:ngens(groups[i])
      t[i] = maps[i].generators[j]
      g = crt(t, ideals)
      push!(generators, g)
      t[i] = oneO
    end
  end

  if length(groups) == 1
    m = GrpAbFinGenToAlgAssAbsOrdMap(G, O, generators, maps[1].discrete_logarithm, modulus...)
    return G, m
  end

  function disc_log(a::AlgAssAbsOrdElem)
    result = Vector{fmpz}()
    for map in maps
      append!(result, map.discrete_logarithm(a))
    end
    return result
  end

  m = GrpAbFinGenToAlgAssAbsOrdMap(G, O, generators, disc_log, modulus...)
  return G, m
end
