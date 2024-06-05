################################################################################
#
#  High level functions
#
################################################################################

@doc raw"""
    picard_group(O::AbsSimpleNumFieldOrder) -> FinGenAbGroup, MapClassGrp

Returns the Picard group of $O$ and a map from the group in the set of
(invertible) ideals of $O$.
"""
function picard_group(O::AbsSimpleNumFieldOrder)
  mP = get_attribute!(O, :picard_group) do
    OK = maximal_order(nf(O)) # We need it later anyway
    if O == OK
      return class_group_as_picard(OK)[2]
    end
    return _picard_group(O)[2]
  end::MapPicardGrp{FinGenAbGroup, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}
  return domain(mP), mP
end

function unit_group_non_maximal(O::AbsSimpleNumFieldOrder)
  mU = get_attribute!(O, :unit_group_non_maximal) do
    if is_maximal(O)
      return _unit_group_maximal(O)[2]
    end
    OK = maximal_order(O)
    UU, mUU = unit_group(OK)
    return _unit_group_non_maximal(O, OK, mUU)[2]
  end::MapUnitGrp{AbsSimpleNumFieldOrder}
  return domain(mU), mU
end

################################################################################
#
#  Internals
#
################################################################################

function class_group_as_picard(OK::AbsSimpleNumFieldOrder)
  C, mC = class_group(OK)
  mp = MapPicardGrp{FinGenAbGroup, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  mp.header = MapHeader(C, IdealSet(OK), mC.header.image, mC.header.preimage)
  return C, mp
end

# Computes \bigoplus_p OK_p^\times/O_p^\times where the sum runs over all prime
# ideals p containing the conductor of O and OK is the maximal order.
# This group is isomorphic to (OK/F)^\times/(O/F)^\times.
# Algorithm 8.1 in Klueners, Pauli: Computing residue class rings and Picard
# groups of orders
function OO_mod_F_mod_O_mod_F(O::AbsNumFieldOrder)
  OK = maximal_order(nf(O))
  F = conductor(O, OK)
  FOK = extend(F, OK)
  QF, OKtoQF = quo(OK, FOK)

  fac = factor(QF)
  D = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{Int}}() # keys are ideals p of O, values the indices of the ideals q in OK such that contract(q, O) == p.
  i = 1
  factors_of_FOK = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}(undef, length(fac)) # ideals of OK
  for (q, e) in fac
    p = contract(q, O)
    p.is_prime = q.is_prime
    get!(D, p, Int[])
    append!(D[p], i)
    factors_of_FOK[i] = q^e
    i += 1
  end

  groups = Vector{FinGenAbGroup}()
  maps = Vector{GrpAbFinGenToNfOrdQuoRingMultMap}()
  for p in keys(D)
    # Find m such that p^m*O_p \subseteq F*O_p
    m = 0
    prime_ideals_over_p = Vector{Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}}() # ideals of OK
    pOK = extend(p, OK)
    fac2 = factor(pOK)
    for (q, e) in fac2
      f = get(fac, q, 0)
      if f != 0
        push!(prime_ideals_over_p, (q, f))
        m = max(m, ceil(Int, f/e))
      end
    end

    # Compute (OK_p/F*OK_p)^\times
    groups2 = Vector{FinGenAbGroup}(undef, length(prime_ideals_over_p))
    maps2 = Vector{GrpAbFinGenToNfOrdQuoRingMultMap}(undef, length(prime_ideals_over_p))
    for i = 1:length(prime_ideals_over_p)
      q, eq = prime_ideals_over_p[i]
      groups2[i], maps2[i] = _multgrp_mod_pv(q, eq, q^eq)
    end
    G, GtoQ, OKtoQ = direct_product(groups2, maps2)
    Q = codomain(GtoQ)

    # Compute (O_p/p^mO_p)^\times
    GG, mGG = _multgrp_mod_pv(p, m, p^m; method = :quadratic)
    # Klueners and Pauli want to have the generators of GG coprime to other
    # primes. But I don't see a reason for this.
    #=
    gens = Vector{elem_type(Q)}(ngens(GG))
    oneOK = OK(1)
    t = [ oneOK for i = 1:length(factors_of_FOK) ]
    for i = 1:length(gens)
      gOK = OK(elem_in_nf(mGG.generators[i]))
      for j in D[p]
        t[j] = gOK
      end
      gens[i] = Q(crt(t, factors_of_FOK))
    end
    gens = map(x -> GtoQ\(OKtoQ(OK(x.elem))), gens)
    =#

    gens = Vector{FinGenAbGroupElem}(undef, length(mGG.generators))
    for ind_for = 1:length(gens)
      gens[ind_for] = GtoQ\(OKtoQ(OK(mGG.generators[ind_for].elem)))
    end
    H, GtoH = quo(G, gens, false)
    HtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(H, Q, GtoQ.generators, GtoQ.discrete_logarithm)
    push!(groups, H)
    push!(maps, HtoQ)
  end

  G, GtoQ = direct_product(groups, maps, QF)

  S, StoG, StoQ = snf(G, GtoQ)
  return S, StoQ, OKtoQF
end

function _unit_group_non_maximal(O::Union{AbsNumFieldOrder, AlgAssAbsOrd}, OK, GtoOK::MapUnitGrp{T}) where {T}
  # OK = maximal_order
  # _, GtoK = unit_group[_fac_elem](OK)
  G = domain(GtoOK)

  if isdefined(O, :picard_group) && isdefined(O.picard_group, :OO_mod_F_mod_O_mod_F) # only for AbsNumFieldOrder
    HtoQ = O.picard_group.OO_mod_F_mod_O_mod_F
    H = domain(HtoQ)
    OKtoQ = AbsOrdQuoMap(codomain(HtoQ))
  else
    H, HtoQ, OKtoQ = OO_mod_F_mod_O_mod_F(O)
  end

  # We use the exact sequence
  # 0 --> O^\times --> O_K^\times --> (O_K/F)^\times)/(O/F)^\times
  # that is 0 --> O^\times --> G --> H.
  # So, O^\times is the kernel of a map from G to H
  # (we really want a FinGenAbGroupHom, so we can't use compose to build this map)
  M = zero_matrix(FlintZZ, ngens(G), ngens(H))
  for i = 1:ngens(G)
    q = OKtoQ(GtoOK(G[i]))
    h = HtoQ\q
    for j = 1:ngens(H)
      M[i, j] = h.coeff[1, j]
    end
  end
  GtoH = hom(G, H, M, check = false)

  K, KtoG = kernel(GtoH)
  S, StoK = snf(K)
  StoG = compose(StoK, KtoG)

  # Build the map from S to O
  function _image(x::FinGenAbGroupElem)
    @assert parent(x) == S
    y = GtoOK(StoG(x))
    if T <: FacElemMon
      return y
    else
      return O(_elem_in_algebra(y))
    end
  end

  function _preimage(x::Union{ AbsNumFieldOrderElem, AlgAssAbsOrdElem })
    @assert parent(x) === O
    y = OK(_elem_in_algebra(x))
    g = GtoOK\y
    b, k = has_preimage_with_preimage(KtoG, g)
    @assert b
    b, s = has_preimage_with_preimage(StoK, k)
    @assert b
    return s
  end

  if T <: FacElemMon
    StoO = MapUnitGrp{typeof(codomain(GtoOK))}()
    StoO.header = MapHeader(S, codomain(GtoOK), _image, _preimage)
  else
    StoO = MapUnitGrp{typeof(O)}()
    StoO.header = MapHeader(S, O, _image, _preimage)
  end
  StoO.OO_mod_F_mod_O_mod_F = HtoQ

  return S, StoO
end

function _picard_group(O::AbsSimpleNumFieldOrder)
  # We use the exact sequence
  # OK^\times \to \bigoplus_p OK_p^\times/O_p^\times \to Pic(O) \to Pic(OK) \to 1
  # and Algorithm 4.1.9 in Cohen: Advanced topics in computational number theory
  # to compute Pic(O).

  OK = maximal_order(nf(O))
  Cl, CltoOK = class_group(OK)
  U, UtoOK = unit_group(OK)
  G, GtoQ, OKtoQ = OO_mod_F_mod_O_mod_F(O)
  @assert is_snf(U) && is_snf(Cl) && is_snf(G)

  _assure_princ_gen(CltoOK)

  F = conductor(O, OK)
  FOK = extend(F, OK)

  # Collect the generators (they have to be coprime to F)
  gens_of_Cl = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  generators = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  Z = Vector{elem_type(G)}()
  for (I, g) in CltoOK.princ_gens
    II, _ = _coprime_integral_ideal_class(I, FOK)
    J1 = evaluate(II)
    @assert J1.den == 1
    J = numerator(J1)
    push!(gens_of_Cl, J)
    push!(generators, contract(J, O))
  end

  for i = 1:length(generators)
    I = generators[i]
    #The powering should happen in the maximal order.
    IOK = extend(I, OK)^Int(Cl.snf[i])
    a = principal_generator(IOK)
    push!(Z, GtoQ\(OKtoQ(a)))
  end

  append!(generators, [ contract(GtoQ(G[i]).elem*OK, O) for i = 1:ngens(G) ])

  # Build the relation matrix
  P = zero_matrix(FlintZZ, length(Z), ngens(G))
  for i = 1:length(Z)
    t = Z[i].coeff
    for j = 1:ngens(G)
      P[i, j] = t[1, j]
    end
  end

  UtoG = compose(UtoOK, compose(OKtoQ, pseudo_inv(GtoQ)))
  Q = zero_matrix(FlintZZ, ngens(U), ngens(G))
  for i = 1:ngens(U)
    t = UtoG(U[i]).coeff
    for j = 1:ngens(G)
      Q[i, j] = t[1, j]
    end
  end

  M = hcat(rels(Cl), -P)
  M = vcat(M, hcat(zero_matrix(FlintZZ, ngens(G), ngens(Cl)), rels(G)))
  M = vcat(M, hcat(zero_matrix(FlintZZ, nrows(Q), ngens(Cl)), Q))

  P = abelian_group(M)

  S, StoP = snf(P)

  gens_snf = typeof(generators)(undef, ngens(S))
  for i = 1:ngens(S)
    x = (StoP(S[i])).coeff
    for j = 1:ngens(P)
      x[1, j] = mod(x[1, j], S.snf[end])
    end
    y = O(1)*O
    for j = 1:ngens(P)
      y *= generators[j]^Int(x[1, j])
    end
    gens_snf[i] = y
  end

  # Build the map
  local disc_exp_picard_group
  let O = O, gens_snf = gens_snf
    function disc_exp_picard_group(x::FinGenAbGroupElem)
      y = ideal(O, 1)
      for i = 1:length(x.coeff)
        y *= gens_snf[i]^Int(x.coeff[1, i])
      end
      return y
    end
  end

  local disc_log_picard_group
  let P = P, F = F, O = O, OK = OK, CltoOK = CltoOK, gens_of_Cl = gens_of_Cl, OKtoQ = OKtoQ, GtoQ = GtoQ, StoP = StoP
    function disc_log_picard_group(x1::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      @assert order(x1) == O
      # x is only an element of the picard group if it is invertible.
      if !is_invertible(x1)[1]
        error("Ideal is not invertible")
      end
      if !isone(x1 + F)
        x1, _ = _coprime_integral_ideal_class(x1, F)
      end
      xOK = extend(x1, OK)
      c = CltoOK\xOK
      yOK = ideal(OK, 1)
      for i = 1:length(c.coeff)
        yOK *= gens_of_Cl[i]^Int(c.coeff[i])
      end
      y = contract(yOK, O)
      iy = inv(y) # y should be coprime to F
      z = x1*iy
      zOK = extend(z.num, OK)//z.den
      simplify(zOK)
      a1 = OKtoQ(principal_generator(zOK.num))
      a2 = OKtoQ(OK(zOK.den))
      b1, a = is_divisible(a1, a2)
      @assert b1
      @hassert :AbsNumFieldOrder 1 is_divisible(OKtoQ(OK(1)), a)[1]
      h = GtoQ\a
      p = FinGenAbGroupElem(P, hcat(c.coeff, h.coeff))
      b, s = has_preimage_with_preimage(StoP, p)
      @assert b
      return s
    end
  end
  Idl = IdealSet(O)
  StoIdl = MapPicardGrp{typeof(S), typeof(Idl)}()
  StoIdl.header = MapHeader(S, Idl, disc_exp_picard_group, disc_log_picard_group)
  StoIdl.OO_mod_F_mod_O_mod_F = GtoQ

  return S, StoIdl
end

################################################################################
#
#  Principal ideals
#
################################################################################

function _is_principal_non_maximal(I::Union{ AbsNumFieldOrderIdeal, AlgAssAbsOrdIdl })
  # Main inspiriation from a Magma implementation by Stefano Marseglia.
  # We use the exact sequence
  # 1 --> O^\times -(1)-> O_K^\times -(2)-> (O_K/F)^\times/(O/F)^\times
  #      -(3)-> Pic(O) -(4)-> Pic(O_K) --> 1
  # where F is the conductor of O in O_K.
  # See W. Bley, M. Endres "Picard groups and refined discrete logarithm", p. 4.
  # The idea is the following: Assume I + F = O and I*O_K = a*O_K for some a in O_K.
  # Then a is in (O_K/F)^\times and we can look for a preimage under the map (2).
  # If this does not exists, then the ideal is not in the kernel of map (3), so
  # not trivial in Pic(O), so not a principal ideal.
  # Otherwise let b in O_K^\times be such an preimage. Then c := a*b^{-1} is 1 in
  # (O_K/F)^\times/(O/F)^\times and hence an element of (O/F)^\times, so of O.
  # But I*O_K = c*O_K, as b is a unit of O_K, so I = c*O.
  O = order(I)
  if I isa AlgAssAbsOrdIdl
    @assert is_one(denominator(I, O))
  end
  if !is_invertible(I)[1]
    return false, O()
  end
  K = _algebra(O)
  OK = maximal_order(O)
  F = conductor(O, OK)
  if !isone(I + F)
    J, z = _coprime_integral_ideal_class(I, F)
  else
    J = I
    z = one(K)
  end
  JOK = J*OK
  b, x = is_principal_fac_elem(JOK)
  if !b
    return false, O()
  end

  x = evaluate(x)
  if x in O && ideal(O, O(x)) == J
    y = O(x*inv(z))
    return true, y
  end

  _, m = unit_group(O)
  # We do not really need the unit group, but only m.OO_mod_F_mod_O_mod_F.
  # If we compute the unit group then this map is cached for the next time.
  # (And computing the unit group is only little more work).
  GtoQ = m.OO_mod_F_mod_O_mod_F
  G = domain(GtoQ)
  if order(G) == 1
    y = O(x*inv(z))
    return true, y
  end

  Q = codomain(GtoQ)
  OKtoQ = AbsOrdQuoMap(OK, Q)
  U, mU = unit_group(OK)
  h = hom(U, G, [ GtoQ\(OKtoQ(mU(U[i]))) for i = 1:ngens(U) ])
  b, u = has_preimage_with_preimage(h, GtoQ\(OKtoQ(OK(x))))
  if !b
    return false, O()
  end
  _K, _mK = kernel(h, false)

  _, toQ = quo(U, _mK, false)
  u = toQ\(toQ(u)) # Reduce the coefficient size (hopefully)
  y = O(x*inv(_elem_in_algebra(mU(u), copy = false))*inv(z))
  return true, y
end
