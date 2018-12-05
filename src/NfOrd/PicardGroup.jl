export picard_group

################################################################################
#
#  High level functions
#
################################################################################

@doc Markdown.doc"""
      picard_group(O::NfOrd) -> GrpAbFinGen, MapClassGrp

> Returns the Picard group of O and a map from the group in the set of
> (invertible) ideals of O.
"""
function picard_group(O::NfOrd)
  try
    mP = _get_picard_group(O)
    return domain(mP), mP
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
    OK = maximal_order(nf(O)) # We need it later anyway
    if O == OK
      return class_group(OK)
    end
    P, mP = _picard_group(O)
    _set_picard_group(O, mP)
    return P, mP
  end
end

function unit_group_non_maximal(O::NfOrd)
  try
    mU = _get_unit_group_non_maximal(O)
    return domain(mU), mU
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
    U, mU = _unit_group_non_maximal(O)
    _set_unit_group_non_maximal(O, mU)
    return U, mU
  end
end

################################################################################
#
#  Internals
#
################################################################################

# Computes \bigoplus_p OK_p^\times/O_p^\times where the sum runs over all prime
# ideals p containing the conductor of O and OK is the maximal order.
# Algorithm 8.1 in Klueners, Pauli: Computing residue class rings and Picard
# groups of orders
function _direct_sum_of_localizations(O::NfOrd)
  OK = maximal_order(nf(O))
  F = conductor(O, OK)
  FOK = extend(F, OK)
  QF, OKtoQF = quo(OK, FOK)

  fac = factor(QF)
  D = Dict{NfOrdIdl, Vector{Int}}() # keys are ideals p of O, values the indices of the ideals q in OK such that contract(q, O) == p.
  i = 1
  factors_of_FOK = Vector{NfOrdIdl}(undef, length(fac)) # ideals of OK
  for (q, e) in fac
    p = contract(q, O)
    p.is_prime = q.is_prime
    get!(D, p, Int[])
    append!(D[p], i)
    factors_of_FOK[i] = q^e
    i += 1
  end

  groups = Vector{GrpAbFinGen}()
  maps = Vector{GrpAbFinGenToAbsOrdQuoRingMultMap}()
  for p in keys(D)
    # Find m such that p^m*O_p \subseteq F*O_p
    m = 0
    prime_ideals_over_p = Vector{Tuple{NfOrdIdl, Int}}() # ideals of OK
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
    groups2 = Vector{GrpAbFinGen}(undef, length(prime_ideals_over_p))
    maps2 = Vector{GrpAbFinGenToAbsOrdQuoRingMultMap}(undef, length(prime_ideals_over_p))
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

    gens = map(x -> GtoQ\(OKtoQ(OK(x.elem))), mGG.generators)
    H, GtoH = quo(G, gens)
    @assert GtoH.map == identity_matrix(FlintZZ, ngens(G))
    HtoQ = GrpAbFinGenToAbsOrdQuoRingMultMap(H, Q, GtoQ.generators, GtoQ.discrete_logarithm)
    push!(groups, H)
    push!(maps, HtoQ)
  end

  G, GtoQ = direct_product(groups, maps, QF)

  S, StoG, StoQ = snf(G, GtoQ)
  return S, StoQ, OKtoQF
end

function _unit_group_non_maximal(O::NfOrd)
  OK = maximal_order(nf(O))
  G, GtoOK = unit_group(OK)
  H, HtoQ, OKtoQ = _direct_sum_of_localizations(O)

  # The unit group of O is the kernel of a map from G to H
  # (we really want a GrpAbFinGenMap, so we can't use compose to build this map)
  M = zero_matrix(FlintZZ, ngens(G), ngens(H))
  for i = 1:ngens(G)
    q = OKtoQ(GtoOK(G[i]))
    h = HtoQ\q
    for j = 1:ngens(H)
      M[i, j] = h.coeff[1, j]
    end
  end
  GtoH = hom(G, H, M, false)

  K, KtoG = kernel(GtoH)
  S, StoK = snf(K)
  StoG = compose(StoK, KtoG)

  # Build the map from S to O
  function _image(x::GrpAbFinGenElem)
    y = GtoOK(StoG(x))
    return O(elem_in_nf(y))
  end

  function _preimage(x::NfOrdElem)
    y = OK(elem_in_nf(x))
    g = GtoOK\y
    b, k = haspreimage(KtoG, g)
    @assert b
    b, s = haspreimage(StoK, k)
    @assert b
    return s
  end

  StoO = MapUnitGrp{typeof(S), typeof(O)}()
  StoO.header = MapHeader(S, O, _image, _preimage)

  return S, StoO
end

function _picard_group(O::NfOrd)
  # We use the exact sequence
  # OK^\times \to \bigoplus_p OK_p^\times/O_p^\times \to Pic(O) \to Pic(OK) \to 1
  # and Algorithm 4.1.9 in Cohen: Advanced topics in computational number theory
  # to compute Pic(O).

  OK = maximal_order(nf(O))
  U, UtoOK = unit_group(OK)
  Cl, CltoOK = class_group(OK)
  G, GtoQ, OKtoQ = _direct_sum_of_localizations(O)
  @assert issnf(U) && issnf(Cl) && issnf(G)

  _assure_princ_gen(CltoOK)

  F = conductor(O, OK)
  FOK = extend(F, OK)

  # Collect the generators (they have to be coprime to F)
  gens_of_Cl = Vector{NfOrdIdl}()
  generators = Vector{NfOrdIdl}()
  Z = Vector{elem_type(G)}()
  for (I, g) in CltoOK.princ_gens
    II, _ = _coprime_integral_ideal_class(I, FOK)
    J = evaluate(II)
    @assert J.den == 1
    J = numerator(J)
    push!(gens_of_Cl, J)
    push!(generators, contract(J, O))
  end

  for i = 1:length(generators)
    I = generators[i]^Int(Cl.snf[i])
    IOK = extend(I, OK)
    a = principal_gen(IOK)
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

  UtoG = compose(UtoOK, compose(OKtoQ, inv(GtoQ)))
  Q = zero_matrix(FlintZZ, ngens(U), ngens(G))
  for i = 1:ngens(U)
    t = UtoG(U[i]).coeff
    for j = 1:ngens(G)
      Q[i, j] = t[1, j]
    end
  end

  M = hcat(rels(Cl), -P)
  M = vcat(M, hcat(zero_matrix(FlintZZ, ngens(G), ngens(Cl)), rels(G)))
  M = vcat(M, hcat(zero_matrix(FlintZZ, rows(Q), ngens(Cl)), Q))

  P = AbelianGroup(M)

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
  function disc_exp_picard_group(x::GrpAbFinGenElem)
    y = O(1)*O
    for i = 1:length(x.coeff)
      y *= gens_snf[i]^Int(x.coeff[1, i])
    end
    return y
  end

  function disc_log_picard_group(x::NfOrdIdl)
    @assert order(x) == O
    # x is only an element of the picard group if it is invertible.
    if !isinvertible(x)[1]
      error("Ideal is not invertible")
    end
    if !isone(x + F)
      x, _ = _coprime_integral_ideal_class(x, F)
    end
    xOK = extend(x, OK)
    c = CltoOK\xOK
    yOK = gens_of_Cl[1]^Int(c.coeff[1])
    for i = 2:length(c.coeff)
      yOK *= gens_of_Cl[i]^Int(c.coeff[i])
    end
    y = contract(yOK, O)
    iy = inv(y) # y should be coprime to F
    z = x*iy
    zOK = extend(z.num, OK)//z.den
    simplify(zOK)
    a1 = OKtoQ(principal_gen(zOK.num))
    a2 = OKtoQ(OK(zOK.den))
    b1, a = isdivisible(a1, a2)
    @assert b1
    b2, _ = isdivisible(OKtoQ(OK(1)), a)
    @assert b2
    h = GtoQ\a
    p = P(hcat(c.coeff, h.coeff))
    b, s = haspreimage(StoP, p)
    @assert b
    return s
  end

  StoIdl = MapClassGrp{typeof(S)}() # Technically, it is a MapPicardGrp...
  StoIdl.header = MapHeader(S, IdealSet(O), disc_exp_picard_group, disc_log_picard_group)

  return S, StoIdl
end
