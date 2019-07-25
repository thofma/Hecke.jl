export principal_gen, kernel_group

################################################################################
#
#  Map Types
#
################################################################################

mutable struct MapRayClassGroupAlg{S, T} <: Map{S, T, HeckeMap, MapRayClassGroupAlg}
  header::MapHeader{S, T}
  modulus#::AlgAssAbsOrdIdl{...}
  groups_in_number_fields::Vector{Tuple{S, MapRayClassGrp}}
  into_product_of_groups::GrpAbFinGenMap # the isomorphism between the domain and the product of the groups in groups_in_number_fields

  function MapRayClassGroupAlg{S, T}() where {S, T}
    return new{S, T}()
  end
end

mutable struct MapPicardGrp{S, T} <: Map{S, T, HeckeMap, MapPicardGrp}
  header::MapHeader{S, T}

  # For the refined discrete logarithm:
  right_transform::fmpz_mat
  betas # Vector of factorized algebra elements
  gammas # the same type as betas
  ray_class_group_map::MapRayClassGroupAlg

  function MapPicardGrp{S, T}() where {S, T}
    return new{S, T}()
  end
end

################################################################################
#
#  Picard group
#
################################################################################

@doc Markdown.doc"""
    picard_group(O::AlgAssAbsOrd, prepare_ref_disc_log::Bool = false)
      -> GrpAbFinGen, MapPicardGroup

> Given an order $O$ in a commutative algebra over $\mathbb Q$, this function
> returns the picard group of $O$.
> If `prepare_ref_disc_log` is `true`, then (possibly expensive) preparations
> for the computation of refined discrete logarithms in non maximal orders are done.
"""
function picard_group(O::AlgAssAbsOrd, prepare_ref_disc_log::Bool = false)
  if !prepare_ref_disc_log && isdefined(O, :picard_group)
    return domain(O.picard_group), O.picard_group
  end

  OO = maximal_order(algebra(O)) # We need it later anyway
  if O == OO
    return _picard_group_maximal(OO)
  end

  if prepare_ref_disc_log && isdefined(O, :picard_group)
    mP = O.picard_group
    if isdefined(mP, :betas) && isdefined(mP, :gammas) && isdefined(mP, :right_transform)
      return domain(mP), mP
    end
  end
  return _picard_group_non_maximal(O, prepare_ref_disc_log)
end

function _picard_group_maximal(O::AlgAssAbsOrd)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)
  class_groups = [ class_group(field) for (field, map) in fields_and_maps ]
  P = class_groups[1][1]
  for i = 2:length(class_groups)
    P = direct_product(P, class_groups[i][1])[1]
  end
  S, StoP = snf(P)

  function disc_exp(x::GrpAbFinGenElem)
    p = StoP(x)
    basis_of_ideal = Vector{elem_type(O)}()
    offset = 1
    for i = 1:length(fields_and_maps)
      K, AtoK = fields_and_maps[i]
      C, CtoIdl = class_groups[i]
      c = C(sub(p.coeff, 1:1, offset:(offset + ngens(C) - 1)))
      I = CtoIdl(c)
      for b in basis(I)
        push!(basis_of_ideal, O(AtoK\K(b)))
      end
      offset += ngens(C)
    end
    I = ideal_from_z_gens(O, basis_of_ideal)
    return I
  end

  function disc_log(x::AlgAssAbsOrdIdl)
    ideals = Vector{NfOrdIdl}()
    for i = 1:length(fields_and_maps)
      push!(ideals, _as_ideal_of_number_field(x, fields_and_maps[i][2]))
    end

    p = zero_matrix(FlintZZ, 1, 0)
    for i = 1:length(ideals)
      C, CtoIdl = class_groups[i]
      c = CtoIdl\ideals[i]
      p = hcat(p, c.coeff)
    end
    return StoP\P(p)
  end

  Idl = IdealSet(O)
  StoIdl = MapPicardGrp{typeof(S), typeof(Idl)}()
  StoIdl.header = MapHeader(S, Idl, disc_exp, disc_log)
  O.picard_group = StoIdl
  return S, StoIdl
end

# See Bley, Endres "Picard Groups and Refined Discrete Logarithms".
function _picard_group_non_maximal(O::AlgAssAbsOrd, prepare_ref_disc_log::Bool = false)
  A = algebra(O)
  OO = maximal_order(A)

  F = conductor(O, OO, :left)
  FOO = extend(F, OO)

  # We want to use the exact sequence
  # (O/F)^\times \to C_FOO(OO) \to Pic(O) \to 0.
  # where C_FOO(OO) is the ray class group of modulo FOO.

  # Firstly, we compute the groups.
  R, mR = ray_class_group(FOO)
  @assert issnf(R)

  Idl = IdealSet(O)
  fac_elem_mon_A = FacElemMon(A)
  if ngens(R) == 0
    function disc_exp_triv(x::GrpAbFinGenElem)
      return ideal(O, one(O))
    end

    function disc_log_triv(x::AlgAssAbsOrdIdl)
      return R()
    end

    RtoIdl = MapPicardGrp{typeof(R), typeof(Idl)}()
    RtoIdl.header = MapHeader(R, Idl, disc_exp_triv, disc_log_triv)
    RtoIdl.right_transform = zero_matrix(FlintZZ, 0, 0)
    RtoIdl.betas = Vector{elem_type(fac_elem_mon_A)}()
    RtoIdl.gammas = Vector{elem_type(fac_elem_mon_A)}()
    RtoIdl.ray_class_group_map = mR
    O.picard_group = RtoIdl
    return R, RtoIdl
  end

  Q, OtoQ = quo(O, F)
  G, GtoQ = multiplicative_group(Q)

  if !prepare_ref_disc_log
    # If we don't need to compute refined discrete logarithms, we compute the
    # picard group as the quotient of groups.

    # Compute the image of the map from G to R, i. e. the kernel of the map from
    # R to Pic(O).
    GinR = Vector{GrpAbFinGenElem}()
    for i = 1:ngens(G)
      g = OO(OtoQ\(GtoQ(G[i])))
      r = mR\(ideal(OO, g))
      push!(GinR, r)
    end

    # Compute the Picard group
    P, RtoP = quo(R, GinR)
    S, StoP = snf(P)

    StoR = compose(StoP, pseudo_inv(RtoP))

    gens_snf = Vector{ideal_type(O)}(undef, ngens(S))
    for i = 1:ngens(S)
      r = RtoP\StoP(S[i])
      # Contraction does not commute with multiplication, so we have to evaluate.
      # TODO: Can we make this work?
      gens_snf[i] = contract(evaluate(mR(r)), O)
    end

  else
    # This is now Algorithm 3.3 in the Bley-Endres-paper.

    # Let [r_1,...,r_n] in R. Then mR([r_1,...,r_n]) is in general not equal to
    # prod_i mR(R[i])^r_i but just something equivalent. In the following, we
    # need this latter "discrete exponentiation". Therefore we collect the
    # generators here and don't use mR later.
    fac_elem_mon_idl_OO = FacElemMon(IdealSet(OO))
    gens_of_R = Vector{elem_type(fac_elem_mon_idl_OO)}()
    for i = 1:ngens(R)
      push!(gens_of_R, mR(R[i]))
    end

    # Compute the relations of the generators of G in R
    gens_of_G = Vector{elem_type(fac_elem_mon_A)}()
    D = zero_matrix(FlintZZ, ngens(R) + ngens(G), ngens(R))
    for i = 1:ngens(R)
      D[i, i] = R.snf[i]
    end
    for i = (ngens(R) + 1):(ngens(R) + ngens(G))
      g = OO(OtoQ\(GtoQ(G[i - ngens(R)])))
      gOO = ideal(OO, g)
      a, r = disc_log_generalized_ray_class_grp(gOO, mR)

      # Now we have gOO = a*mR(r), but we need gOO = c*gOO2
      gOO2 = fac_elem_mon_idl_OO()
      for j = 1:ngens(R)
        gOO2 *= gens_of_R[j]^r[j]
      end
      b, s = disc_log_generalized_ray_class_grp(gOO2, mR)
      @assert r == s
      c = a*inv(b)

      for j = 1:ngens(R)
        D[i, j] = r[j]
      end
      push!(gens_of_G, elem_in_algebra(g, copy = false)*inv(c))
    end

    # D is the relation matrix of the picard group
    H, W = hnf_with_transform(D)
    H = sub(H, 1:ngens(R), 1:ngens(R))

    S_rels, U, V = snf_with_transform(H)
    Vi = inv(V)

    # In principle S_rels is the SNF of GrpAbFinGen(H), but we can as well use R
    # here, since the transformation for the HNF is from the left.
    S, StoR = _reduce_snf(R, S_rels, V, Vi)

    # We need to change Vi, since we want integral generators.
    Q = similar(V) # Not exactly the same Q as in the Bley-Endres-paper
    C = deepcopy(Vi) # Will be Vi + Q*R.rels, we can't change Vi in place, since it is also part of StoR
    for i = 1:nrows(C)
      for j = 1:ncols(C)
        if C[i, j] >= 0
          continue
        end

        Q[i, j] = div(-C[i, j], R.snf[j]) + 1
        C[i, j] = addeq!(C[i, j], R.snf[j]*Q[i, j])
      end
    end

    # Compute the generators
    generators_in_OO = Vector{elem_type(fac_elem_mon_idl_OO)}()
    gens_snf = Vector{ideal_type(O)}()
    for i = 1:nrows(C)
      I = fac_elem_mon_idl_OO()
      for j = 1:ncols(C)
        I *= gens_of_R[j]^C[i, j]
      end
      push!(generators_in_OO, I)

      if !isone(S_rels[i, i])
        # Contraction does not commute with multiplication, so we have to evaluate.
        push!(gens_snf, contract(evaluate(I), O))
      end
    end
    @assert length(gens_snf) == ngens(S)

    # Compute the additional data needed for the refined discrete logarithm.
    princ_gens_ray = Vector{elem_type(fac_elem_mon_A)}()
    for i = 1:ngens(R)
      b, a = has_principal_gen_1_mod_m(gens_of_R[i]^R.snf[i], FOO)
      @assert b
      push!(princ_gens_ray, a)
    end

    gammas = Vector{elem_type(fac_elem_mon_A)}()
    for i = 1:ngens(R)
      g = fac_elem_mon_A()
      for j = 1:ngens(R)
        g *= princ_gens_ray[j]^Q[i, j]
      end
      push!(gammas, g)
    end

    # In principle this should be
    # (U | 0)       (* | *)
    # (-----) * W = (-----)
    # (0 | 0)       (0 | 0).
    # We don't do the multiplications with zero.
    UW = U*sub(W, 1:ngens(R), 1:ncols(W))

    betas = Vector{elem_type(fac_elem_mon_A)}()
    for i = 1:nrows(UW)
      t = fac_elem_mon_A()
      for j = 1:ngens(R)
        t *= princ_gens_ray[j]^UW[i, j]
      end
      for j = 1:ngens(G)
        t *= gens_of_G[j]^UW[i, j + ngens(R)]
      end
      if i <= length(gammas)
        t *= gammas[i]^S_rels[i, i]
      end
      push!(betas, t)
    end
  end

  function disc_exp(x::GrpAbFinGenElem)
    y = one(Idl)
    for i = 1:length(x.coeff)
      y *= gens_snf[i]^x[i]
    end
    return y
  end

  function disc_log(x::AlgAssAbsOrdIdl)
    if !isinvertible(x)[1]
      error("Ideal is not invertible")
    end
    if !isone(x + F)
      x, _ = _coprime_integral_ideal_class(x, F)
    end

    xOO = extend(x, OO)
    r = mR\xOO
    return StoR\r
  end

  StoIdl = MapPicardGrp{typeof(S), typeof(Idl)}()
  StoIdl.header = MapHeader(S, Idl, disc_exp, disc_log)
  StoIdl.ray_class_group_map = mR
  if prepare_ref_disc_log
    StoIdl.right_transform = V
    StoIdl.betas = betas
    StoIdl.gammas = gammas
  end
  O.picard_group = StoIdl
  return S, StoIdl
end

# Algorithm 3.5 in Bley, Endres "Picard groups and refined discrete logarithms"
function refined_disc_log_picard_group(a::AlgAssAbsOrdIdl, mP::MapPicardGrp)
  if !isdefined(mP, :betas) || !isdefined(mP, :gammas) || !isdefined(mP, :right_transform)
    # I don't want to recompute the group here, because the user gave me the map.
    error("Data for the refined discrete logarithm is not available.")
  end

  if !isinvertible(a)[1]
    error("Ideal is not invertible")
  end

  O = order(a)
  A = algebra(O)
  OO = maximal_order(A)
  F = conductor(O, OO, :left)
  FOO = F*OO
  aOO = a*OO

  t = one(A)
  if !isone(a + F)
    # After this modification of a we do not need steps 1 to 4 of the algorithm
    a, t = _coprime_integral_ideal_class(a, F)
    aOO = a*OO
  end

  # Compute the refined disc log of aOO in the ray class group
  mR = mP.ray_class_group_map
  R = domain(mR)

  k1, r = disc_log_generalized_ray_class_grp(aOO, mR)
  aOO2 = FacElemMon(IdealSet(OO))()
  for i = 1:ngens(R)
    # We need this kind of discrete exponentiation
    aOO2 *= mR(R[i])^r[i]
  end

  k2, s = disc_log_generalized_ray_class_grp(aOO2, mR)
  @assert r == s
  k = k1*inv(k2)

  # Map r into the picard group
  rV = r.coeff*mP.right_transform

  P = domain(mP)
  rr = Vector{fmpz}(undef, ngens(R))
  num1 = ngens(R) - ngens(P) # the number of ones in the SNF of P
  for i = 1:num1
    rr[i] = rV[1, i]
  end

  p = Vector{fmpz}(undef, ngens(P))
  for i = 1:ngens(P)
    inum1 = i + num1
    q, r = divrem(rV[inum1], P.snf[i])

    # We need positive remainder
    if r < 0
      r += P.snf[i]
      q -= 1
    end
    rr[inum1] = q
    p[i] = r
  end

  beta = one(A)
  gamma = one(A)
  for i = 1:ngens(R)
    beta *= mP.betas[i]^rr[i]
    gamma *= mP.gammas[i]^rV[i]
  end

  return k*beta*inv(t*gamma), P(p)
end

@doc Markdown.doc"""
    principal_gen(a::AlgAssAbsOrdIdl) -> AlgAssAbsOrdElem

> Given an principal ideal $a$ in an order $O$ in a commutative algebra over
> $\mathbb Q$, this function returns a principal generator of $a$.
"""
function principal_gen(a::AlgAssAbsOrdIdl)
  g = principal_gen_fac_elem(a)
  return order(a)(evaluate(g))
end

function principal_gen_fac_elem(a::AlgAssAbsOrdIdl)
  a, g = isprincipal_fac_elem(a)
  if !a
    error("Ideal is not principal")
  end
  return g
end

function isprincipal_fac_elem(a::AlgAssAbsOrdIdl)
  O = order(a)
  if O.ismaximal == 1
    return isprincipal_maximal_fac_elem(a)
  end

  OO = maximal_order(algebra(O))
  if O == OO
    return isprincipal_maximal_fac_elem(a)
  end

  return isprincipal_non_maximal_fac_elem(a)
end

function isprincipal_non_maximal_fac_elem(a::AlgAssAbsOrdIdl)
  P, mP = picard_group(order(a), true)

  g, r = refined_disc_log_picard_group(a, mP)
  return iszero(r), g
end

function isprincipal_maximal_fac_elem(a::AlgAssAbsOrdIdl)
  O = order(a)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)

  idems = [ AtoK\one(K) for (K, AtoK) in fields_and_maps ]
  sum_idems = sum(idems)
  minus_idems = [ -one(A)*idem for idem in idems ]
  bases = Vector{elem_type(A)}()
  exps = Vector{fmpz}()
  for i = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[i]
    C, mC = class_group(K) # should be cached
    Hecke._assure_princ_gen(mC)
    ai = _as_ideal_of_number_field(a, AtoK)
    c, g = isprincipal_fac_elem(ai)
    if !c
      return false, FacElemMon(A)()
    end
    for (b, e) in g
      t = AtoK\b
      t = add!(t, t, sum_idems)
      t = add!(t, t, minus_idems[i])
      push!(bases, t)
      push!(exps, e)
    end
  end
  return true, FacElem(bases, exps)
end

################################################################################
#
#  Ray Class Group
#
################################################################################

# inf_pcl[i] may contain places for the field A.maps_to_numberfields[i][1]
function ray_class_group(m::AlgAssAbsOrdIdl, inf_plc::Vector{Vector{InfPlc}} = Vector{Vector{InfPlc}}())
  O = order(m)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)

  # Compute the groups in the number fields
  groups = Vector{Tuple{GrpAbFinGen, MapRayClassGrp}}()
  for i = 1:length(fields_and_maps)
    mi = _as_ideal_of_number_field(m, fields_and_maps[i][2])
    if length(inf_plc) != 0
      r, mr = ray_class_group(mi, inf_plc[i])
    else
      r, mr = ray_class_group(mi)
    end
    push!(groups, _make_disc_exp_deterministic(mr))
    #push!(groups, ray_class_group(mi))
  end

  C = groups[1][1]
  for i = 2:length(groups)
    C = direct_product(C, groups[i][1])[1]
  end
  S, StoC = snf(C)

  one_ideals = _lift_one_ideals(O)
  fac_elem_mon = FacElemMon(parent(m))

  function disc_exp(x::GrpAbFinGenElem)
    z = StoC(x).coeff
    y = fac_elem_mon()
    j = 1
    for k = 1:length(groups)
      G, GtoIdl = groups[k]
      zz = sub(z, 1:1, j:(j + ngens(G) - 1))
      Ifac = GtoIdl(G(zz))
      y *= _as_ideal_of_algebra(Ifac, k, O, one_ideals)
      j += ngens(G)
    end
    return y
  end

  function disc_log(x::AlgAssAbsOrdIdl)
    ideals = Vector{NfOrdIdl}()
    for i = 1:length(fields_and_maps)
      push!(ideals, _as_ideal_of_number_field(x, fields_and_maps[i][2]))
    end

    c = zero_matrix(FlintZZ, 1, 0)
    for i = 1:length(ideals)
      G, GtoIdl = groups[i]
      g = GtoIdl\ideals[i]
      c = hcat(c, g.coeff)
    end
    return StoC\C(c)
  end

  function disc_log(x::FacElem)
    ideals = Vector{FacElem}()
    for i = 1:length(fields_and_maps)
      base = Vector{NfOrdIdl}()
      exp = Vector{fmpz}()
      for (I, e) in x
        push!(base, _as_ideal_of_number_field(I, fields_and_maps[i][2]))
        push!(exp, e)
      end
      push!(ideals, FacElem(base, exp))
    end

    c = zero_matrix(FlintZZ, 1, 0)
    for i = 1:length(ideals)
      G, GtoIdl = groups[i]
      g = GtoIdl\ideals[i]
      c = hcat(c, g.coeff)
    end
    return StoC\C(c)
  end

  StoIdl = MapRayClassGroupAlg{typeof(S), typeof(fac_elem_mon)}()
  StoIdl.header = MapHeader(S, fac_elem_mon, disc_exp, disc_log)
  StoIdl.modulus = m
  StoIdl.groups_in_number_fields = groups
  StoIdl.into_product_of_groups = StoC
  return S, StoIdl
end

# A simple way to make the discrete exponentiation in the ray class group (for
# number fields) deterministic.
function _make_disc_exp_deterministic(mR::MapRayClassGrp)
  R = domain(mR)
  S, StoR = snf(R)

  fac_elem_mon = codomain(mR)
  generators = Vector{elem_type(fac_elem_mon)}()
  for i = 1:ngens(S)
    r = StoR(S[i])
    push!(generators, mR(r))
  end

  function disc_exp(x::GrpAbFinGenElem)
    y = fac_elem_mon()
    for i = 1:ngens(parent(x))
      y *= generators[i]^x[i]
    end
    return y
  end

  function disc_log(x::FacElem)
    return StoR\(mR\x)
  end

  function disc_log(x::NfAbsOrdIdl)
    return StoR\(mR\x)
  end

  mRR = MapRayClassGrp()
  mRR.header = MapHeader(S, fac_elem_mon, disc_exp, disc_log)
  for x in fieldnames(typeof(mR))
    if x != :header && isdefined(mR, x)
      setfield!(mRR, x, getfield(mR, x))
    end
  end
  return S, mRR
end

function has_principal_gen_1_mod_m(I::Union{ AlgAssAbsOrdIdl, FacElem{ <: AlgAssAbsOrdIdl, <: AlgAssAbsOrdIdlSet} }, m::AlgAssAbsOrdIdl)
  O = order(m)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)

  idems = [ AtoK\one(K) for (K, AtoK) in fields_and_maps ]
  sum_idems = sum(idems)
  minus_idems = [ -one(A)*idem for idem in idems ]
  bases = Vector{elem_type(A)}()
  exps = Vector{fmpz}()
  for i = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[i]
    mi = _as_ideal_of_number_field(m, AtoK)
    Ii = _as_ideal_of_number_field(I, AtoK)
    a, g = has_principal_gen_1_mod_m(Ii, mi)
    if !a
      return false, FacElem(base, exps)
    end
    for (b, e) in g
      t = AtoK\b
      t = add!(t, t, sum_idems)
      t = add!(t, t, minus_idems[i])
      push!(bases, t)
      push!(exps, e)
    end
  end
  return true, FacElem(bases, exps)
end

function disc_log_generalized_ray_class_grp(I::Union{ S, FacElem{S, T} }, mR::MapRayClassGroupAlg) where { S <: AlgAssAbsOrdIdl, T <: AlgAssAbsOrdIdlSet }
  m = mR.modulus
  O = order(m)
  A = algebra(O)

  if I isa FacElem && isempty(I)
    return FacElemMon(A)(), domain(mR)()
  end

  fields_and_maps = as_number_fields(A)

  groups = mR.groups_in_number_fields

  if I isa AlgAssAbsOrdIdl
    ideals = Vector{NfOrdIdl}()
  else
    ideals = Vector{FacElem{NfOrdIdl, NfOrdIdlSet}}()
  end
  for i = 1:length(fields_and_maps)
    push!(ideals, _as_ideal_of_number_field(I, fields_and_maps[i][2]))
  end

  idems = [ AtoK\one(K) for (K, AtoK) in fields_and_maps ]
  sum_idems = sum(idems)
  minus_idems = [ -one(A)*idem for idem in idems ]
  bases = Vector{elem_type(A)}()
  exps = Vector{fmpz}()
  p = zero_matrix(FlintZZ, 1, 0)
  ideal_gens = Vector{elem_type(O)}()
  for i = 1:length(ideals)
    K, AtoK = fields_and_maps[i]
    d, lI = disc_log_generalized_ray_class_grp(ideals[i], groups[i][2])
    p = hcat(p, matrix(FlintZZ, 1, length(lI), [ lI[i][2] for i = 1:length(lI) ]))
    for (b, e) in d
      t = AtoK\b
      t = add!(t, t, sum_idems)
      t = add!(t, t, minus_idems[i])
      push!(bases, t)
      push!(exps, e)
    end
  end
  RtoP = mR.into_product_of_groups
  P = codomain(RtoP)
  r = RtoP\P(p)

  return FacElem(bases, exps), r
end

################################################################################
#
#  Kernel group
#
################################################################################

@doc Markdown.doc"""
    kernel_group(O::AlgAssAbsOrd) -> GrpAbFinGen, MapPicardGroup

> Given an order $O$ in a commutative algebra over $\mathbb Q$, this function
> returns the group $D$ in the exact sequence $0 \to D \to Pic(O) \to Pic(O')$
> where $O'$ is a maximal order containing $O$.
"""
function kernel_group(O::AlgAssAbsOrd)
  A = algebra(O)
  OO = maximal_order(A)

  # We use the short exact sequence
  # 0 \to D(O) \to Pic(O) \to Pic(OO) \to 0,
  # where D(O) is the kernel group of O.

  P, mP = picard_group(O)
  C, mC = picard_group(OO)

  Idl = IdealSet(O)
  if C == P
    D = GrpAbFinGen(fmpz[])
    function disc_exp_triv(x::GrpAbFinGenElem)
      return ideal(O, one(O))
    end

    function disc_log_triv(x::AlgAssAbsOrdIdl)
      return D()
    end

    DtoIdl = MapPicardGrp{typeof(D), typeof(Idl)}()
    DtoIdl.header = MapHeader(D, Idl, disc_exp_triv, disc_log_triv)
    return D, DtoIdl
  end

  # Build the morphism from Pic(O) to Pic(OO)
  A = Vector{GrpAbFinGenElem}()
  B = Vector{GrpAbFinGenElem}()
  for i = 1:ngens(P)
    push!(A, P[i])
    p = mP(P[i])
    pOO = extend(p, OO)
    c = mC\pOO
    push!(B, c)
  end

  PtoC = hom(A, B)

  # The kernel group is the kernel of this morphism
  D, DtoP = kernel(PtoC)
  S, StoD = snf(D)

  gens_snf = Vector{elem_type(Idl)}()
  for i = 1:ngens(S)
    p = DtoP(StoD(S[i]))
    push!(gens_snf, mP(p))
  end

  function disc_exp(x::GrpAbFinGenElem)
    y = one(Idl)
    for i = 1:length(x.coeff)
      y *= gens_snf[i]^x.coeff[1, i]
    end
    return y
  end

  function disc_log(x::AlgAssAbsOrdIdl)
    p = mP\x
    b, g = haspreimage(DtoP, p)
    @assert b "Ideal not an element of the kernel group"
    return StoD\g
  end

  StoIdl = MapPicardGrp{typeof(S), typeof(Idl)}()
  StoIdl.header = MapHeader(S, Idl, disc_exp, disc_log)
  return S, StoIdl
end

################################################################################
#
#  Coprime representatives
#
################################################################################

# Mostly taken from NfOrd/LinearAlgebra.jl
function _coprime_integral_ideal_class(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl)
  O = order(b)
  a_inv = inv(a)
  c = ideal(O, one(O))
  x = algebra(O)()
  check = true
  while check
    x = rand(a_inv, 100)
    c = x*a
    c = simplify!(c)
    @assert denominator(c, copy = false) == 1
    isone(numerator(c, copy = false) + b) ? (check = false) : (check = true)
  end
  return numerator(c, copy = false), x
end
