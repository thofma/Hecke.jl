################################################################################
#
#  Map Types
#
################################################################################

mutable struct MapRayClassGroupAlg{S, T} <: Map{S, T, HeckeMap, MapRayClassGroupAlg}
  header::MapHeader{S, T}
  modulus#::AlgAssAbsOrdIdl{...}
  groups_in_number_fields::Vector{Tuple{S, MapRayClassGrp}}
  into_product_of_groups::FinGenAbGroupHom # the isomorphism between the domain and the product of the groups in groups_in_number_fields

  function MapRayClassGroupAlg{S, T}() where {S, T}
    return new{S, T}()
  end
end

function modulus(f::MapRayClassGroupAlg{S, T}) where {S, T}
  return f.modulus::elem_type(base_ring_type(T))
end

base_ring_type(::Type{FacElemMon{S}}) where {S} = S

mutable struct MapPicardGrp{S, T} <: Map{S, T, HeckeMap, MapPicardGrp}
  header::MapHeader{S, T}

  # Only used for picard groups of orders in number fields
  OO_mod_F_mod_O_mod_F::GrpAbFinGenToAbsOrdQuoRingMultMap

  # For the refined discrete logarithm: (only used for picard groups of orders in algebras)
  right_transform::ZZMatrix
  betas # Vector of factorized algebra elements
  gammas # the same type as betas
  ray_class_group_map::MapRayClassGroupAlg{S, FacElemMon{T}}

  function MapPicardGrp{S, T}() where {S, T}
    return new{S, T}()
  end
end

function show(io::IO, mP::MapPicardGrp)
  @show_name(io, mP)
  println(io, "Picard Group map of ")
  show(IOContext(io, :compact => true), codomain(mP))
end

################################################################################
#
#  Picard group
#
################################################################################

@doc raw"""
    picard_group(O::AlgAssAbsOrd, prepare_ref_disc_log::Bool = false)
      -> FinGenAbGroup, MapPicardGroup

Given an order $O$ in a commutative algebra over $\mathbb Q$, this function
returns the picard group of $O$.
If `prepare_ref_disc_log` is `true`, then (possibly expensive) preparations
for the computation of refined discrete logarithms in non maximal orders are done.
"""
function picard_group(O::AlgAssAbsOrd, prepare_ref_disc_log::Bool = false)
  @assert is_commutative(O)
  if !prepare_ref_disc_log && isdefined(O, :picard_group)
    mp = O.picard_group::MapPicardGrp{FinGenAbGroup, parent_type(ideal_type(O))}
    return domain(mp), mp
  end

  if is_maximal(O)
    return _picard_group_maximal(O)
  end

  if prepare_ref_disc_log && isdefined(O, :picard_group)
    mP = O.picard_group::MapPicardGrp{FinGenAbGroup, parent_type(ideal_type(O))}
    if isdefined(mP, :betas) && isdefined(mP, :gammas) && isdefined(mP, :right_transform)
      return domain(mP), mP
    end
  end
  return _picard_group_non_maximal(O, prepare_ref_disc_log)
end

function _picard_group_maximal(O::AlgAssAbsOrd)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)
  class_groups = Tuple{FinGenAbGroup, MapClassGrp}[ class_group(field) for (field, map) in fields_and_maps ]
  P = class_groups[1][1]
  for i = 2:length(class_groups)
    P = direct_product(P, class_groups[i][1]; task = :none)::FinGenAbGroup
  end
  S, StoP = snf(P)

  local disc_exp
  let A = A, StoP = StoP, fields_and_maps = fields_and_maps, class_groups = class_groups, O = O
    function disc_exp(x::FinGenAbGroupElem)
      p = StoP(x)
      basis_of_ideal = Vector{elem_type(A)}()
      offset = 1
      for i = 1:length(fields_and_maps)
        K, AtoK = fields_and_maps[i]
        C, CtoIdl = class_groups[i]
        c = C(sub(p.coeff, 1:1, offset:(offset + ngens(C) - 1)))
        I = CtoIdl(c)
        for b in basis(I)
          push!(basis_of_ideal, AtoK\K(b))
        end
        offset += ngens(C)
      end
      I = ideal_from_lattice_gens(A, O, basis_of_ideal)
      return I
    end
  end

  local disc_log
  let fields_and_maps = fields_and_maps, class_groups = class_groups, StoP = StoP, P = P
    function disc_log(x::AlgAssAbsOrdIdl)
      ideals = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
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
  end

  Idl = IdealSet(O)
  StoIdl = MapPicardGrp{FinGenAbGroup, typeof(Idl)}()
  StoIdl.header = MapHeader(S, Idl, disc_exp, disc_log)
  O.picard_group = StoIdl
  return S, StoIdl
end


function _trivial_picard(O::AlgAssAbsOrd, R::FinGenAbGroup, mR)
  A = algebra(O)
  Idl = IdealSet(O)
  local disc_exp_triv
  let O = O
    function disc_exp_triv(x::FinGenAbGroupElem)
      return ideal(O, one(O))
    end
  end

  local disc_log_triv
  let R = R
    function disc_log_triv(x::AlgAssAbsOrdIdl)
      return R()
    end
  end

  Idl = IdealSet(O)
  fac_elem_mon_A = FacElemMon(A)
  RtoIdl = MapPicardGrp{FinGenAbGroup, typeof(Idl)}()
  RtoIdl.header = MapHeader(R, Idl, disc_exp_triv, disc_log_triv)
  RtoIdl.right_transform = zero_matrix(FlintZZ, 0, 0)
  RtoIdl.betas = Vector{elem_type(fac_elem_mon_A)}()
  RtoIdl.gammas = Vector{elem_type(fac_elem_mon_A)}()
  RtoIdl.ray_class_group_map = mR
  O.picard_group = RtoIdl
  return R, RtoIdl

end

# See Bley, Endres "Picard Groups and Refined Discrete Logarithms".
function _picard_group_non_maximal(O::AlgAssAbsOrd, prepare_ref_disc_log::Bool = false)
  A = algebra(O)
  OO = maximal_order(A)

  F = conductor(O, OO, :left)
  FOO = extend(F, OO)

  # We want to use the exact sequence
  # (O/F)^\times \to C_FOO(OO) \to Pic(O) \to 0.
  # where C_FOO(OO) is the ray class group of OO modulo FOO.

  # Firstly, we compute the groups.
  R, mR = ray_class_group(FOO)
  @assert is_snf(R)

  Idl = IdealSet(O)
  fac_elem_mon_A = FacElemMon(A)
  if ngens(R) == 0
    return _trivial_picard(O, R, mR)
  end

  Q, OtoQ = quo(O, F)
  G, GtoQ = multiplicative_group(Q)

  if !prepare_ref_disc_log
    # If we don't need to compute refined discrete logarithms, we compute the
    # picard group as the quotient of groups.

    # Compute the image of the map from G to R, i. e. the kernel of the map from
    # R to Pic(O).
    GinR = Vector{FinGenAbGroupElem}()
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

    # In principle S_rels is the SNF of FinGenAbGroup(H), but we can as well use R
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
      b, a = has_principal_generator_1_mod_m(gens_of_R[i]^R.snf[i], FOO)
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

  local disc_exp
  let Idl = Idl, gens_snf = gens_snf
    function disc_exp(x::FinGenAbGroupElem)
      y = one(Idl)
      for i = 1:length(x.coeff)
        y *= gens_snf[i]^x[i]
      end
      return y
    end
  end

  local disc_log
  let F = F, OO = OO, mR = mR, StoR = StoR
    function disc_log(x::AlgAssAbsOrdIdl)
      if !is_invertible(x)[1]
        error("Ideal is not invertible")
      end
      if !isone(x + F)
        x, _ = _coprime_integral_ideal_class(x, F)
      end

      xOO = extend(x, OO)
      r = mR\xOO
      return StoR\r
    end
  end

  StoIdl = MapPicardGrp{FinGenAbGroup, typeof(Idl)}()
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

  if !is_invertible(a)[1]
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
    a, t = _coprime_integral_ideal_class_deterministic(a, F)
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
  rr = Vector{ZZRingElem}(undef, ngens(R))
  num1 = ngens(R) - ngens(P) # the number of ones in the SNF of P
  for i = 1:num1
    rr[i] = rV[1, i]
  end

  p = Vector{ZZRingElem}(undef, ngens(P))
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

@doc raw"""
    principal_generator(a::AlgAssAbsOrdIdl) -> AlgAssAbsOrdElem

Given a principal ideal $a$ in an order $O$ in a commutative algebra over
$\mathbb Q$, this function returns a principal generator of $a$.
"""
function principal_generator(a::AlgAssAbsOrdIdl)
  a, g = _is_principal_with_data_etale(a)
  if !a
    error("Ideal is not principal")
  end
  return g
end

function _principal_generator_fac_elem(a::AlgAssAbsOrdIdl)
  @assert is_maximal(order(a)) "Not implemented"
  a, g = is_principal_maximal_fac_elem(a)
  if !a
    error("Ideal is not principal")
  end
  return g
end

function _is_principal_with_data_etale(a::AlgAssAbsOrdIdl; local_freeness::Bool = false)
  # all the internal functions assume that the ideal is an ideal of the order
  #
  # support the keyword argument, since the "generic" interface requires it
  O = order(a)
  d = denominator(a, O)
  b = d * a
  if is_maximal(O)
    fl, z = _is_principal_maximal(b)
  else
    fl, z =  _is_principal_non_maximal(b)
  end
  if !fl
    return fl, elem_in_algebra(z)
  else
    # d * a = z * O
    return fl, 1//d * elem_in_algebra(z)
  end
end

function is_principal_fac_elem(a::AlgAssAbsOrdIdl)
  @assert is_maximal(order(a)) "Not implemented"
  return _is_principal_maximal_fac_elem(a)
end

function _is_principal_maximal(a::AlgAssAbsOrdIdl)
  b, x = _is_principal_maximal_fac_elem(a)
  return b, order(a)(evaluate(x))
end

function _is_principal_maximal_fac_elem(a::AlgAssAbsOrdIdl)
  O = order(a)
  @assert is_one(denominator(a, O))
  A = algebra(O)
  fields_and_maps = as_number_fields(A)

  idems = [ AtoK\one(K) for (K, AtoK) in fields_and_maps ]
  sum_idems = sum(idems)
  minus_idems = [ -one(A)*idem for idem in idems ]
  bases = Vector{elem_type(A)}()
  exps = Vector{ZZRingElem}()
  for i = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[i]
    C, mC = class_group(K) # should be cached
    Hecke._assure_princ_gen(mC)
    ai = _as_ideal_of_number_field(a, AtoK)
    c, g = is_principal_fac_elem(ai)
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

# for is_principal_non_maximal see AbsSimpleNumFieldOrder/PicardGroup.jl

################################################################################
#
#  Ray Class Group
#
################################################################################

# inf_pcl[i] may contain places for the field A.maps_to_numberfields[i][1]
function ray_class_group(m::AlgAssAbsOrdIdl, inf_plc::Vector{Vector{T}} = Vector{Vector{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}}}()) where {T}
  O = order(m)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)

  # Compute the groups in the number fields
  groups = Vector{Tuple{FinGenAbGroup, MapRayClassGrp}}()
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
    C = direct_product(C, groups[i][1], task = :none)::FinGenAbGroup
  end
  S, StoC = snf(C)

  one_ideals = _lift_one_ideals(O)
  fac_elem_mon = FacElemMon(parent(m))

  local disc_exp
  let StoC = StoC, groups = groups, O = O, one_ideals = one_ideals
    function disc_exp(x::FinGenAbGroupElem)
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
  end

  local disc_log
  let fields_and_maps = fields_and_maps, C = C, StoC = StoC
    function disc_log(x::AlgAssAbsOrdIdl)
      ideals = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
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
      ideals = Vector{FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}}()
      for i = 1:length(fields_and_maps)
        base = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
        exp = Vector{ZZRingElem}()
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

  local disc_exp
  let fac_elem_mon = fac_elem_mon, generators = generators
    function disc_exp(x::FinGenAbGroupElem)
      y = fac_elem_mon()
      for i = 1:ngens(parent(x))
        y *= generators[i]^x[i]
      end
      return y
    end
  end

  local disc_log
  let StoR = StoR, mR = mR
    function disc_log(x::FacElem)
      return StoR\(mR\x)
    end

    function disc_log(x::AbsNumFieldOrderIdeal)
      return StoR\(mR\x)
    end
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

function has_principal_generator_1_mod_m(I::Union{ AlgAssAbsOrdIdl, FacElem{ <: AlgAssAbsOrdIdl, <: AlgAssAbsOrdIdlSet} }, m::AlgAssAbsOrdIdl)
  O = order(m)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)

  idems = elem_type(A)[ AtoK\one(K) for (K, AtoK) in fields_and_maps ]
  sum_idems = sum(idems)
  minus_idems = elem_type(A)[ -one(A)*idem for idem in idems ]
  bases = Vector{elem_type(A)}()
  exps = Vector{ZZRingElem}()
  for i = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[i]
    mi = _as_ideal_of_number_field(m, AtoK)
    Ii = _as_ideal_of_number_field(I, AtoK)
    a, g = has_principal_generator_1_mod_m(Ii, mi)
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

function disc_log_generalized_ray_class_grp(I::FacElem{S, T}, mR::MapRayClassGroupAlg) where { S <: AlgAssAbsOrdIdl, T <: AlgAssAbsOrdIdlSet }
  m = modulus(mR)
  O = order(m)
  A = algebra(O)

  if isempty(I)
    return FacElemMon(A)(), domain(mR)()
  end

  fields_and_maps = as_number_fields(A)

  groups = mR.groups_in_number_fields

  ideals = Vector{FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}}()

  for i = 1:length(fields_and_maps)
    push!(ideals, _as_ideal_of_number_field(I, fields_and_maps[i][2]))
  end

  idems = elem_type(A)[ AtoK\one(K) for (K, AtoK) in fields_and_maps ]
  sum_idems = sum(idems)
  minus_idems = elem_type(A)[ -one(A)*idem for idem in idems ]
  bases = Vector{elem_type(A)}()
  exps = Vector{ZZRingElem}()
  p = zero_matrix(FlintZZ, 1, 0)
  ideal_gens = Vector{elem_type(O)}()
  for i = 1:length(ideals)
    K, AtoK = fields_and_maps[i]
    d, lI = disc_log_generalized_ray_class_grp(ideals[i], groups[i][2])
    p = hcat(p, lI.coeff)
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

function disc_log_generalized_ray_class_grp(I::S, mR::MapRayClassGroupAlg) where {S <: AlgAssAbsOrdIdl}
  m = modulus(mR)
  O = order(m)
  A = algebra(O)

  fields_and_maps = as_number_fields(A)

  groups = mR.groups_in_number_fields

  ideals = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()

  for i = 1:length(fields_and_maps)
    push!(ideals, _as_ideal_of_number_field(I, fields_and_maps[i][2]))
  end

  idems = elem_type(A)[ AtoK\one(K) for (K, AtoK) in fields_and_maps ]
  sum_idems = sum(idems)
  minus_idems = elem_type(A)[ -one(A)*idem for idem in idems ]
  bases = Vector{elem_type(A)}()
  exps = Vector{ZZRingElem}()
  p = zero_matrix(FlintZZ, 1, 0)
  ideal_gens = Vector{elem_type(O)}()
  for i = 1:length(ideals)
    K, AtoK = fields_and_maps[i]
    d, lI = disc_log_generalized_ray_class_grp(ideals[i], groups[i][2])
    p = hcat(p, lI.coeff)
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

@doc raw"""
    kernel_group_with_disc_log(O::AlgAssAbsOrd) -> FinGenAbGroup, MapPicardGroup

Given an order $O$ in a commutative algebra over $\mathbb Q$, this function
returns the group $D$ in the exact sequence $0 \to D \to Pic(O) \to Pic(O')$
where $O'$ is a maximal order containing $O$.
"""
function kernel_group_with_disc_log(O::AlgAssAbsOrd)
  A = algebra(O)
  @req is_commutative(O) "Order must be commutative"
  OO = maximal_order(A)

  # We use the short exact sequence
  # 0 \to D(O) \to Pic(O) \to Pic(OO) \to 0,
  # where D(O) is the kernel group of O.

  P, mP = picard_group(O)
  C, mC = picard_group(OO)

  Idl = IdealSet(O)
  if C == P
    D = FinGenAbGroup(ZZRingElem[])
    local disc_exp_triv
    let O = O
      function disc_exp_triv(x::FinGenAbGroupElem)
        return ideal(O, one(O))
      end
    end

    local disc_log_triv
    let D = D
      function disc_log_triv(x::AlgAssAbsOrdIdl)
        return D()
      end
    end

    DtoIdl = MapPicardGrp{typeof(D), typeof(Idl)}()
    DtoIdl.header = MapHeader(D, Idl, disc_exp_triv, disc_log_triv)
    return D, DtoIdl
  end

  # Build the morphism from Pic(O) to Pic(OO)
  A = Vector{FinGenAbGroupElem}()
  B = Vector{FinGenAbGroupElem}()
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

  local disc_exp
  let Idl = Idl, gens_snf = gens_snf
    function disc_exp(x::FinGenAbGroupElem)
      y = one(Idl)
      for i = 1:length(x.coeff)
        y *= gens_snf[i]^x.coeff[1, i]
      end
      return y
    end
  end

  local disc_log
  let mP = mP, DtoP = DtoP, StoD = StoD
    function disc_log(x::AlgAssAbsOrdIdl)
      p = mP\x
      b, g = has_preimage_with_preimage(DtoP, p)
      @assert b "Ideal not an element of the kernel group"
      return StoD\g
    end
  end

  StoIdl = MapPicardGrp{FinGenAbGroup, typeof(Idl)}()
  StoIdl.header = MapHeader(S, Idl, disc_exp, disc_log)
  return S, StoIdl
end

################################################################################
#
#  Coprime representatives
#
################################################################################

# Mostly taken from AbsSimpleNumFieldOrder/LinearAlgebra.jl
function _coprime_integral_ideal_class(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl)
  O = order(b)
  @assert isone(denominator(b, O))
  d = denominator(a, O)
  a = d*a
  a_inv = inv(a)
  c = ideal(O, one(O))
  x = algebra(O)()
  check = true
  cnt = 0
  while check
    cnt += 1
    if cnt > 10000
      return _coprime_integral_ideal_class_deterministic(a, b)
    end
    x = rand(a_inv, 200)
    c = x*a
    @assert denominator(c, O) == 1
    c.order = O
    if iszero(det(basis_matrix(c)))
      continue
    end
    isone(c + b) ? (check = false) : (check = true)
  end
  return c, x*d
end

function _intersect_modules(BM::FakeFmpqMat, BN::FakeFmpqMat)
  dM = denominator(BM)
  dN = denominator(BN)
  d = lcm(dM, dN)
  BMint = change_base_ring(FlintZZ, numerator(d * BM))
  BNint = change_base_ring(FlintZZ, numerator(d * BN))
  H = vcat(BMint, BNint)
  K = kernel(H, side = :left)
  BI = divexact(change_base_ring(FlintQQ, hnf(view(K, 1:nrows(K), 1:nrows(BM)) * BMint)), d)
  return BI
end

function _coprime_integral_ideal_class_deterministic(a::AlgAssAbsOrdIdl, b::AlgAssAbsOrdIdl)
  aorig = a
  O = order(b)
  a.order = O
  @assert isone(denominator(b, O))
  # Now intersect b with the maximal order of the base field
  A = algebra(O)
  K = base_ring(A)
  OK = base_ring(O)
  BM = FakeFmpqMat(basis_matrix([A(one(K))]))
  BN = basis_matrix(b)
  BI = _intersect_modules(BM, BN)
  local c::ZZRingElem
  for i in 1:ncols(BM)
    if !iszero(BM[1, i])
      c = FlintZZ(divexact(BI[1, i], BM[1, i]))
      break
    end
  end
  #@show (basis_matrix(c * O) * inv(basis_matrix(b)))
  @assert c * BM == FakeFmpqMat(BI)
  # The intersection b \cap Z is c*Z
  lp = prime_divisors(c)
  local_bases_inv = elem_type(A)[]
  d = denominator(a, O)
  a = d * a
  a.order = O
  for p in lp
    fl, x = is_locally_free(O, a, p, side = :right)
    @assert valuation(det(basis_matrix(a) * inv(basis_matrix(x * O))), p) == 0
    dd = denominator(basis_matrix(a) * inv(basis_matrix(x * O)))
    xx = x * 1//dd
    push!(local_bases_inv, inv(xx))
  end
  # Now compute \beta_i such that bi = 1 mod p_i and bj = 0 mod p_j
  elems = ZZRingElem[]
  rhs = ZZRingElem[0 for i in 1:length(lp)]
  for i in 1:length(lp)
    rhs[i] = 1
    c = crt(rhs, lp)
    push!(elems, c)
    rhs[i] = 0
    @assert mod(c, lp[i]) == 1
  end
  x = sum(elems[i] * local_bases_inv[i] for i in 1:length(lp))
  #@show x
  res_elem = x * d
  res_ideal = x * a
  #@show res_ideal
  #@show res_ideal == res_ideal + b
  #@show (basis_matrix(res_ideal) * inv(basis_matrix(res_ideal + b)))
  #@show (basis_matrix(b) * inv(basis_matrix(res_ideal)))

  #@show res_ideal + b
  #@show one(A) * O

  @assert res_elem * aorig == res_ideal
  @assert res_ideal + b == one(A) * O
  return res_ideal, res_elem
end
