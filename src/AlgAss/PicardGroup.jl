################################################################################
#
#  Map Types
#
################################################################################

mutable struct MapRayClassGroupAlg{S, T} <: Map{S, T, HeckeMap, MapRayClassGroupAlg}
  header::MapHeader{S, T}

  function MapRayClassGroupAlg{S, T}() where {S, T}
    return new{S, T}()
  end
end

mutable struct MapPicardGrp{S, T} <: Map{S, T, HeckeMap, MapPicardGrp}
  header::MapHeader{S, T}

  function MapPicardGrp{S, T}() where {S, T}
    return new{S, T}()
  end
end

################################################################################
#
#  Picard group
#
################################################################################

function picard_group(O::AlgAssAbsOrd)
  OO = maximal_order(algebra(O)) # We need it later anyway
  if O == OO
    return _picard_group_maximal(OO)
  end
  return _picard_group_non_maximal(O)
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
  return S, StoIdl
end

# See Bley, Endres "Picard Groups and Refined Discrete Logarithms".
function _picard_group_non_maximal(O::AlgAssAbsOrd)
  A = algebra(O)
  OO = maximal_order(A)

  F = conductor(O, OO)
  FOO = F*OO

  # We want to use the exact sequence
  # (O/F)^\times \to C_FOO(OO) \to Pic(O) \to 0.
  # where C_FOO(OO) is the ray class group of modulo FOO.

  # Firstly, we compute the groups.
  R, mR = ray_class_group(FOO)

  Idl = IdealSet(O)
  if ngens(R) == 0
    function disc_exp_triv(x::GrpAbFinGenElem)
      return ideal(O, one(O))
    end

    function disc_log_triv(x::AlgAssAbsOrdIdl)
      return R()
    end

    RtoIdl = MapPicardGrp{typeof(R), typeof(Idl)}()
    RtoIdl.header = MapHeader(R, Idl, disc_exp_triv, disc_log_triv)
    return R, RtoIdl
  end

  G, GtoO = _multgrp_mod_ideal(O, F)

  # Compute the image of the map from G to R, i. e. the kernel of the map from
  # R to Pic(O).
  GinR = Vector{GrpAbFinGenElem}()
  for i = 1:ngens(G)
    g = OO(GtoO(G[i]))
    r = mR\(ideal(OO, g))
    push!(GinR, r)
  end

  # Compute the Picard group
  P, RtoP = quo(R, GinR)
  S, StoP = snf(P)

  #= generators = Vector{ideal_type(O)}(undef, ngens(R)) =#
  #= for i = 1:ngens(R) =#
  #=   I = mR(R[i]) =#
  #=   generators[i] = contract(evaluate(I), O) =#
  #= end =#

  #= gens_snf = Vector{ideal_type(O)}(undef, ngens(S)) =#
  #= for i = 1:ngens(S) =#
  #=   x = (RtoP\StoP(S[i])).coeff =#
  #=   for j = 1:ngens(R) =#
  #=     x[1, j] = mod(x[1, j], S.snf[end]) =#
  #=   end =#
  #=   y = one(Idl) =#
  #=   for j = 1:ngens(R) =#
  #=     y *= generators[j]^x[1, j] =#
  #=   end =#
  #=   gens_snf[i] = y =#
  #= end =#

  gens_snf = Vector{ideal_type(O)}(undef, ngens(S))
  for i = 1:ngens(S)
    r = RtoP\StoP(S[i])
    gens_snf[i] = contract(evaluate(mR(r)), O)
  end

  function disc_exp(x::GrpAbFinGenElem)
    y = one(Idl)
    for i = 1:length(x.coeff)
      y *= gens_snf[i]^x.coeff[1, i]
    end
    return y
  end

  function disc_log(x::AlgAssAbsOrdIdl)
    if !isone(x + F)
      error("Ideal is not coprime to the conductor")
    end

    xOO = extend(x, OO)
    r = mR\xOO
    p = RtoP(r)
    return StoP\p
  end

  StoIdl = MapPicardGrp{typeof(S), typeof(Idl)}()
  StoIdl.header = MapHeader(S, Idl, disc_exp, disc_log)
  return S, StoIdl
end

################################################################################
#
#  Ray Class Group
#
################################################################################

function ray_class_group(m::AlgAssAbsOrdIdl)
  O = order(m)
  A = algebra(O)
  fields_and_maps = as_number_fields(A)

  # Compute the groups in the number fields
  groups = Vector{Tuple{GrpAbFinGen, MapRayClassGrp}}()
  for i = 1:length(fields_and_maps)
    mi = _as_ideal_of_number_field(m, fields_and_maps[i][2])
    push!(groups, ray_class_group(mi))
  end

  C = groups[1][1]
  for i = 2:length(groups)
    C = direct_product(C, groups[i][1])[1]
  end
  S, StoC = snf(C)

  # Compute the generators
  one_ideals = _lift_one_ideals(O)
  fac_elem_mon = FacElemMon(parent(m))

  generators = Vector{elem_type(fac_elem_mon)}()
  for i = 1:length(fields_and_maps)
    K, AtoK = fields_and_maps[i]
    G, GtoIdl = groups[i]
    for j = 1:ngens(G)
      Ifac = GtoIdl(G[j])
      base = Vector{ideal_type(O)}()
      exp = Vector{fmpz}()
      for (I, e) in Ifac
        J = _as_ideal_of_algebra(I, i, O, one_ideals)
        push!(base, J)
        push!(exp, e)
      end
      push!(generators, FacElem(base, exp))
    end
  end

  gens_snf = typeof(generators)(undef, ngens(S))
  for i = 1:ngens(S)
    x = (StoC(S[i])).coeff
    for j = 1:ngens(C)
      x[1, j] = mod(x[1, j], S.snf[end])
    end
    y = fac_elem_mon()
    for j = 1:ngens(C)
      y *= generators[j]^Int(x[1, j])
    end
    gens_snf[i] = y
  end

  function disc_exp(x::GrpAbFinGenElem)
    y = fac_elem_mon()
    for i = 1:length(x.coeff)
      y *= gens_snf[i]^Int(x.coeff[1, i])
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
  return S, StoIdl
end

################################################################################
#
#  Kernel group
#
################################################################################

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
