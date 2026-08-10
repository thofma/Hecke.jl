module pRational

using ..Hecke

import Hecke:
  @sprintf,
  IntegerUnion,
  induce_image

import ..Hecke.MultDep:
  _psaturation

function _pick_automorphisms(K; is_abelian = false)
  A = automorphism_list(K; is_abelian)
  if is_totally_real(K)
    return A[1:end-1]
  else
    Ps = infinite_places(K)
    AA = eltype(A)[]
    P = Ps[1]
    Pst = eltype(Ps)[]
    for a in A
      Q = induce_image(a, P)
      if Q in Pst
        continue
      else
        push!(AA, a)
        push!(Pst, Q)
      end
    end
    return AA[1:end-1]
  end
end

function _random_cyclic_subgroup(K, aut, cyc)
  cnt = 0
  while true
    rad = 10
    if cnt % 1000 == 1
      rad += 1
      @info "Increase radius to $(rad)"
    end
    if eltype(cyc) === AbsSimpleNumFieldElem
      uu = FacElem(Dict(rand(cyc) => rand(-1:1) for i in 1:rad))
    else
      uu = prod(rand(cyc)^rand([-1,1]) for i in 1:rad)
    end
    try
      fl, = _schirokauer_map_data_minkowski_unit(K, uu, next_prime(rand(2^10:2^20)), aut)
      if fl
        return uu
      end
    catch e
      rethrow(e)
    end
  end
end

function _schirokauer_map_data_minkowski_unit(K, u::Union{AbsSimpleNumFieldElem, FacElem}, ell, aut = nothing; is_abelian = false, new::Bool = true)
  __schirokauer_map_data_minkowski_unit(K, u, ell, aut === nothing ? _pick_automorphisms(K; is_abelian) : aut, is_abelian, new)
end

function __schirokauer_map_data_minkowski_unit(K, u::Union{AbsSimpleNumFieldElem, FacElem}, ell, aut::Vector, is_abelian::Bool, new::Bool = true)
  if is_index_divisor(maximal_order(K), ell) || is_ramified(maximal_order(K), ell)
    if u isa FacElem
      error("no can do")
    end
    return _schirokauer_map_data_really_generic(K, u, ell, ZZ(ell)^2, aut)
  end
  if 2*nbits(ell) < 63
    if new
      return ___schirokauer_map_data_minkowski_unit_new(K, u, ell, ell^2, aut)
    else
      return ___schirokauer_map_data_minkowski_unit(K, u, ell, ell^2, aut)
    end
  else
    if new
      return ___schirokauer_map_data_minkowski_unit_new(K, u, ell, ZZ(ell)^2, aut)
    else
      return ___schirokauer_map_data_minkowski_unit(K, u, ell, ZZ(ell)^2, aut)
    end
  end
end

function _lift_from_Zellx_to_K(Zx, a, g)
  return lift(Zx, g)(a)
end

function _mod(Zell2x, u::AbsSimpleNumFieldElem, dpoly, dpolymodl, Zellx)
  return Zell2x(Hecke.__mod(u, ZZ(modulus(base_ring(Zell2x)))))
end

function _mod(Zell2x, u::FacElem, dpoly, dpolymodl, Zellx; D = Dict{AbsSimpleNumFieldElem, elem_type(Zell2x)}(), Dinv = Dict{AbsSimpleNumFieldElem, elem_type(Zell2x)}())
  res = one(Zell2x)
  w = Zellx()
  for (b, e) in u
    v = get!(D, b) do
      _mod(Zell2x, b, dpoly, dpolymodl, Zellx)
    end
    if e < 0
      v = get!(Dinv, b) do
        # compute the inverse mod l^2 by Hensel lifting (2*w - v * w^2) where w is the inverse mod l
        #w = Zellx(b)
        if w isa ZZModPolyRingElem
          Hecke.Nemo.nf_elem_to_fmpz_mod_poly!(w, b)
        else
          Hecke.Nemo.nf_elem_to_nmod_poly!(w, b)
        end
        winv = invmod(w, dpolymodl)
        winv2 = change_base_ring(base_ring(Zell2x), lift(Hecke.Globals.Zx, winv); parent = Zell2x)
        twowinv2 = 2*winv2
        Hecke.mul!(winv2, winv2, winv2)
        Hecke.mod!(winv2, winv2, dpoly)
        Hecke.mul!(winv2, winv2, v)
        Hecke.mod!(winv2, winv2, dpoly)
        _v = sub!(twowinv2, twowinv2, winv2)
        #_v = mod(2*winv2 - v * winv2^2, dpoly)
        #@show v, dpoly
        #_v = invmod(v, dpoly)
        #@show mod(v * _v, dpoly)
        #@assert mod(v * _v, dpoly) |> is_one
        _v
      end
      e = -e
    end
    res = Hecke.mul!(res, res, powermod(v, e, dpoly))
    res = Hecke.mod!(res, res, dpoly)
  end
  return res
end

assert_toggle() = false

const toggle_lock = ReentrantLock()

function toggle(enable::Bool)
    lock(toggle_lock) do
        @eval assert_toggle() = $enable
        on_or_off = enable ? "on." : "off."
        @info "Toggleable asserts turned "*on_or_off
    end
end

macro t(ex)
  return :(assert_toggle() ? $(esc(ex)) : nothing)
end

function ___schirokauer_map_data_minkowski_unit_new(K, u::Union{AbsSimpleNumFieldElem, FacElem}, ell, ell2, aut = _pick_automorphisms(K))
  @t tstart = time()
  # assume that K is normal and u is a minkowski unit
  d = degree(K)
  a = gen(K)
  r = Hecke.unit_group_rank(K)
  A = aut
  OK = lll(maximal_order(K))
  @assert !is_ramified(OK, ell)
  dectyp = prime_decomposition_type(OK, ell)
  f = dectyp[1][1]
  # we want to detect the inert case
  # because `frobenius` is faster
  ellpm1 = ZZ(ell)^f - 1
  g = defining_polynomial(K)
  Qx = parent(g)
  #Zellx, = Hecke.Nemo.Native.GF(ell; cached = false)[:x]
  Zellx, = polynomial_ring(residue_ring(ZZ, ell; cached = false)[1]; cached = false)
  Zell2x, = polynomial_ring(residue_ring(ZZ, ell2; cached = false)[1]; cached = false)
  ZZy, = polynomial_ring(ZZ, :y; cached = false)
  gmodell2 = change_base_ring(base_ring(Zell2x), g; parent = Zell2x)
  gmodell = change_base_ring(base_ring(Zellx), g; parent = Zellx)
  # Compute u^(ell^f - 1) in Z/l^2[X] modulo g
  @t tstartpow = time()
  num = powermod(_mod(Zell2x, u, gmodell2, gmodell, Zellx), ellpm1, gmodell2) - 1
  @t(tpow = time() - tstartpow)
  @t tauto = 0.0
  if f == d
    # Create the finite field
    F, o = Hecke.Nemo.Native.finite_field(gmodell; cached = false)
    # Lift to ZZy and divide by ell, then pass to Z/l[X] and then to F = Z/l[X]/g
    upow_mod_ell2_ff = F(change_base_ring(base_ring(Zellx), divexact!(lift(ZZy, num), ell); parent = Zellx))

    # If K is totally imaginary, then r = d/2 - 1, so this is exactly what we need
    M = zero_matrix(base_ring(Zellx), r, d)
    @t tstartmat = time()
    for i in 1:r
      for j in 1:d
        M[i, j] = coeff(upow_mod_ell2_ff, j - 1)
      end
      upow_mod_ell2_ff = frobenius(upow_mod_ell2_ff)
    end
    @t tmat = time() - tstartmat
  else
    # Lift to ZZy and divide by ell, then pass to Z/l[X]
    upow_mod_ell2 = change_base_ring(base_ring(Zellx), divexact!(lift(ZZy, num), ell); parent = Zellx)
    # Determine the action of the automorphisms mod ell
    @t tstartauto = time()
    autmodl = elem_type(Zellx)[change_base_ring(base_ring(Zellx), Qx(Hecke.image_primitive_element(a)); parent = Zellx) for a in A]
    @t tauto = time() - tstartauto
    M = zero_matrix(base_ring(Zellx), r, d)
    @t tstartmat = time()
    for i in 1:r
      # this is upow_mod_ell2(autmodl[i]) mod gmodell
      b = Hecke.compose_mod(upow_mod_ell2, autmodl[i], gmodell)
      for j in 1:d
        M[i, j] = coeff(b, j - 1)
      end
    end
    @t tmat = time() - tstartmat
  end
  rM = rank(M)
  res = rM == r
  @t begin
  ttotal = time() - tstart
  @info "Timings for d = $d, f = $f"
  @info "Total time : $ttotal"
  tpowrel = @sprintf("%.2f", 100 * tpow/ttotal)
  @info "First power: $(tpow) ($(tpowrel)%)"
  tmatrel = @sprintf("%.2f", 100 * tmat/ttotal)
  @info "Matrix comp: $(tmat) ($(tmatrel)%)"
  tautorel = @sprintf("%.2f", 100 * tauto/ttotal)
  @info "Auto reduct: $(tauto) ($(tautorel)%)"
  return res, (; d = degree(K), f, tpow, tmat, tauto, ttotal)
  end
  return res, r - rM, rM
end

# this does not assume anyyhing, except total realness
function _schirokauer_map_data_generic(K, u::Vector, ell; OK = lll(maximal_order(K)))
  if is_index_divisor(maximal_order(K), ell) || is_ramified(OK, ell)
    return _schirokauer_map_data_really_really_generic(K, u, ell, ZZ(ell)^2, OK)
  end

  try
    if 2*nbits(ell) < 63
      @assert fits(Int, ZZ(ell)^2)
      return _schirokauer_map_data_generic(K, u, ell, ell^2, OK)
    else
      return _schirokauer_map_data_generic(K, u, ell, ZZ(ell)^2, OK)
    end
  catch e
    if !(e isa ErrorException && (e.msg == "Problem in the FLINT-Subsystem" || e.msg == "Impossible inverse in invmod"))
      rethrow(e)
    end
    return _schirokauer_map_data_really_really_generic(K, u, ZZ(ell), ZZ(ell)^2, OK)
  end
end

function _schirokauer_map_data_generic(K, u::Vector, ell, ell2, OK)
  d = degree(K)
  a = gen(K)
  #r = Hecke.unit_group_rank(K)
  r = length(u)
  #@assert length(u) == r
  curupowers = similar(u, elem_type(K))
  lP = prime_ideals_over(OK, ell)
  @assert !is_ramified(OK, ell)
  #@info length(lP)
  g = defining_polynomial(K)
  Zell2x, = residue_ring(ZZ, ell2)[1][:x]
  Zellx, = residue_ring(ZZ, ell)[1][:x]
  ZZy, = ZZ[:y]
  gmodell2 = change_base_ring(base_ring(Zell2x), g; parent = Zell2x)
  gmodell = change_base_ring(base_ring(Zellx), g; parent = Zellx)
  sort!(lP, by = P -> norm(P))
  # We do the computations prime ideal by prime ideal.
  # We sort the prime ideals, so that we can reuse the powers u^norm(P) in case
  # the prime ideal has the same norm as the previous one
  if eltype(u) <: FacElem
    D = Dict{AbsSimpleNumFieldElem, elem_type(Zell2x)}()
    Dinv = Dict{AbsSimpleNumFieldElem, elem_type(Zell2x)}()
    u_mod_ell2 = [_mod(Zell2x, u[i], gmodell2, gmodell, Zellx; D, Dinv) for i in 1:length(u)]
  else
    u_mod_ell2 = [_mod(Zell2x, u[i], gmodell2, gmodell, Zellx) for i in 1:length(u)]
  end

  M = zero_matrix(Hecke.Nemo.Native.GF(ell), r, d)
  oldnorm = zero(ZZ)
  new_norm = false
  curj = 0
  #@show lP |> length
  for j in 1:length(lP)
    P = lP[j]
    if norm(P) != oldnorm
      oldnorm = norm(P)
      normPm1 = norm(P) - 1
      new_norm = true
    else
      new_norm = false
    end
    #@info "new_norm: $(new_norm)"
    F, mF = Hecke.ResidueFieldSmall(OK, P)
    mFF = Hecke.extend(mF, K)
    mFF_easy = Hecke.extend_easy(mF, K)
    for i in 1:length(u)
      jj = curj + 1
      #@info jj
      #vv = divexact(_powermod(us[i], ellpm1, ZZ(ell)^2)- 1, ell)
      if new_norm
        curupowers[i] = divexact(_lift_from_Zellx_to_K(ZZy, a, powermod(u_mod_ell2[i], normPm1, gmodell2) - 1), ell)
        #curupowers[i] = divexact(lift(ZZy, powermod(_mod(Zellx, u[i], gmodell2), normPm1, gmodell2) - 1)(a), ell)
      end
      w = curupowers[i]
      vv = mFF(w)
      for k in 1:degree(P)
        M[i, jj] = coeff(vv, k - 1)
        jj += 1
      end
    end
    curj += degree(P)
  end
  #for j in 1:d
  #  M[d, j] = 1
  #end
  #Base.show(stdout, "text/plain", M)
  r = Hecke.unit_group_rank(K)
  rM = rank(M)
  return rM == r, r - rM, rM
end

function _schirokauer_map_data_really_generic(K, _u, ell, ell2, aut)
  if parent(_u) === K
    OK = maximal_order(K)
    u = OK(_u)::elem_type(OK)
  else
    OK = parent(_u)
    u = _u::elem_type(OK)
  end
  n = euler_phi(ell*OK)
  r = Hecke.unit_group_rank(K)
  @assert length(aut) == r
  d = degree(K)
  M = zero_matrix(Hecke.Nemo.Native.GF(ell), r, d)
  uimg = divexact(powermod(u, n, ell2) - 1, ell)
  for i in 1:r
    z = OK(aut[i](elem_in_nf(uimg)))
    M[i, :] = coordinates(z)
  end
  rM = rank(M)
  return rM == r, r - rM, rM
end

# We cannot do clever things with polynomials, so we just evaluate into OK/ell^2
# and compute everything there
function _schirokauer_map_data_really_really_generic(K, u::Vector, ell, ell2, OK)
  R, OKtoR = quo(OK, ell2 * OK)
  n = euler_phi(ell*OK)
  r = length(u)
  d = degree(K)
  M = zero_matrix(Hecke.Nemo.Native.GF(ell), r, d)
  for i in 1:r
    z = divexact(preimage(OKtoR, OKtoR(u[i])^n) - 1, ell)
    M[i, :] = coordinates(z)
  end
  rM = rank(M)
  r = Hecke.unit_group_rank(K)
  return rM == r, r - rM, rM
end

function _schirokauer_map_data_really_generic(K, _u::Vector, ell, ell2, OK)
  if eltype(_u) <: FacElem
    u = OK.(evaluate.(_u))::Vector{elem_type(OK)}
  else
    u = OK.(_u)::Vector{elem_type(OK)}
  end
  n = euler_phi(ell*OK)
  r = length(u)
  @assert r == Hecke.unit_group_rank(K)
  d = degree(K)
  M = zero_matrix(Hecke.Nemo.Native.GF(ell), r, d)
  for i in 1:r
    z = divexact(powermod(u[i], n, ell2) - 1, ell)
    M[i, :] = coordinates(z)
  end
  rM = rank(M)
  return rM == r, r - rM, rM
end

# Algorithm 1 of Computing the local group of prime-power classes
function local_group_modulo_prime_power_classes(K::AbsSimpleNumField, P, p)
  e = ramification_index(P)
  k = Int(floor(e * p//(p - 1))) + 1
  OK = order(P)
  Q, OKtoQ = quo(OK, P^k)
  U, UtoQ = Hecke._mult_grp(Q, p; method = :quadratic)
  A, UtoA = quo(U, p)
  return A, x -> UtoA(UtoQ\(OKtoQ(x)))
end

function _create_eta_map(K, p; OK = lll(maximal_order(K)))
  Ps = prime_ideals_over(OK, p)
  unitgroups = []
  maps = []
  for P in Ps
    A, map = local_group_modulo_prime_power_classes(K, P, p)
    push!(unitgroups, A)
    push!(maps, map)
  end
  U, proj, inj = biproduct(unitgroups...)
  U, x -> sum(i(m(x)) for (m, i) in zip(maps, inj))
end

struct pRationalityTestGenericCtx{S, T, U, V}
  K::AbsSimpleNumField
  OK::AbsSimpleNumFieldOrder
  maxindep::S
  maxindepnotmaximal::Vector{ZZRingElem} # primes where unit group is not known to be maximal
  minkowski::T
  torsionunit::U
  aut::V
  classnumber::ZZRingElem
end

function pRationalityTestGenericCtx(K::AbsSimpleNumField, maxindep, maxindepnotmaximal, mink, torsionunit, aut, classnumber)
  OK = lll(maximal_order(K))
  return pRationalityTestGenericCtx{typeof(maxindep), typeof(mink), typeof(torsionunit), typeof(aut)}(
    K,
    OK,
    maxindep,
    maxindepnotmaximal,
    mink,
    torsionunit,
    aut,
    classnumber)
end

function p_rationality_context(K::AbsSimpleNumField; GRH::Bool = false, fundamental_units = nothing, class_number = nothing, is_normal::Bool = false)
  if !is_normal
    return _p_rationality_context(K; GRH, fundamental_units, class_number)
  else
    return _p_rationality_context_normal(K; GRH, fundamental_units, class_number)
  end
end

function _p_rationality_context(K::AbsSimpleNumField; GRH::Bool = false, fundamental_units = nothing, class_number = nothing)
  OK = lll(maximal_order(K))
  if fundamental_units === nothing
    U, mU = unit_group_fac_elem(OK; GRH)
    us = mU.(gens(U))
  else
    us = fundamental_units
  end
  tor = FacElem(torsion_units_generator(K))
  maxindepnotmaximal = ZZRingElem[]
  if class_number === nothing
    classnumber = Hecke.class_number(OK; GRH)
  else
    classnumber = class_number
  end
  return pRationalityTestGenericCtx(K, us, maxindepnotmaximal, nothing, tor, nothing, classnumber)
end

function _p_rationality_context_normal(K::AbsSimpleNumField; GRH::Bool = false, fundamental_units = nothing, class_number = nothing)
  OK = lll(maximal_order(K))
  if fundamental_units === nothing
    U, mU = unit_group_fac_elem(OK; GRH = GRH)
    us = mU.(gens(U)[2:end])
  else
    us = fundamental_units
  end
  tor = FacElem(torsion_units_generator(K))
  maxindepnotmaximal = ZZRingElem[]
  if class_number === nothing
    classnumber = Hecke.class_number(OK; GRH)
  else
    classnumber = class_number
  end
  autfull = automorphism_list(K)
  aut = _pick_automorphisms(K)
  #@info "Computing random Minkowski unit"
  mink = _random_cyclic_subgroup(K, aut, us)

  return pRationalityTestGenericCtx(K, us, maxindepnotmaximal, mink, tor, aut, classnumber)
end

function p_rationality_context_form_norm_relation(K::AbsSimpleNumField, h::ZZRingElem; GRH = false)
  N = Hecke.NormRel._norm_relation_setup_generic(K; small_degree = true, pure = true)
  us = []
  for (k, ktoK) in N.subfields
    ok = lll(maximal_order(k))
    U, mU = unit_group_fac_elem(ok; GRH = GRH)
    append!(us, ktoK.(mU.(gens(U)[2:ngens(U)])))
  end
  us = identity.(us)
  C, mC = Hecke.multiplicative_group(us; task = :modulo_tor, support = ideal_type(maximal_order(K))[]);
  uss = mC.(gens(C))
  tor = FacElem(torsion_units_generator(K))

  autfull = automorphism_list(K)
  aut = _pick_automorphisms(K)
  mink = _random_cyclic_subgroup(K, aut, us)

  return pRationalityTestGenericCtx(K, uss, prime_divisors(N.denominator), mink, tor, aut, h)
end

function _p_maximal_units(T, p; OK = lllmaximal_order(T), GRH::Bool = true)
  if !(p in T.maxindepnotmaximal)
    if !is_divisible_by(torsion_units_order(Hecke.nf(OK)), p)
      return T.maxindep
    else
      return push!(copy(T.maxindep), T.torsionunit)
    end
  else
    C, mC = Hecke.multiplicative_group(identity.(T.maxindep); task = :modulo_tor, support = ideal_type(OK)[]);
    mCp = _psaturation(mC, p)
    # we always enlarge by the torsion unit (to be on the safe side)
    return push!(mCp.(gens(domain(mCp))), FacElem(torsion_units_generator(Hecke.nf(OK))))
  end
end

function _p_maximal_units(K::AbsSimpleNumField, p; OK = lll(maximal_order(K)), GRH::Bool = true)
  U, mU = unit_group_fac_elem(OK; GRH)
  us = mU.(gens(U))
  C, mC = Hecke.multiplicative_group(identity.(us); task = :modulo_tor, support = ideal_type(OK)[]);
  mCp = _psaturation(mC, p)
  # we always enlarge by the torsion unit (to be on the safe side)
  return push!(mCp.(gens(domain(mCp))), FacElem(torsion_units_generator(Hecke.nf(OK))))
end

function _is_class_number_divisible(K::AbsSimpleNumField, p; OK, GRH::Bool)
  return is_divisible_by(order(class_group(OK; GRH = GRH)[1]), p)
end

function _is_class_number_divisible(K::pRationalityTestGenericCtx, p; OK, GRH::Bool)
  return is_divisible_by(K.classnumber, p)
end

_is_totally_real(OK) = is_totally_real(Hecke.nf(OK))

function _check_splitting_condition(OK::AbsSimpleNumFieldOrder, p)
  if p > degree(OK) + 1
    return true
  end
  if !is_divisible_by(2*discriminant(OK), p)
    return true
  end
  #if all(!is_divisible_by(e, p - 1) for (P, e) in prime_decomposition(OK, p))
  #  return true
  #end
  if is_divisible_by(torsion_units_order(Hecke.nf(OK)), p)
    return length(prime_ideals_over(OK, p)) == 1
  else
    if all(!is_divisible_by(e, p - 1) for (P, e) in prime_decomposition(OK, p))
      return true
    end
    C = cyclotomic_extension(Hecke.nf(OK), Int(p))
    OC = maximal_order(C.Kr)
    for (P, e) in prime_decomposition(maximal_order(base_field(C.Kr)), p)
      if is_divisible_by(e, p - 1) && length(prime_decomposition(OC, P)) == degree(OC)
        return false
      end
    end
    return true
  end
end

lllmaximal_order(C::pRationalityTestGenericCtx) = C.OK

lllmaximal_order(K) = lll(maximal_order(K))

Hecke.signature(C::pRationalityTestGenericCtx) = Hecke.signature(C.K)

_nf(K::AbsSimpleNumField) = K

_nf(K) = K.K

function _dim_image_of_schirokauer_map(_K::pRationalityTestGenericCtx, us, p)
  K = _nf(_K)
  rK = Hecke.unit_group_rank(K)
  try
    fl, _, dimimage  = _schirokauer_map_data_minkowski_unit(K, _K.minkowski, p, _K.aut; new = true)
  catch e
    if !(e isa ErrorException && (e.msg == "Impossible inverse in invmod" || e.msg == "no can do")) && !(e isa FlintException)
      rethrow(e)
    end
    fl, _, dimimage = _schirokauer_map_data_generic(K, us, p)
  end
  @assert fl == !(dimimage < rK)
  if fl
    return dimimage
  end
  fl, _, dimimage = _schirokauer_map_data_generic(K, us, p)
  @assert fl == !(dimimage < rK)
  return dimimage
end

function _dim_image_of_schirokauer_map(K::AbsSimpleNumField, us, p)
  fl, _, dimimage = _schirokauer_map_data_generic(K, us, p)
  return dimimage
end

function _dim_image_of_eta_map(K, us, p; OK = lll(maximal_order(K)))
  U, f = _create_eta_map(K, p; OK = OK)
  V, = sub(U, f.(us))
  r = rank(V, p)
  return r
end

# Algorithm 15.1

@doc raw"""
    is_quasi_p_rational(K::AbsSimpleNumField, p; GRH::Bool = false)

Return whether the number field $K$ is quasi-$p$-rational.

See also [`is_p_rational`](@ref).

# Examples

```jldoctest
julia> K, = cyclotomic_real_subfield(15);

julia> is_quasi_p_rational(K, 13)
false
```
"""
function is_quasi_p_rational(K::Union{pRationalityTestGenericCtx, AbsSimpleNumField}, p; GRH::Bool = false)
  @req is_prime(p) "p ($p) must be prime"
  fl, = _is_quasi_p_rational(K, p; GRH)
  return fl
end

# is_quasi_p_rational, but also return the p-maximal unit group for later use
function _is_quasi_p_rational(K::Union{pRationalityTestGenericCtx, AbsSimpleNumField}, p::IntegerUnion; GRH::Bool = false)
  OK = lllmaximal_order(K)
  dK = discriminant(OK)
  us = _p_maximal_units(K, p; OK = OK)
  rK = Hecke.unit_group_rank(OK)
  # (2)
  if !is_divisible_by(2*dK, p)
    dimimage2 = _dim_image_of_schirokauer_map(K, us, p)
    #fl, _, dimimage = _schirokauer_map_data_generic(_nf(K), us, p)
    #@assert dimimage2 == dimimage
    #@assert fl == !(dimimage < rK)
    return dimimage2 == rK, us
  end
  # (3)
  if p == 2
    lp = prime_ideals_over(OK, p)
    if length(lp) > 1
      return false, us
    end
    dimimage = _dim_image_of_eta_map(_nf(K), us, p)
    return dimimage == rK + 1, us
  end
  @assert p > 2 && is_divisible_by(dK, p)
  # (4)
  if !_check_splitting_condition(OK, p)
    return false, us
  end
  dimimage = _dim_image_of_eta_map(_nf(K), us, p)
  unitprank = Hecke.unit_group_rank(OK) + (is_divisible_by(torsion_units_order(_nf(K)), p) ? 1 : 0)
  return dimimage == unitprank, us
end

# Algorithm 15.4

@doc raw"""
    is_p_rational(K::AbsSimpleNumField, p; GRH::Bool = false)

Return whether the number field $K$ is $p$-rational at $p$.

See also [`is_quasi_p_rational`](@ref) and
[`is_real_cyclotomic_field_p_rational`](@ref) for an improved version that
works for real cyclotomic fields and does not require GRH.

# Examples

```jldoctest
julia> K, = cyclotomic_real_subfield(15);

julia> is_p_rational(K, 13)
false
```
"""
function is_p_rational(K::Union{pRationalityTestGenericCtx, AbsSimpleNumField}, p::IntegerUnion; GRH::Bool = false)
  @req is_prime(p) "p ($p) must be prime"

  OK = lllmaximal_order(K)

  # (1)
  fl = is_quasi_p_rational(K, p)
  if !fl
    return false
  end

  # (2)
  if !_is_class_number_divisible(K, p; OK = OK, GRH = GRH)
    return true
  end

  _, cK = signature(K)

  # (3)
  if cK == 0 && is_tamely_ramified(K, p) # this is at most tamely ramified
    return false
  end

  k = p == 2 ? 3 : 2
  C, = ray_class_group(OK, Dict(P => e*k for (P, e) in prime_decomposition(OK, p)); n_quo = p, GRH = GRH)
  return rank(C, p) == cK + 1
end

#function is_p_rational(K::Union{pRationalityTestGenericCtx, AbsSimpleNumField}, ps; GRH::Bool = false, fundamental_units = nothing, class_number = nothing, is_normal::Bool = false)
#  if is_normal
#    C = p_rationality_context_normal(K; GRH, fundamental_units, class_number)
#  else
#    C = p_rationality_context(K; GRH, fundamental_units, class_number)
#  end
#  res = eltype(ps)[]
#  for p in ps
#    if is_p_rational(K, ps)
#      push
#
#end

# old is_p_rational:
#
# function is_p_rational(K::Union{pRationalityTestGenericCtx, AbsSimpleNumField}, p; GRH::Bool = false)
#   OK = lllmaximal_order(K)
#   dK = discriminant(OK)
#   us = _p_maximal_units(K, p; OK = OK)
#   rK = Hecke.unit_group_rank(OK)
#   _, cK = signature(K)
#   if !is_divisible_by(2*dK, p)
#     dimimage2 = _dim_image_of_schirokauer_map(K, us, p)
#     fl, _, dimimage = _schirokauer_map_data_generic(_nf(K), us, p)
#     @assert dimimage2 == dimimage
#     @assert fl == !(dimimage < rK)
#     if dimimage < rK
#       return false
#     end
#     if !_is_class_number_divisible(K, p; OK = OK, GRH = GRH)
#       return true
#     end
#     if cK == 0
#       return false
#     end
#   end
#   if p == 2
#     lp = prime_ideals_over(OK, p)
#     if length(lp) > 1
#       return false
#     end
#     dimimage = _dim_image_of_eta_map(_nf(K), us, p)
#     if dimimage < rK + 1
#       return false
#     end
#     if !_is_class_number_divisible(K, p; OK = OK, GRH = GRH)
#       return true
#     end
#     if cK == 0 && is_tamely_ramified(K, p)
#       return false
#     end
#   end
#   # (4)
#   if !_check_splitting_condition(OK, p)
#     return false
#   end
#   dimimage = _dim_image_of_eta_map(_nf(K), us, p)
#   unitprank = Hecke.unit_group_rank(OK) + (is_divisible_by(torsion_units_order(_nf(K)), p) ? 1 : 0)
#   if dimimage < unitprank
#     return false
#   end
#   if !_is_class_number_divisible(K, p; GRH = GRH, OK = OK)
#     return true
#   end
#   if cK == 0 && is_tamely_ramified(K, p)
#     return false
#   end
#   # (5)
#   k = p == 2 ? 3 : 2
#   C, = ray_class_group(OK, Dict(P => e*k for (P, e) in prime_decomposition(OK, p)); n_quo = p, GRH = GRH)
#   return rank(C, p) == cK + 1
# end

end

import .pRational:
  is_p_rational,
  is_quasi_p_rational,
  p_rationality_context
