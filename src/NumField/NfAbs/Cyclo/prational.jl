module pRationalCyclotomic

using ..Hecke

import Nemo
import AbstractAlgebra

import ..Hecke: IntegerUnion

import ..Hecke.pRational:
  _schirokauer_map_data_generic,
  _schirokauer_map_data_minkowski_unit,
  _create_eta_map,
  _pick_automorphisms,
  _random_cyclic_subgroup

import ..Hecke.KimGoldBases:
  _sinnott_g

struct _PrimeConductorData
  n::Int
  d::Int
  orbit::Vector{Int}
  binomials::Matrix{ZZRingElem}
  defining_polynomial::Vector{ZZRingElem}
  minkowski_unit::Vector{ZZRingElem}
  conjugates::Matrix{ZZRingElem}
  inverse_conjugates::Matrix{ZZRingElem}
  minkowski_unit_is_generator::Bool
end

mutable struct pRationalityTestCtx
  k::AbsSimpleNumField
  ok::AbsSimpleNumFieldOrder
  n::Int # conductor
  mink
  strongminkowski::Bool
  aut
  cyc::Vector{AbsSimpleNumFieldElem}
  cycmC::MapFromFunc{FinGenAbGroup, FacElemMon{AbsSimpleNumField}} # unit group map
  subfields::Vector{AbsSimpleNumField}
  subfield_class_number::IdDict{AbsSimpleNumField, ZZRingElem}
  prime_conductor_orbit::Vector{Int}
  prime_conductor_data::Union{Nothing, _PrimeConductorData}

  pRationalityTestCtx() = new()
end

degree(k) = Hecke.degree(k)

function degree(T::pRationalityTestCtx)
  return Hecke.degree(T.k)
end

function pRationalityTestCtx(n::Int)
  T = pRationalityTestCtx()
  T.n = n
  k, = cyclotomic_real_subfield(n)
  T.k = k
  T.ok = lll(maximal_order(k))
  @vprint :pRationality 1 "conductor: $n: computing cyclotomic units\n"
  cyc = cyclotomic_units_totally_real(k; conductor = n)
  T.cyc = cyc
  # triger automorphism group computation
  autfull = automorphism_list(k; is_abelian = true)
  aut = _pick_automorphisms(k; is_abelian = true)
  T.aut = aut
  @vprint :pRationality 1 "conductor: $n: computing (weak) Minkowski unit\n"
  if Hecke.is_prime_power(n) && is_odd(n)
    u = _cyclotomic_units_totally_real_prime_power_conductor(k, n)
    T.strongminkowski = true
    T.mink = u
  else
    @vprint :pRationality 1 "conductor: $n: computing (weak) Minkowski unit\n"
    u = _random_cyclic_subgroup(k, aut, cyc)
    T.strongminkowski = false
    T.mink = u
  end

  T.prime_conductor_orbit = Int[]
  T.prime_conductor_data = nothing
  if is_prime(n) && is_odd(n) && degree(k) > 1
    T.prime_conductor_orbit = _prime_conductor_orbit(n, degree(k))
    T.prime_conductor_data = _prime_conductor_data(T)
  end

  T.subfield_class_number = IdDict{AbsSimpleNumField, ZZRingElem}()
  return T
end

function _prime_conductor_data(T::pRationalityTestCtx)
  K = T.k
  n = T.n
  d = degree(K)
  orbit = T.prime_conductor_orbit

  # These coefficients are independent of p. Store them as integers once;
  # reducing a cached coefficient is cheaper than rebuilding Pascal's
  # triangle in every one of the (potentially trillions of) prime tests.
  binomials = zeros(ZZRingElem, d, d)
  for m in 0:d - 1, j in 0:div(m, 2)
    binomials[m + 1, j + 1] = binomial(ZZ(m), ZZ(j))
  end

  g = defining_polynomial(K)
  defining_polynomial_coefficients = ZZRingElem[
    ZZ(coeff(g, i)) for i in 0:d
  ]
  minkowski_unit_coefficients = ZZRingElem[
    ZZ(coeff(T.mink, i)) for i in 0:d - 1
  ]

  # Cache sigma_a(u) for 1 <= a <= (n - 1)/2. In the real cyclotomic
  # field, sigma_a sends x = zeta + zeta^(-1) to
  # e_a = zeta^a + zeta^(-a), with e_{a+1} = x*e_a - e_{a-1}.
  conjugates = zeros(ZZRingElem, d, d)
  inverse_conjugates = zeros(ZZRingElem, d, d)
  x = gen(K)
  unit_is_generator = T.mink == x
  e0 = K(2)
  ea = x
  for a in 1:d
    sigma_u = unit_is_generator ? ea : hom(K, K, ea; check = false)(T.mink)
    sigma_u_inverse = inv(sigma_u)
    for i in 0:d - 1
      conjugates[a, i + 1] = ZZ(coeff(sigma_u, i))
      inverse_conjugates[a, i + 1] = ZZ(coeff(sigma_u_inverse, i))
    end
    if a < d
      e0, ea = ea, x * ea - e0
    end
  end

  return _PrimeConductorData(
    n, d, orbit, binomials, defining_polynomial_coefficients,
    minkowski_unit_coefficients, conjugates, inverse_conjugates,
    unit_is_generator
  )
end

function _prime_conductor_orbit(n::Int, d::Int)
  g = Int(primitive_root(n))
  orbit = Vector{Int}(undef, d)
  a = 1
  for i in 1:d
    orbit[i] = min(a, n - a)
    a = mod(a * g, n)
  end
  @assert allunique(orbit)
  return orbit
end

################################################################################
#
#  UInt128 arithmetic modulo p^2 for AbstractAlgebra polynomials
#
################################################################################

# This is deliberately a minimal coefficient ring. Elements are canonical
# representatives in a UInt128, while the parent remembers p and p^2. A
# product cannot be formed directly in UInt128: it may require up to 252 bits.
# Instead, write a = a0 + p*a1 and b = b0 + p*b1. Then modulo p^2,
#
#   a*b = r0 + p*(c0 + a0*b1 + a1*b0),
#
# where a0*b0 = r0 + p*c0. Every product on the right fits in UInt128 when
# p fits in a positive Int. The wrapper supplies the small AbstractAlgebra
# interface needed by Generic.Poly and its polynomial arithmetic.

struct _UInt128ModRing <: Ring
  p::UInt128
  p2::UInt128

  function _UInt128ModRing(p::Int)
    @assert 0 < p && nbits(p) <= 63
    pu = UInt128(p)
    return new(pu, pu^2)
  end
end

struct _UInt128ModRingElem <: RingElem
  data::UInt128
  parent::_UInt128ModRing
end

AbstractAlgebra.parent_type(::Type{_UInt128ModRingElem}) = _UInt128ModRing
AbstractAlgebra.elem_type(::Type{_UInt128ModRing}) = _UInt128ModRingElem
AbstractAlgebra.parent(a::_UInt128ModRingElem) = a.parent

AbstractAlgebra.is_domain_type(::Type{_UInt128ModRingElem}) = false
AbstractAlgebra.is_exact_type(::Type{_UInt128ModRingElem}) = true
AbstractAlgebra.is_trivial(R::_UInt128ModRing) = R.p2 == UInt128(1)
AbstractAlgebra.characteristic(R::_UInt128ModRing) = ZZ(R.p2)

(R::_UInt128ModRing)() = _UInt128ModRingElem(0, R)
(R::_UInt128ModRing)(a::UInt128) = _UInt128ModRingElem(a % R.p2, R)
(R::_UInt128ModRing)(a::UInt) = R(UInt128(a))
function (R::_UInt128ModRing)(a::Int)
  if a >= 0
    return R(UInt128(a))
  end
  b = UInt128(-(a + 1)) + 1
  b %= R.p2
  return _UInt128ModRingElem(iszero(b) ? b : R.p2 - b, R)
end
function (R::_UInt128ModRing)(a::ZZRingElem)
  return R(UInt128(mod(a, ZZ(R.p2))))
end
function (R::_UInt128ModRing)(a::_UInt128ModRingElem)
  parent(a) === R || error("Operation on incompatible objects")
  return a
end

Base.zero(R::_UInt128ModRing) = R()
Base.one(R::_UInt128ModRing) = _UInt128ModRingElem(1, R)
Base.zero(a::_UInt128ModRingElem) = zero(parent(a))
Base.one(a::_UInt128ModRingElem) = one(parent(a))
Base.iszero(a::_UInt128ModRingElem) = iszero(a.data)
Base.isone(a::_UInt128ModRingElem) = a.data == UInt128(1)

Base.copy(a::_UInt128ModRingElem) = a
Base.deepcopy_internal(a::_UInt128ModRingElem, ::IdDict) = a

function Base.:(==)(a::_UInt128ModRingElem, b::_UInt128ModRingElem)
  return parent(a) === parent(b) && a.data == b.data
end

Base.isequal(a::_UInt128ModRingElem, b::_UInt128ModRingElem) =
  parent(a) === parent(b) && a.data == b.data

Base.hash(a::_UInt128ModRingElem, h::UInt) =
  hash(a.data, hash(objectid(parent(a)), h))

@inline function Base.:+(a::_UInt128ModRingElem, b::_UInt128ModRingElem)
  R = parent(a)
  parent(b) === R || error("Operation on incompatible objects")
  c = a.data + b.data
  c >= R.p2 && (c -= R.p2)
  return _UInt128ModRingElem(c, R)
end

@inline function Base.:-(a::_UInt128ModRingElem, b::_UInt128ModRingElem)
  R = parent(a)
  parent(b) === R || error("Operation on incompatible objects")
  c = a.data >= b.data ? a.data - b.data : R.p2 - (b.data - a.data)
  return _UInt128ModRingElem(c, R)
end

@inline function Base.:-(a::_UInt128ModRingElem)
  return iszero(a) ? a : _UInt128ModRingElem(parent(a).p2 - a.data, parent(a))
end

@inline function Base.:*(a::_UInt128ModRingElem, b::_UInt128ModRingElem)
  R = parent(a)
  parent(b) === R || error("Operation on incompatible objects")
  p = R.p

  a1, a0 = divrem(a.data, p)
  b1, b0 = divrem(b.data, p)
  c0, r0 = divrem(a0 * b0, p)
  r1 = (c0 + a0 * b1 + a1 * b0) % p
  return _UInt128ModRingElem(r0 + p * r1, R)
end

AbstractAlgebra.mul!(::_UInt128ModRingElem, a::_UInt128ModRingElem,
                     b::_UInt128ModRingElem) = a * b
AbstractAlgebra.add!(::_UInt128ModRingElem, a::_UInt128ModRingElem,
                     b::_UInt128ModRingElem) = a + b
AbstractAlgebra.add!(a::_UInt128ModRingElem, b::_UInt128ModRingElem) = a + b
AbstractAlgebra.sub!(::_UInt128ModRingElem, a::_UInt128ModRingElem,
                     b::_UInt128ModRingElem) = a - b
AbstractAlgebra.neg!(a::_UInt128ModRingElem) = -a
AbstractAlgebra.neg!(::_UInt128ModRingElem, a::_UInt128ModRingElem) = -a
AbstractAlgebra.zero!(a::_UInt128ModRingElem) = zero(a)

function Base.inv(a::_UInt128ModRingElem)
  isone(a) && return a
  error("inverse is not implemented for _UInt128ModRingElem")
end

function AbstractAlgebra.divexact(a::_UInt128ModRingElem,
                                  b::_UInt128ModRingElem;
                                  check::Bool = true)
  isone(b) && return a
  error("division is only implemented by one for _UInt128ModRingElem")
end

Base.show(io::IO, R::_UInt128ModRing) =
  print(io, "UInt128 residue ring modulo ", R.p2)
Base.show(io::IO, a::_UInt128ModRingElem) = print(io, a.data)

################################################################################
#
#  Two-limb arithmetic modulo p^2
#
################################################################################

# FLINT's mpn_mod generic ring is specialized for fixed moduli occupying
# 2--16 machine limbs. Nemo does not currently wrap this ring, so use the
# small part of the public FLINT gr interface that is needed for polynomial
# exponentiation modulo p^2. The C-compatible prefixes of these types mirror
# gr_ctx_struct and gr_poly_struct, respectively.

const _prational_libflint = Nemo.libflint

mutable struct _MpnModCtx
  data::NTuple{6, UInt}
  which_ring::UInt
  sizeof_elem::Int
  methods::Ptr{Cvoid}
  size_limit::UInt
  cleared::Bool

  function _MpnModCtx(n::ZZRingElem)
    z = new(ntuple(_ -> UInt(0), 6), UInt(0), 0, C_NULL, UInt(0), false)
    status = @ccall _prational_libflint.gr_ctx_init_mpn_mod(
      z::Ref{_MpnModCtx}, n::Ref{ZZRingElem}
    )::Cint
    status == 0 || error("FLINT gr_ctx_init_mpn_mod failed with status $status")
    finalizer(_clear!, z)
    return z
  end
end

function _clear!(z::_MpnModCtx)
  if !z.cleared
    @ccall _prational_libflint.mpn_mod_ctx_clear(z::Ref{_MpnModCtx})::Cvoid
    z.cleared = true
  end
  return nothing
end

mutable struct _MpnModPoly
  coeffs::Ptr{Cvoid}
  alloc::Int
  length::Int
  ctx::_MpnModCtx
  cleared::Bool

  function _MpnModPoly(ctx::_MpnModCtx)
    z = new(C_NULL, 0, 0, ctx, false)
    @ccall _prational_libflint.gr_poly_init(
      z::Ref{_MpnModPoly}, ctx::Ref{_MpnModCtx}
    )::Cvoid
    finalizer(_clear!, z)
    return z
  end
end

function _clear!(z::_MpnModPoly)
  if !z.cleared
    @ccall _prational_libflint.gr_poly_clear(
      z::Ref{_MpnModPoly}, z.ctx::Ref{_MpnModCtx}
    )::Cvoid
    z.cleared = true
  end
  return nothing
end

function _setcoeff!(a::_MpnModPoly, i::Int, x::ZZRingElem)
  status = @ccall _prational_libflint.gr_poly_set_coeff_fmpz(
    a::Ref{_MpnModPoly}, i::Int, x::Ref{ZZRingElem},
    a.ctx::Ref{_MpnModCtx}
  )::Cint
  status == 0 || error("FLINT gr_poly_set_coeff_fmpz failed with status $status")
  return a
end

function _powermod_two_limb!(z::_MpnModPoly, a::_MpnModPoly,
                             e::ZZRingElem, modulus::_MpnModPoly)
  # A seven-bit sliding window is near-optimal for the several-thousand-bit
  # exponents occurring at the target conductor. Preinvert the fixed
  # polynomial modulus once for all reductions in this exponentiation.
  reversed = _MpnModPoly(z.ctx)
  inverse = _MpnModPoly(z.ctx)
  try
    status = @ccall _prational_libflint.gr_poly_reverse(
      reversed::Ref{_MpnModPoly}, modulus::Ref{_MpnModPoly},
      modulus.length::Int, z.ctx::Ref{_MpnModCtx}
    )::Cint
    status == 0 || error("FLINT gr_poly_reverse failed with status $status")

    status = @ccall _prational_libflint.gr_poly_inv_series(
      inverse::Ref{_MpnModPoly}, reversed::Ref{_MpnModPoly},
      modulus.length::Int, z.ctx::Ref{_MpnModCtx}
    )::Cint
    status == 0 || error("FLINT gr_poly_inv_series failed with status $status")

    status = @ccall _prational_libflint.gr_poly_powmod_fmpz_sliding_preinv(
      z::Ref{_MpnModPoly}, a::Ref{_MpnModPoly}, e::Ref{ZZRingElem},
      UInt(7)::UInt, modulus::Ref{_MpnModPoly},
      inverse::Ref{_MpnModPoly}, z.ctx::Ref{_MpnModCtx}
    )::Cint
    status == 0 ||
      error("FLINT gr_poly_powmod_fmpz_sliding_preinv failed with status $status")
  finally
    _clear!(inverse)
    _clear!(reversed)
  end
  return z
end

function _powermod_two_limb_ui!(z::_MpnModPoly, a::_MpnModPoly,
                                e::UInt, modulus::_MpnModPoly)
  reversed = _MpnModPoly(z.ctx)
  inverse = _MpnModPoly(z.ctx)
  try
    status = @ccall _prational_libflint.gr_poly_reverse(
      reversed::Ref{_MpnModPoly}, modulus::Ref{_MpnModPoly},
      modulus.length::Int, z.ctx::Ref{_MpnModCtx}
    )::Cint
    status == 0 || error("FLINT gr_poly_reverse failed with status $status")

    status = @ccall _prational_libflint.gr_poly_inv_series(
      inverse::Ref{_MpnModPoly}, reversed::Ref{_MpnModPoly},
      modulus.length::Int, z.ctx::Ref{_MpnModCtx}
    )::Cint
    status == 0 || error("FLINT gr_poly_inv_series failed with status $status")

    status = @ccall _prational_libflint.gr_poly_powmod_ui_binexp_preinv(
      z::Ref{_MpnModPoly}, a::Ref{_MpnModPoly}, e::UInt,
      modulus::Ref{_MpnModPoly}, inverse::Ref{_MpnModPoly},
      z.ctx::Ref{_MpnModCtx}
    )::Cint
    status == 0 ||
      error("FLINT gr_poly_powmod_ui_binexp_preinv failed with status $status")
  finally
    _clear!(inverse)
    _clear!(reversed)
  end
  return z
end

function _powermod_x_two_limb!(z::_MpnModPoly, e::ZZRingElem,
                               modulus::_MpnModPoly)
  reversed = _MpnModPoly(z.ctx)
  inverse = _MpnModPoly(z.ctx)
  try
    status = @ccall _prational_libflint.gr_poly_reverse(
      reversed::Ref{_MpnModPoly}, modulus::Ref{_MpnModPoly},
      modulus.length::Int, z.ctx::Ref{_MpnModCtx}
    )::Cint
    status == 0 || error("FLINT gr_poly_reverse failed with status $status")

    status = @ccall _prational_libflint.gr_poly_inv_series(
      inverse::Ref{_MpnModPoly}, reversed::Ref{_MpnModPoly},
      modulus.length::Int, z.ctx::Ref{_MpnModCtx}
    )::Cint
    status == 0 || error("FLINT gr_poly_inv_series failed with status $status")

    status = @ccall _prational_libflint.gr_poly_powmod_x_fmpz_preinv(
      z::Ref{_MpnModPoly}, e::Ref{ZZRingElem}, modulus::Ref{_MpnModPoly},
      inverse::Ref{_MpnModPoly}, z.ctx::Ref{_MpnModCtx}
    )::Cint
    status == 0 ||
      error("FLINT gr_poly_powmod_x_fmpz_preinv failed with status $status")
  finally
    _clear!(inverse)
    _clear!(reversed)
  end
  return z
end

function _coeff_two_limbs!(tmp::Vector{UInt}, a::_MpnModPoly, i::Int)
  @assert length(tmp) == 2
  status = @ccall _prational_libflint.gr_poly_get_coeff_scalar(
    tmp::Ptr{UInt}, a::Ref{_MpnModPoly}, i::Int,
    a.ctx::Ref{_MpnModCtx}
  )::Cint
  status == 0 || error("FLINT gr_poly_get_coeff_scalar failed with status $status")
  return UInt128(tmp[1]) | (UInt128(tmp[2]) << 64)
end

function _powermod_x_single_limb(e::UInt, modulus::zzModPolyRingElem)
  reversed = reverse(modulus, length(modulus))
  inverse = parent(modulus)()
  @ccall _prational_libflint.nmod_poly_inv_series(
    inverse::Ref{zzModPolyRingElem}, reversed::Ref{zzModPolyRingElem},
    length(modulus)::Int
  )::Cvoid
  z = parent(modulus)()
  @ccall _prational_libflint.nmod_poly_powmod_x_ui_preinv(
    z::Ref{zzModPolyRingElem}, e::UInt, modulus::Ref{zzModPolyRingElem},
    inverse::Ref{zzModPolyRingElem}
  )::Cvoid
  return z
end

# Fast Schirokauer rank computation for K = Q(zeta_n)^+ with n an odd prime.
# The conjugates e_a = zeta_n^a + zeta_n^(-a), indexed modulo sign, form a
# normal basis of K. Thus the Galois conjugates of one Schirokauer image are
# the cyclic shifts of its coefficient vector c. Their rank is the rank of
# multiplication by c(X) on F_p[X]/(X^d - 1), namely
#
#   d - degree(gcd(c(X), X^d - 1)).
#
# The norm of the Minkowski unit is +/-1, so c(1) = 0. The required unit rank
# d - 1 is therefore attained precisely when the gcd has degree one.
function _schirokauer_map_data_prime_conductor(T::pRationalityTestCtx, p)
  if 2 * nbits(p) < 63
    return _schirokauer_map_data_prime_conductor(T, p, p^2)
  elseif p isa Int && 32 < nbits(p) <= 63
    return _schirokauer_map_data_prime_conductor_two_limb(T, p)
  else
    return _schirokauer_map_data_prime_conductor(T, p, ZZ(p)^2)
  end
end

function _schirokauer_map_data_prime_conductor(T::pRationalityTestCtx, p, p2)
  K = T.k
  n = T.n
  d = degree(K)
  @assert is_prime(n) && is_odd(n) && d == div(n - 1, 2)
  @assert !is_divisible_by(2 * n, p)
  @assert T.strongminkowski && T.mink isa AbsSimpleNumFieldElem

  # In the real cyclotomic field, the residue degree is the order of p in
  # (Z/nZ)^*/{+/-1}. Since n is prime, this is ord_n(p), divided by two when
  # the latter is even.
  ord = modord(Int(mod(p, n)), n)
  f = is_even(ord) ? div(ord, 2) : ord

  g = defining_polynomial(K)
  Zellx, = polynomial_ring(residue_ring(ZZ, p; cached = false)[1]; cached = false)
  Zell2x, = polynomial_ring(residue_ring(ZZ, p2; cached = false)[1]; cached = false)
  ZZy, = polynomial_ring(ZZ, :y; cached = false)
  gmodell2 = change_base_ring(base_ring(Zell2x), g; parent = Zell2x)

  u_mod_ell2 = Zell2x(Hecke.__mod(T.mink, ZZ(p2)))
  num = powermod(u_mod_ell2, ZZ(p)^f - 1, gmodell2) - 1
  q = change_base_ring(base_ring(Zellx), divexact!(lift(ZZy, num), p); parent = Zellx)
  return _schirokauer_rank_prime_conductor(T, q)
end

# Separate Frobenius/delta path. The direct p^f - 1 implementations above and
# below are intentionally retained as reference implementations and fallbacks.
function _schirokauer_map_data_prime_conductor_delta(
    T::pRationalityTestCtx, p)
  data = T.prime_conductor_data
  @assert data !== nothing
  @assert !is_divisible_by(2 * data.n, p)
  @assert T.strongminkowski && T.mink isa AbsSimpleNumFieldElem
  if p isa Int && 32 < nbits(p) <= 63
    return _schirokauer_map_data_prime_conductor_delta_two_limb(data, p)
  elseif 2 * nbits(p) < 63
    return _schirokauer_map_data_prime_conductor_delta(data, p, p^2)
  else
    return _schirokauer_map_data_prime_conductor_delta(data, p, ZZ(p)^2)
  end
end

function _schirokauer_map_data_prime_conductor_delta(
    data::_PrimeConductorData, p, p2)
  n = data.n
  d = data.d
  afwd = Int(mod(p, n))
  a = min(afwd, n - afwd)

  R2 = residue_ring(ZZ, p2; cached = false)[1]
  R2x, = polynomial_ring(R2, :x; cached = false)
  gmod2 = R2x()
  umod2 = R2x()
  sigma_umod2 = R2x()
  for i in 0:d
    setcoeff!(gmod2, i, data.defining_polynomial[i + 1])
  end
  for i in 0:d - 1
    setcoeff!(umod2, i, data.minkowski_unit[i + 1])
    setcoeff!(sigma_umod2, i, data.conjugates[a, i + 1])
  end

  upow = data.minkowski_unit_is_generator && p isa Int && p2 isa Int ?
    _powermod_x_single_limb(UInt(p), gmod2) :
    powermod(umod2, ZZ(p), gmod2)
  num = upow - sigma_umod2
  ZZy, = polynomial_ring(ZZ, :y; cached = false)
  R = residue_ring(ZZ, p; cached = false)[1]
  Rx, = polynomial_ring(R, :x; cached = false)
  q0 = change_base_ring(
    R, divexact!(lift(ZZy, num), p); parent = Rx
  )
  inverse_sigma_umod = Rx()
  gmod = Rx()
  for i in 0:d - 1
    setcoeff!(inverse_sigma_umod, i, data.inverse_conjugates[a, i + 1])
  end
  for i in 0:d
    setcoeff!(gmod, i, data.defining_polynomial[i + 1])
  end
  q = mulmod(q0, inverse_sigma_umod, gmod)
  return _schirokauer_rank_prime_conductor(data, q)
end

function _powermod_uint128(a, e::ZZRingElem, modulus; window::Int = 7)
  @assert e >= 0
  @assert 1 <= window <= 8
  iszero(e) && return one(parent(a))

  # Odd powers a, a^3, ..., a^(2^window - 1).
  odd_powers = Vector{typeof(a)}(undef, 1 << (window - 1))
  odd_powers[1] = mod(a, modulus)
  a2 = mulmod(odd_powers[1], odd_powers[1], modulus)
  for i in 2:length(odd_powers)
    odd_powers[i] = mulmod(odd_powers[i - 1], a2, modulus)
  end

  z = one(parent(a))
  i = nbits(e) - 1
  while i >= 0
    if !tstbit(e, i)
      z = mulmod(z, z, modulus)
      i -= 1
      continue
    end

    lo = max(0, i - window + 1)
    while !tstbit(e, lo)
      lo += 1
    end

    w = 0
    for j in i:-1:lo
      w = (w << 1) | Int(tstbit(e, j))
    end
    for _ in lo:i
      z = mulmod(z, z, modulus)
    end
    z = mulmod(z, odd_powers[(w + 1) >> 1], modulus)
    i = lo - 1
  end
  return z
end

function _schirokauer_map_data_prime_conductor_uint128(
    T::pRationalityTestCtx, p::Int)
  K = T.k
  n = T.n
  d = degree(K)
  @assert is_prime(n) && is_odd(n) && d == div(n - 1, 2)
  @assert !is_divisible_by(2 * n, p)
  @assert T.strongminkowski && T.mink isa AbsSimpleNumFieldElem
  @assert 32 < nbits(p) <= 63

  ord = modord(mod(p, n), n)
  f = is_even(ord) ? div(ord, 2) : ord
  pzz = ZZ(p)
  p2 = pzz^2

  R128 = _UInt128ModRing(p)
  R128x, = polynomial_ring(R128, :x; cached = false)
  gmod = R128x()
  umod = R128x()
  g = defining_polynomial(K)
  u = Hecke.__mod(T.mink, p2)
  for i in 0:degree(g)
    setcoeff!(gmod, i, R128(ZZ(coeff(g, i))))
  end
  for i in 0:d - 1
    setcoeff!(umod, i, R128(ZZ(coeff(u, i))))
  end

  result = _powermod_uint128(umod, pzz^f - 1, gmod)

  R = residue_ring(ZZ, p; cached = false)[1]
  Rx, = polynomial_ring(R, :x; cached = false)
  q = Rx()
  pu = UInt128(p)
  for i in 0:d - 1
    value = coeff(result, i).data
    if i == 0
      @assert value % pu == 1
      value -= 1
    else
      @assert value % pu == 0
    end
    setcoeff!(q, i, UInt(value ÷ pu))
  end

  return _schirokauer_rank_prime_conductor(T, q)
end

function _schirokauer_map_data_prime_conductor_two_limb(
    T::pRationalityTestCtx, p::Int)
  K = T.k
  n = T.n
  d = degree(K)
  @assert is_prime(n) && is_odd(n) && d == div(n - 1, 2)
  @assert !is_divisible_by(2 * n, p)
  @assert T.strongminkowski && T.mink isa AbsSimpleNumFieldElem
  @assert 32 < nbits(p) <= 63

  ord = modord(mod(p, n), n)
  f = is_even(ord) ? div(ord, 2) : ord
  pzz = ZZ(p)
  p2 = pzz^2
  ctx = _MpnModCtx(p2)
  @assert ctx.sizeof_elem == 2 * sizeof(UInt)

  g = defining_polynomial(K)
  u = Hecke.__mod(T.mink, p2)
  gmod = _MpnModPoly(ctx)
  umod = _MpnModPoly(ctx)
  result = _MpnModPoly(ctx)

  q = try
    for i in 0:degree(g)
      _setcoeff!(gmod, i, ZZ(coeff(g, i)))
    end
    for i in 0:d - 1
      _setcoeff!(umod, i, ZZ(coeff(u, i)))
    end

    _powermod_two_limb!(result, umod, pzz^f - 1, gmod)

    R = residue_ring(ZZ, p; cached = false)[1]
    Rx, = polynomial_ring(R, :x; cached = false)
    q = Rx()
    tmp = Vector{UInt}(undef, 2)
    pu = UInt128(p)
    for i in 0:d - 1
      value = _coeff_two_limbs!(tmp, result, i)
      if i == 0
        @assert value % pu == 1
        value -= 1
      else
        @assert value % pu == 0
      end
      setcoeff!(q, i, UInt(value ÷ pu))
    end
    q
  finally
    _clear!(result)
    _clear!(umod)
    _clear!(gmod)
    _clear!(ctx)
  end

  return _schirokauer_rank_prime_conductor(T, q)
end

# Let f be the residue degree and let S(u) = (u^(p^f - 1) - 1)/p be the
# Schirokauer image. Reduction of sigma_p is p-th powering on O_K/pO_K. If
# y = sigma_p^(-1)(u), then y = u^(p^(f - 1)) modulo p. For odd p, congruent
# elements modulo p have congruent p-th powers modulo p^2, hence
#
#   sigma_p(S(u)) = (u^p - sigma_p(u))/(p*sigma_p(u))  modulo p.
#
# The numerator on the right is divisible by p already over O_K. Since a
# Galois automorphism preserves the rank of the orbit of S(u), it is enough
# to compute this conjugate. This replaces an exponent with f*nbits(p) bits by
# the single nbits(p)-bit exponent p. It also orients the formula so that the
# target unit u = x can use FLINT's specialized powmod-x kernel.
function _schirokauer_map_data_prime_conductor_delta_two_limb(
    T::pRationalityTestCtx, p::Int)
  data = T.prime_conductor_data
  @assert data !== nothing
  @assert !is_divisible_by(2 * data.n, p)
  @assert T.strongminkowski && T.mink isa AbsSimpleNumFieldElem
  @assert 32 < nbits(p) <= 63
  return _schirokauer_map_data_prime_conductor_delta_two_limb(data, p)
end

function _schirokauer_map_data_prime_conductor_delta_two_limb(
    data::_PrimeConductorData, p::Int)
  n = data.n
  d = data.d
  afwd = Int(mod(p, n))
  a = min(afwd, n - afwd)
  pzz = ZZ(p)
  p2 = pzz^2
  ctx = _MpnModCtx(p2)
  @assert ctx.sizeof_elem == 2 * sizeof(UInt)

  gmod = _MpnModPoly(ctx)
  umod2 = _MpnModPoly(ctx)
  result = _MpnModPoly(ctx)

  q = try
    for i in 0:d
      _setcoeff!(gmod, i, data.defining_polynomial[i + 1])
    end
    if data.minkowski_unit_is_generator
      _powermod_x_two_limb!(result, pzz, gmod)
    else
      for i in 0:d - 1
        _setcoeff!(umod2, i, data.minkowski_unit[i + 1])
      end
      _powermod_two_limb_ui!(result, umod2, UInt(p), gmod)
    end

    R = residue_ring(ZZ, p; cached = false)[1]
    Rx, = polynomial_ring(R, :x; cached = false)
    q0 = Rx()
    inverse_sigma_umod = Rx()
    tmp = Vector{UInt}(undef, 2)
    pu = UInt128(p)
    p2u = pu^2
    for i in 0:d - 1
      value = _coeff_two_limbs!(tmp, result, i)
      sigma_coefficient = data.conjugates[a, i + 1]
      sigma_ui = UInt128(mod(sigma_coefficient, p2))
      delta = value >= sigma_ui ? value - sigma_ui : p2u - (sigma_ui - value)
      @assert delta % pu == 0
      setcoeff!(q0, i, UInt(delta ÷ pu))
      setcoeff!(inverse_sigma_umod, i, data.inverse_conjugates[a, i + 1])
    end
    gmodp = Rx()
    for i in 0:d
      setcoeff!(gmodp, i, data.defining_polynomial[i + 1])
    end
    mulmod(q0, inverse_sigma_umod, gmodp)
  finally
    _clear!(result)
    _clear!(umod2)
    _clear!(gmod)
    _clear!(ctx)
  end

  return _schirokauer_rank_prime_conductor(data, q)
end

function _schirokauer_rank_prime_conductor(T::pRationalityTestCtx, q)
  data = T.prime_conductor_data
  @assert data !== nothing
  return _schirokauer_rank_prime_conductor(data, q)
end

function _schirokauer_rank_prime_conductor(data::_PrimeConductorData, q)
  d = data.d
  # Convert from the power basis 1, x, ..., x^(d - 1) to
  # 1, e_1, ..., e_(d - 1), using
  #
  #   x^m = sum_j binomial(m, j) * e_(m - 2j),
  #
  # where the term with m - 2j = 0 is the constant binomial(m, m/2). The
  # integer binomial coefficients are cached on the fixed-conductor context.
  R = base_ring(parent(q))
  b = [zero(R) for _ in 1:d - 1]
  a0 = zero(R)
  for m in 0:d - 1
    qm = coeff(q, m)
    for j in 0:div(m, 2)
      k = m - 2 * j
      bmj = R(data.binomials[m + 1, j + 1])
      if k == 0
        a0 += qm * bmj
      else
        b[k] += qm * bmj
      end
    end
  end

  # For prime n, 1 + e_1 + ... + e_d = 0. Replace the remaining constant
  # coefficient and order the normal basis by powers of a primitive root.
  Rx, X = polynomial_ring(R, :X; cached = false)
  c = Rx()
  for i in 1:d
    k = data.orbit[i]
    setcoeff!(c, i - 1, k < d ? b[k] - a0 : -a0)
  end
  @assert is_zero(c(one(R)))

  gcd_degree = degree(gcd(c, X^d - 1))
  image_rank = d - gcd_degree
  unit_rank = d - 1
  return image_rank == unit_rank, unit_rank - image_rank, image_rank
end

function _p_rationality_of_real_cyclotomic_quick_check_at_2(T)
  n = T.n
  nps = prime_divisors(n)
  if n == 2^valuation(n, 2) || n == 2^valuation(n, 2) * 3 || n == 2^valuation(n, 2) * 5
    return true
  end
  if any(l -> mod(l, 8) == 1, nps)
    return false
  end
  if any(l -> mod(l, 8) == 7 && mod(n, 4l) == 0, nps)
    return false
  end
  if !allunique([mod(l, 4) for l in nps if l > 2])
    return false
  end
  if _sinnott_g(n) >= 3
    return false
  end
  if length(prime_ideals_over(maximal_order(T.k), 2)) > 1
    return false
  end
  return nothing
end

# per prime version
function _p_rationality_of_real_cyclotomic_check_per_prime(T, p)
  n = T.n

  if p == 2
    @vprint :pRationality 1 "conductor: $n: prime $p: quick check for n = $(factor(n))\n"
    fl = _p_rationality_of_real_cyclotomic_quick_check_at_2(T)
    @vprint :pRationality 1 "conductor: $n: prime $p: quick check at 2: $fl\n"
    if fl isa Bool
      return fl
    end
  end

  @vprint :pRationality 1 "conductor: $n: prime $p: check Schirokauer map on cyclotomic units\n"
  if !is_divisible_by(2*n, p)
    if T.prime_conductor_data !== nothing
      # Use the cached Frobenius-delta path by default. The direct
      # prime-conductor methods remain available as separate references.
      fl, = _schirokauer_map_data_prime_conductor_delta(T, p)
    else
      fl, = _schirokauer_map_data_minkowski_unit(T.k, T.mink, p, T.aut; is_abelian = true, new = true)
    end
    if fl
      @vprint :pRationality 1 "conductor: $n: prime $p: Schirokauer map injective; p-rationality established\n"
      return true
    end
    @vprint :pRationality 1 "conductor: $n: prime $p: p does not divide (2*n)\n"
    if T.strongminkowski
      return false
    end
    fl, = _schirokauer_map_data_generic(T.k, T.cyc, p)
    return fl
  end

  return _is_prational_cyclotomic_via_eta_map(T, p)
end

function _is_prational_cyclotomic_via_eta_map(T, p)
  k = T.k
  n = T.n
  @vprint :pRationality 1 "conductor: $n: prime $p\n"
  ok = lll(maximal_order(k))
  # we need to check the condition on the p-th roots of unity
  if mod(2*n, p) == 0
    # p divides 2 * d_K
    if p == 2
      g = length(prime_ideals_over(ok, 2))
      @vprint :pRationality 1 "conductor: $n: prime $p: number of primes above 2: $g\n"
      if g > 1
        @vprint :pRationality 1 "conductor: $n: prime $p: returning false\n"
        return false
      end
    else
      @vprint :pRationality 1 "conductor: $n: prime $p: check splitting of p in Q(z_n)|Q(z_n)^+\n"
      # need to look at K(zeta_p)|K = Q(zeta_n)|Q(zeta_n)^+, a quadratic extension
      K, = cyclotomic_field(n; cached = false)
      g = length(prime_decomposition_type(ok, p)) # g primes over p in Q(zeta_n)^+
      gg = length(prime_decomposition_type(maximal_order(K), p)) # gg primes over p in Q(zeta_n)
      @vprint :pRationality 1 "conductor: $n: prime $p: number of primes above of p in Q(z_n)^+: $g\n"
      @vprint :pRationality 1 "conductor: $n: prime $p: number of primes above of p in Q(z_n): $gg\n"
      if gg > g
        @assert gg == 2 * g
        @vprint :pRationality 1 "conductor: $n: prime $p: returning false\n"
        # the primes are totally split
        return false
      end
    end
  end
  # p does not divide 2*n, so condition (b) is satisfied
  # we just check if the eta map on C/C^p is injective
  @vprint :pRationality 1 "conductor: $n: prime $p: creating eta map\n"
  U, f = _create_eta_map(k, p)
  prankcyclo = p == 2 ? degree(k) - 1 + 1 : degree(k) - 1
  u = FacElem.(T.cyc)
  @vprint :pRationality 1 "conductor: $n: prime $p: computing image of cyclotomic units\n"
  V, = sub(U, f.(u))
  r = rank(V, p)
  @vprint :pRationality 1 "conductor: $n: prime $p: p-rank is $r (cyclotomic units have p-rank $prankcyclo)\n"
  @vprint :pRationality 1 "conductor: $n: prime $p: returning $(r == prankcyclo)\n"
  return r == prankcyclo
end

@doc raw"""
    is_real_cyclotomic_field_p_rational(n::Int, p; GRH::Bool = false)

Return whether the maximal real subfield of the cyclotomic field of conductor
$n$ is $p$-rational at $p$. The conductor $n$ must not be congruent to $2$
modulo $4$.

See also [`is_quasi_p_rational`](@ref) and [`is_p_rational`](@ref) for versions
that work for any number field.

# Examples

```jldoctest
julia> is_real_cyclotomic_field_p_rational(15, 13)
false

julia> p = ZZ(2)^127 - 1;

julia> is_real_cyclotomic_field_p_rational(5, p)
true
```
"""
function is_real_cyclotomic_field_p_rational(n, p::IntegerUnion)
  @req mod(n, 4) != 2 "conductor n ($n) must not be congruent to 2 modulo 4"
  @req is_prime(p) "p ($p) must be prime"
  return _is_real_cyclotomic_field_p_rational(n, Nemo.flintify(p))
end

function _is_real_cyclotomic_field_p_rational(n, p)
  T = pRationalityTestCtx(n)
  return _p_rationality_of_real_cyclotomic_check_per_prime(T, p)
end

function _cyclotomic_units_totally_real_prime_power_conductor(K, q)
  Zx = Hecke.Globals.Zx
  x = gen(Zx)
  @assert is_zero(cos_minpoly(q, gen(Zx))(gen(K)))
  xi = gen(K)

  # Schoof, "Class numbers of real cyclotomic fields of prime conductor", Section 2
  # gives the following formula:
  # eta = zeta^(g) - zeta^(-g)/zeta - zeta^-1 = sin(2pi g/n)/sin(2p/n) = U_{g - 1}(cos(2pi/n))
  # then Cyc is generated by the G-orbit of eta,
  # where G = Gal(K/Q).
  # This is slightly different from Washington, who takes sin(pi g/n)(sin(2pi/n)
  # but they differ only by a choice of primitive root of unity. If you take z' with z'^2 = z
  # in Washington, you get Schoofs unit.

  @assert Hecke.is_prime_power(q)

  U, mU = unit_group(residue_ring(ZZ, q, cached = false)[1])
  @assert ngens(U) == 1
  g = Int(lift(mU(U[1])))


  p1 = numerator(chebyshev_u(g - 1, x)(x//2))
  eta = p1(xi)
  return eta
end

# p-rationality check for fixed field

function _check_prationality_of_cyclotomic_units_up_to(n, bound, callback = nothing)
  T = pRationalityTestCtx(n)
  res = Int[]
  for (i, ell) in enumerate(PrimesSet(2, bound))
    if !(callback isa Nothing)
      callback(i, ell, res)
    end
    fl = _p_rationality_of_real_cyclotomic_check_per_prime(T, ell)
    if fl
      continue
    end
    push!(res, ell)
  end
  return res
end

end

import .pRationalCyclotomic:
  is_real_cyclotomic_field_p_rational,
  _check_prationality_of_cyclotomic_units_up_to
