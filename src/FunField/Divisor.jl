################################################################################
#
#  Constructors
#
################################################################################


mutable struct Divisor{S <: Generic.AbsSimpleFunctionField, T1 <: PolyRing, T2 <: KInftyRing}
  function_field::S

  #Free representation
  finite_support::Dict{GenOrdIdl{S, T1}, Int}
  infinite_support::Dict{GenOrdIdl{S, T2}, Int}

  #Inverse ideal representation
  finite_inv_ideal::GenOrdFracIdl{S, T1}
  infinite_inv_ideal::GenOrdFracIdl{S, T2}

  #Projective representation: D = D_red + r*(x)_inf - div(a)
  D_red::Divisor{S, T1, T2}
  r::Int
  a::FacElem

  #Caching the old representation
  finite_ideal::GenOrdFracIdl{S, T1}
  infinite_ideal::GenOrdFracIdl{S, T2}

  function Divisor{S, T1, T2}(F::S) where {S, T1, T2}
    r = new{S, T1, T2}()
    r.function_field = F
    return r
  end
end

#The empty divisor type for F. Helper function for construction
function _empty_divisor(F::Generic.AbsSimpleFunctionField{T, U}) where {T, U}
  return Divisor{typeof(F), parent_type(U), KInftyRing{T, U}}(F)
end

@attr Divisor{Generic.AbsSimpleFunctionField{T, U}, parent_type(U), KInftyRing{T, U}} function 
trivial_divisor(F::Generic.AbsSimpleFunctionField{T, U}) where {T, U}
  return _divisor_from_support(F, _empty_support(finite_maximal_order(F)),
                                  _empty_support(infinite_maximal_order(F)))
end

function Divisor(I::GenOrdFracIdl{S, T1}, J::GenOrdFracIdl{S, T2}) where {S, T1, T2}
  K = function_field(order(I))
  @req K == function_field(order(J)) "Ideals need to belong to orders of the same function field."
  r = _empty_divisor(K)
  r.finite_ideal = I
  r.infinite_ideal = J
  return r
end

@doc raw"""
    divisor(I::GenOrdFracIdl, J::GenOrdFracIdl) -> Divisor

Return the divisor corresponding to the factorization of the ideal I (for the finite places) and ideal J (for the infinite places)
"""
divisor(I::GenOrdFracIdl, J::GenOrdFracIdl) = Divisor(I, J)
divisor(I::GenOrdIdl,     J::GenOrdIdl)     = Divisor(fractional_ideal(I), fractional_ideal(J))
divisor(I::GenOrdFracIdl, J::GenOrdIdl)     = Divisor(I, fractional_ideal(J))
divisor(I::GenOrdIdl,     J::GenOrdFracIdl) = Divisor(fractional_ideal(I), J)

@doc raw"""
    divisor(I::GenOrdFracIdl) -> Divisor

Return the divisor corresponding to the factorization of the ideal I
"""
function divisor(I::GenOrdFracIdl{<: Generic.AbsSimpleFunctionField, <: KInftyRing})
  Ofin = finite_maximal_order(function_field(order(I)))
  return divisor(ideal(Ofin, one(Ofin)), I)
end

function divisor(I::GenOrdFracIdl{<: Generic.AbsSimpleFunctionField, <: PolyRing})
  Oinf = infinite_maximal_order(function_field(order(I)))
  return divisor(I, ideal(Oinf, one(Oinf)))
end

function divisor(I::GenOrdIdl)
  # A prime ideal (a place) gets the free representation
  if is_prime_known(I) && I.is_prime == 1
    O = order(I)
    F = function_field(O)
    s = Dict(I => 1)
    if _is_infinite_order(O)
      return _divisor_from_support(F, _empty_support(finite_maximal_order(F)), s)
    else
      return _divisor_from_support(F, s, _empty_support(infinite_maximal_order(F)))
    end
  end
  return divisor(fractional_ideal(I))
end

@doc raw"""
    divisor(f::Generic.AbsSimpleFunctionFieldElem) -> Divisor

Return the principal divisor consisting of the sum of zeroes and poles of f
"""
function divisor(f::Generic.AbsSimpleFunctionFieldElem{T, U}) where {T, U}
  @req !is_zero(f) "Element must be non-zero"
  F = parent(f)
  Ofin, Oinf = finite_maximal_order(F), infinite_maximal_order(F)
  D = divisor(Ofin * f, Oinf * f)
  # div(f) = 0 + 0*(x)_inf - div(f^(-1)) is already a projective representation.
  D.D_red = trivial_divisor(F)
  D.r = 0
  D.a = _fac_elem(F, f, -1)
  return D
end

@doc raw"""
    zero_divisor(f::Generic.AbsSimpleFunctionFieldElem) -> Divisor

Return the divisor consisting of the zeroes of f
"""
function zero_divisor(f::Generic.AbsSimpleFunctionFieldElem{T, U}) where {T, U}
  F = parent(f)
  return lcm(divisor(f), trivial_divisor(F))
end

@doc raw"""
    pole_divisor(f::Generic.AbsSimpleFunctionFieldElem) -> Divisor

Return the divisor consisting of the poles of f
"""
function pole_divisor(f::Generic.AbsSimpleFunctionFieldElem{T, U}) where {T, U}
  F = parent(f)
  return lcm(divisor(inv(f)), trivial_divisor(F))
end



################################################################################
#
#  Functions for switching representations and assuring existence
#
################################################################################

function _divisor_from_inverse_ideals(J_fin::GenOrdFracIdl, J_inf::GenOrdFracIdl)
  r = _empty_divisor(function_field(order(J_fin)))
  r.finite_inv_ideal = J_fin
  r.infinite_inv_ideal = J_inf
  return r
end

function _divisor_from_support(F::Generic.AbsSimpleFunctionField, s_fin::Dict, s_inf::Dict)
  r = _empty_divisor(F)
  r.finite_support = s_fin
  r.infinite_support = s_inf
  return r
end

_empty_support(O::GenOrd{S, T}) where {S, T} = Dict{GenOrdIdl{S, T}, Int}()

# Factored elements of F share one parent, cached on F
function _fac_elem_parent(F::Generic.AbsSimpleFunctionField)
  return get_attribute!(F, :fac_elem_mon) do
    FacElemMon{typeof(F)}(F)
  end::FacElemMon{typeof(F)}
end

# Evaluate a factored element of F with a single division at the end
function _evaluate_fac_elem(f::FacElem)
  F = base_ring(f)
  num = one(F)
  den = one(F)
  for (b, e) in f
    if e > 0
      num *= b^Int(e)
    elseif e < 0
      den *= b^Int(-e)
    end
  end
  return is_one(den) ? num : num // den
end

# The factored element f^e
function _fac_elem(F::Generic.AbsSimpleFunctionField, f, e::Int)
  return FacElem(F, [f], [ZZRingElem(e)]; parent = _fac_elem_parent(F))
end

_is_infinite_order(O::GenOrd) = base_ring(O) isa KInftyRing


has_support(D::Divisor) = isdefined(D, :finite_support) && isdefined(D, :infinite_support)
has_inverse_ideals(D::Divisor) = isdefined(D, :finite_inv_ideal)
has_proj_representation(D::Divisor) = isdefined(D, :D_red)
has_ideals(D::Divisor) = isdefined(D, :finite_ideal)

_unit_fractional_ideal(O::GenOrd) = fractional_ideal(ideal(O, one(O)))

# P^(-1) for a prime ideal P, cached on P
function _inv_prime(P::GenOrdIdl{S, T}) where {S, T}
  return get_attribute!(P, :inverse_ideal) do
    inv(P)
  end::GenOrdFracIdl{S, T}
end

# J = prod_P P^(-n_P) for a free representation
function _inv_ideal_from_support(O::GenOrd, s::Dict)
  J = _unit_fractional_ideal(O)
  for (P, n) in s
    if n > 0
      J = J * _inv_prime(P)^n
    elseif n < 0
      J = J * fractional_ideal(P)^(-n)
    end
  end
  return J
end

function _shift_infinite_ideal(J::GenOrdFracIdl, r::Int)
  r == 0 && return J
  kx = base_field(field(order(J)))
  return gen(kx)^r * J
end

# For D = A + r*(x)_inf - div(a) in projective representation, the inverse
#   ideals of A + r*(x)_inf. Since L(D) = a * L(A + r*(x)_inf), they determine
#   L(D) without evaluating a.
function _shifted_reduced_inverse_ideals(D::Divisor)
  A = D.D_red
  assure_has_inverse_ideals(A)
  return A.finite_inv_ideal, _shift_infinite_ideal(A.infinite_inv_ideal, D.r)
end

function assure_has_inverse_ideals(D::Divisor)
  if !has_inverse_ideals(D)
    F = function_field(D)
    if has_ideals(D)
      J_fin = inv(D.finite_ideal)
      J_inf = inv(D.infinite_ideal)
    elseif has_support(D)
      J_fin = _inv_ideal_from_support(finite_maximal_order(F), D.finite_support)
      J_inf = _inv_ideal_from_support(infinite_maximal_order(F), D.infinite_support)
    elseif has_proj_representation(D)
      # J(A + r*(x)_inf - div(f)) = J(A + r*(x)_inf) * f O
      J_fin, J_inf = _shifted_reduced_inverse_ideals(D)
      for (b, e) in D.a
        c = e > 0 ? b^Int(e) : inv(b)^Int(-e)
        J_fin = c * J_fin
        J_inf = c * J_inf
      end
    else
      error("Divisor has no representation")
    end
    D.finite_inv_ideal = J_fin
    D.infinite_inv_ideal = J_inf
  end
end

function assure_has_support(D::Divisor)
  if !has_support(D)
    D1, D2 = ideals(D)
    D.finite_support = factor(D1)
    D.infinite_support = factor(D2)
  end
end

function assure_has_proj_representation(D::Divisor)
  if !has_proj_representation(D)
    assure_has_inverse_ideals(D)
    F = function_field(D)
    D_red, r, a = _maximal_reduction(D.finite_inv_ideal, D.infinite_inv_ideal, F)
    _set_proj_representation!(D, D_red, r, _fac_elem(F, a, 1))
  end
end

function _set_proj_representation!(D::Divisor, D_red::Divisor, r::Int, a::FacElem)
  D.D_red = D_red
  D.r = r
  D.a = a
  return D
end

@doc raw"""
    ideals(D::Divisor) -> GenOrdFracIdl, GenOrdFracIdl

Return a pair of ideals I, J that represent the divisor D. Here I is the ideal for the finite maximal order
and J is the ideal of the infinite maximal order, and v_P(I) (resp. v_P(J)) is the multiplicity of D at
a finite (resp. infinite) place P.
"""
function ideals(D::Divisor)
  if !has_ideals(D)
    assure_has_inverse_ideals(D)
    D.finite_ideal = inv(D.finite_inv_ideal)
    D.infinite_ideal = inv(D.infinite_inv_ideal)
  end
  return D.finite_ideal, D.infinite_ideal
end

@doc raw"""
    inverse_ideals(D::Divisor) -> GenOrdFracIdl, GenOrdFracIdl

Return the pair of ideals (J_fin, J_inf) with J = prod_P P^(-n_P), where D = sum_P n_P P, that is
J = {f : v_P(f) >= -n_P}. Then the Riemann-Roch space of D is the intersection of J_fin and J_inf.
"""
function inverse_ideals(D::Divisor)
  assure_has_inverse_ideals(D)
  return D.finite_inv_ideal, D.infinite_inv_ideal
end

@doc raw"""
    projective_representation(D::Divisor) -> Divisor, Int, FacElem

Return (D_red, r, a) with D = D_red + r*(x)_inf - div(a), where (x)_inf is the pole divisor of the
generator x of the rational function field and D_red is effective of small degree.
"""
function projective_representation(D::Divisor)
  assure_has_proj_representation(D)
  return D.D_red, D.r, D.a
end


################################################################################
#
#  IO
#
################################################################################

function show(io::IO, D::Divisor)
  print(io, "Divisor of function field", D.function_field)
  if has_support(D)
    print(io, "\nDivisor in free representation:")
    print(io, "\nFinite support: ", D.finite_support)
    print(io, "\nInfinite support: ", D.infinite_support)
  elseif has_ideals(D)
    print(io, "\nDivisor in ideal representation:")
    print(io, "\nFinite ideal: ", D.finite_ideal)
    print(io, "\nInfinite ideal: ", D.infinite_ideal)
  elseif has_inverse_ideals(D)
    print(io, "\nDivisor in inverse ideal representation:")
    print(io, "\nFinite ideal: ", D.finite_inv_ideal)
    print(io, "\nInfinite ideal: ", D.infinite_inv_ideal)
  end
end

################################################################################
#
#  Field Access
#
################################################################################

@doc raw"""
    function_field(D::Divisor) -> AbsSimpleFunctionField

Return the function field to which D belongs
"""
function function_field(D::Divisor)
  return D.function_field
end

@doc raw"""
    function_field(O::GenOrd) -> AbsSimpleFunctionField

Return the function field of O.
"""
function function_field(O::GenOrd)
  return O.F
end


@doc raw"""
    finite_maximal_order(K::AbsSimpleFunctionField) -> GenOrd

Return the finite maximal order of K
"""
@attr GenOrd{Generic.AbsSimpleFunctionField{T, U}, parent_type(U)} function
finite_maximal_order(K::Generic.AbsSimpleFunctionField{T, U}) where {T, U}
  kx = parent(numerator(gen(base_ring(K))))
  return integral_closure(kx, K)
end

@doc raw"""
    infinite_maximal_order(K::AbsSimpleFunctionField) -> GenOrd

Return the infinite maximal order of K
"""
@attr GenOrd{Generic.AbsSimpleFunctionField{T, U}, KInftyRing{T, U}} function
infinite_maximal_order(K::Generic.AbsSimpleFunctionField{T, U}) where {T, U}
  R = localization(base_ring(K), degree)
  return integral_closure(R, K)
end


################################################################################
#
#  Equality / Comparison
#
################################################################################

function Base.:(==)(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  D1.function_field === D2.function_field || return false
  if has_support(D1) && has_support(D2)
    return D1.finite_support == D2.finite_support && D1.infinite_support == D2.infinite_support
  end
  return inverse_ideals(D1) == inverse_ideals(D2)
end

function Base.isequal(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  return D1 == D2
end

function Base.hash(D::Divisor, h::UInt)
  return hash(inverse_ideals(D), h)
end

# NOTE: divisor comparison defines a partial order, not total order
# NOTE: thus it is not safe to use sorting algorithms with divisors
function Base.isless(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  @req D1.function_field == D2.function_field "Divisors do not belong to the same field"
  D1 == D2 && return false

  assure_has_support(D1)
  assure_has_support(D2)

  s_fin = union(keys(D1.finite_support),   keys(D2.finite_support))
  s_inf = union(keys(D1.infinite_support), keys(D2.infinite_support))
  return all(p -> valuation(D1, p) <= valuation(D2, p), union(s_fin, s_inf))
end



################################################################################
#
#  Divisor arithmetic
#
#  Each operation computes one representation of the result, chosen from
#  the representations both operands already have.
#  Current approach (could be changed or improved) is to try 
#  the following in order:
#  (i)) Try the free representation as it is usually easiest , 
#  (ii) Try the projective representation
#  (iii) Only use ideal representation as a last resort.
#  If only one operand is projective, the other one is reduced, so that the
#  result stays projective.
#
################################################################################

function Base.:+(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  @req D1.function_field === D2.function_field "Divisors have to belong to the same field"
  F = function_field(D1)

  if has_support(D1) && has_support(D2)
    return _divisor_from_support(F, _merge_support_dict(+, D1.finite_support, D2.finite_support),
                                    _merge_support_dict(+, D1.infinite_support, D2.infinite_support))
  end

  if has_proj_representation(D1) && has_proj_representation(D2)
    R = _empty_divisor(F)
    return _set_proj_representation!(R, _add_in_proj_representation(D1, D2)...)
  end

  if (has_inverse_ideals(D1) || has_ideals(D1)) && (has_inverse_ideals(D2) || has_ideals(D2))
    J1_fin, J1_inf = inverse_ideals(D1)
    J2_fin, J2_inf = inverse_ideals(D2)
    return _divisor_from_inverse_ideals(J1_fin * J2_fin, J1_inf * J2_inf)
  end

  if has_proj_representation(D1) || has_proj_representation(D2)
    #If only one divisor has the projective representation, 
    #we reduce the other summand
    R = _empty_divisor(F)
    return _set_proj_representation!(R, _add_in_proj_representation(D1, D2)...)
  end

  J1_fin, J1_inf = inverse_ideals(D1)
  J2_fin, J2_inf = inverse_ideals(D2)
  return _divisor_from_inverse_ideals(J1_fin * J2_fin, J1_inf * J2_inf)
end

function _add_in_proj_representation(D1::Divisor, D2::Divisor)
  D1_red, r1, a1 = projective_representation(D1)
  D2_red, r2, a2 = projective_representation(D2)
  J1_fin, J1_inf = inverse_ideals(D1_red)
  J2_fin, J2_inf = inverse_ideals(D2_red)
  F = function_field(D1)
  D_red, s, h = _maximal_reduction(J1_fin * J2_fin, J1_inf * J2_inf, F)
  return D_red, r1 + r2 + s, a1 * a2 * _fac_elem(F, h, 1)
end

# projective representation of -D
function _neg_in_proj_representation(D::Divisor)
  D_red, r, a = projective_representation(D)
  J_fin, J_inf = inverse_ideals(D_red)
  F = function_field(D)
  B_red, s, h = _maximal_reduction(inv(J_fin), inv(J_inf), F)
  return B_red, s - r, _fac_elem(F, h, 1) * inv(a)
end

function Base.:-(D::Divisor)
  F = function_field(D)
  R = _empty_divisor(F)
  if has_support(D)
    R.finite_support = Dict(P => -n for (P, n) in D.finite_support)
    R.infinite_support = Dict(P => -n for (P, n) in D.infinite_support)
  end

  if has_ideals(D)
    R.finite_inv_ideal = D.finite_ideal
    R.infinite_inv_ideal = D.infinite_ideal
  end
  if has_inverse_ideals(D)
    R.finite_ideal = D.finite_inv_ideal
    R.infinite_ideal = D.infinite_inv_ideal
  end
  if !has_support(R) && !has_inverse_ideals(R) && !has_ideals(R)
    _set_proj_representation!(R, _neg_in_proj_representation(D)...)
  end
  return R
end

function Base.:*(n::Int, D::Divisor)
  F = function_field(D)
  n == 0 && return trivial_divisor(F)
  n == 1 && return D
  n < 0 && return (-n) * (-D)

  if has_support(D)
    return _divisor_from_support(F, Dict(P => n*e for (P, e) in D.finite_support),
                                    Dict(P => n*e for (P, e) in D.infinite_support))
  end

  if has_proj_representation(D)
    R = nothing
    B = D
    m = n
    while m > 0
      if isodd(m)
        R = R === nothing ? B : R + B
      end
      m >>= 1
      m > 0 && (B = B + B)
    end
    return R
  end

  if has_inverse_ideals(D)
    return _divisor_from_inverse_ideals(D.finite_inv_ideal^n, D.infinite_inv_ideal^n)
  end

  return Divisor(D.finite_ideal^n, D.infinite_ideal^n)
end

Base.:*(D::Divisor, n::Int) = n * D

function Base.:(-)(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  return D1 + (-D2)
end

function gcd(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  F = function_field(D1)
  if has_support(D1) && has_support(D2)
    return _divisor_from_support(F, _merge_support_dict(min, D1.finite_support, D2.finite_support),
                                    _merge_support_dict(min, D1.infinite_support, D2.infinite_support))
  end
  J1_fin, J1_inf = inverse_ideals(D1)
  J2_fin, J2_inf = inverse_ideals(D2)
  return _divisor_from_inverse_ideals(intersect(J1_fin, J2_fin), intersect(J1_inf, J2_inf))
end

function lcm(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  F = function_field(D1)
  if has_support(D1) && has_support(D2)
    return _divisor_from_support(F, _merge_support_dict(max, D1.finite_support, D2.finite_support),
                                    _merge_support_dict(max, D1.infinite_support, D2.infinite_support))
  end
  J1_fin, J1_inf = inverse_ideals(D1)
  J2_fin, J2_inf = inverse_ideals(D2)
  return _divisor_from_inverse_ideals(J1_fin + J2_fin, J1_inf + J2_inf)
end

################################################################################
#
#  Support
#
################################################################################


@doc raw"""
    support(D::Divisor) -> Vector{(GenOrdIdl, Int)}

Return an array of ideals and multiplicities corresponding to the support of D.
"""
function support(D::Divisor)
  assure_has_support(D)
  return vcat(finite_support(D), infinite_support(D))
end

@doc raw"""
    valuation(D::Divisor, p::GenOrdIdl) -> Int

Return the multiplicity of D at the prime ideal p.
"""
function valuation(D::Divisor{S, T1, T2}, p::GenOrdIdl{S, T1}) where {S, T1 <: PolyRing, T2 <: KInftyRing}
  @req is_prime(p) "p must be prime ideal"

  #Might not always want to compute support for a simple valuation
  assure_has_support(D)
  return get(D.finite_support, p, 0)
end

function valuation(D::Divisor{S, T1, T2}, p::GenOrdIdl{S, T2}) where {S, T1 <: PolyRing, T2 <: KInftyRing}
  @req is_prime(p) "p must be prime ideal"

  #Might not always want to compute support for a simple valuation
  assure_has_support(D)
  return get(D.infinite_support, p, 0)
end


function finite_support(D::Divisor)
  assure_has_support(D)
  return collect(D.finite_support)
end

function infinite_support(D::Divisor)
  assure_has_support(D)
  return collect(D.infinite_support)
end

# Trivial helper to merge supports with an operation, and ensure we have exact/compact support
function _merge_support_dict(op, s1::Dict{Hecke.GenOrdIdl{S, T}, Int64}, s2::Dict{Hecke.GenOrdIdl{S, T}, Int64}) where {S, T}
  s = Dict{GenOrdIdl{S, T},Int}()

  for p in union(keys(s1), keys(s2))
    p_val = op(get(s1, p, 0), get(s2, p, 0))
    if p_val != 0
      s[p] = p_val
    end
  end

  return s
end

# Trivial helper to filter support
function _filter_support(D::Divisor, pred)
  assure_has_support(D)
  s_fin = filter(t -> pred(t), D.finite_support)
  s_inf = filter(t -> pred(t), D.infinite_support)
  return _divisor_from_support(function_field(D), s_fin, s_inf)
end


################################################################################
#
#  Related Divisors
#
################################################################################

@doc raw"""
    finite_divisor(D::Divisor) -> Divisor

Return the divisor whose support is equal to the support of D in the finite places
"""
function finite_divisor(D::Divisor)
  F = function_field(D)
  if has_support(D)
    return _divisor_from_support(F, copy(D.finite_support), _empty_support(infinite_maximal_order(F)))
  end
  J_fin, _ = inverse_ideals(D)
  return _divisor_from_inverse_ideals(J_fin, _unit_fractional_ideal(infinite_maximal_order(F)))
end

@doc raw"""
    infinite_divisor(D::Divisor) -> Divisor

Return the divisor whose support is equal to the support of D in the infinite places
"""
function infinite_divisor(D::Divisor)
  F = function_field(D)
  if has_support(D)
    return _divisor_from_support(F, _empty_support(finite_maximal_order(F)), copy(D.infinite_support))
  end
  _, J_inf = inverse_ideals(D)
  return _divisor_from_inverse_ideals(_unit_fractional_ideal(finite_maximal_order(F)), J_inf)
end


@doc raw"""
    finite_split(D::Divisor) -> Divisor, Divisor

Return the tuple consisitng of the 'finite_divisor' and the 'infinite' divisor.
"""
function finite_split(D::Divisor)
  return finite_divisor(D), infinite_divisor(D)
end

@doc raw"""
    zero_divisor(D::Divisor) -> Divisor

Return the divisor whose support consists exactly of all zeroes in the support of D.
"""
function zero_divisor(D::Divisor)
  if has_support(D)
    return _filter_support(D, x -> x.second > 0)
  else
    return lcm(D, trivial_divisor(function_field(D)))
  end
end

@doc raw"""
    pole_divisor(D::Divisor) -> Divisor

Return the divisor whose support consists exactly of all poles in the support of D.
"""
function pole_divisor(D::Divisor)
  if has_support(D)
    return -_filter_support(D, x -> x.second < 0)
  else
    return lcm(-D, trivial_divisor(function_field(D)))
  end
end

################################################################################
#
#  Properties
#
################################################################################

# degree over k of the place P
function _place_degree(P::GenOrdIdl)
  p = minimum(P; copy = false)
  # the infinite place of k(x) has degree 1
  dp = p isa KInftyElem ? 1 : degree(p)
  return degree(P) * dp
end

# degree of the divisor with the ideals I (v_P(I) = n_P), from the norms
function _degree_from_ideals(I_fin::GenOrdFracIdl, I_inf::GenOrdFracIdl)
  # deg(D) = deg_x(det(basis_matrix(I_fin))) + v_inf(det(basis_matrix(I_inf)))
  #        = deg_x( norm(num(I_fin)) / den(I_fin)^n ) + v_inf( norm(num(I_inf)) / den(I_inf)^n ),
  # with n = [F : k(x)]. Since v_inf(f) = -deg_x(f) (also for KInftyElem, see
  # `degree(::KInftyElem)`), we compute degrees in x and SUBTRACT the infinite contribution.
  n = degree(field(order(I_fin)))

  N_fin = numerator(I_fin; copy = false)
  d_fin = denominator(I_fin; copy = false)
  fin_deg = degree(norm(N_fin)) - n*degree(d_fin)

  N_inf = numerator(I_inf; copy = false)
  d_inf = denominator(I_inf; copy = false)
  inf_deg = degree(norm(N_inf)) - n*degree(d_inf)

  return fin_deg - inf_deg
end

@doc raw"""
    degree(D::Divisor) -> Int

Return the degree of D.
"""
function degree(D::Divisor)
  # A divisor D = sum_P n_P * P has degree sum_P n_P * deg(P), where
  #   deg(P) = f(P) * deg(p) for a place P over the place p of k(x).
  if has_support(D)
    fin_deg = sum(_place_degree(P)*e for (P, e) in D.finite_support; init = 0)
    inf_deg = sum(_place_degree(P)*e for (P, e) in D.infinite_support; init = 0)
    return fin_deg + inf_deg
  end
  if has_proj_representation(D)
    # deg(D_red + r*(x)_inf - div(a)) = deg(D_red) + r*[F : k(x)]
    return degree(D.D_red) + D.r * degree(function_field(D))
  end
  if has_inverse_ideals(D)
    return -_degree_from_ideals(D.finite_inv_ideal, D.infinite_inv_ideal)
  end
  return _degree_from_ideals(D.finite_ideal, D.infinite_ideal)
end

@doc raw"""
    is_effective(D::Divisor) -> Bool

Return true if D is an effective divisor.
"""
function is_effective(D::Divisor)
  if has_support(D)
    return all(>=(0), values(D.finite_support)) && all(>=(0), values(D.infinite_support))
  end
  if has_ideals(D) && !has_inverse_ideals(D)
    return is_integral(D.finite_ideal) && is_integral(D.infinite_ideal)
  end
  # D >= 0 iff O is contained in J, i.e. iff 1 is in J
  J_fin, J_inf = inverse_ideals(D)
  F = function_field(D)
  return one(F) in J_fin && one(F) in J_inf
end

@doc raw"""
    is_principal(D::Divisor) -> Bool

Return true if D is a principal divisor.
"""
function is_principal(D::Divisor)
  return degree(D) == 0 && dimension(D) == 1
end

@doc raw"""
    is_principal_with_data(D::Divisor) -> Bool, FunFieldElem

Tests if $D$ is principal and returns $(\mathtt{true}, f)$ if $D = \langle f \rangle$ or $(\mathtt{false}, 1)$ otherwise.
"""
function is_principal_with_data(D::Divisor)
  F = function_field(D)

  degree(D) == 0 || return (false, one(F))

  RR = riemann_roch_space(D)
  length(RR) == 1 || return (false, one(F))

  return (true, inv(RR[1]))
end

@doc raw"""
    is_zero(D::Divisor) -> Bool

Return true if D is the trivial divisor.
"""
function is_zero(D::Divisor)
  if has_support(D)
    return isempty(D.finite_support) && isempty(D.infinite_support)
  end
  if has_ideals(D) && !has_inverse_ideals(D)
    return is_one(D.finite_ideal) && is_one(D.infinite_ideal)
  end
  J_fin, J_inf = inverse_ideals(D)
  return is_one(J_fin) && is_one(J_inf)
end


################################################################################
#
#  Different
#
################################################################################
@doc raw"""
    different_divisor(F::AbsSimpleFunctionField) -> Divisor

Return the different divisor of F.
"""
@attr Divisor{Generic.AbsSimpleFunctionField{T, U}, parent_type(U), KInftyRing{T, U}} function
different_divisor(K::Generic.AbsSimpleFunctionField{T, U}) where {T, U}
  return divisor(different(finite_maximal_order(K)), different(infinite_maximal_order(K)))
end

@doc raw"""
    complementary_divisor(D::Divisor) -> Divisor

Return the complementary divisor of D, which is D_F - D, where D_F is the different divisor of F.
"""
function complementary_divisor(D::Divisor)
  F = function_field(D)
  return different_divisor(F) - D
end


################################################################################
#
#  Canonical Divisor
#
################################################################################
@doc raw"""
    canonical_divisor(F::AbsSimpleFunctionField) -> Divisor

Return the canonical divisor of F.
"""
@attr Divisor{Generic.AbsSimpleFunctionField{T, U}, parent_type(U), KInftyRing{T, U}} function
canonical_divisor(K::Generic.AbsSimpleFunctionField{T, U}) where {T, U}
  @req _is_separable(K) "Currently assumes separable extension"

  dx = differential(separating_element(K))
  return divisor(dx)
end

@doc raw"""
    genus(F::AbsSimpleFunctionField) -> Int

Return the genus of F.
"""
@attr Int function genus(F::AbstractAlgebra.Generic.AbsSimpleFunctionField)
  @req _is_separable(F) "Currently assumes separable extension"
  # g = (degree(K) + 2) / 2, where K is the canonical divisor.
  # Since K = (dx) = Diff_{F/k(x)} - 2(x)_inf, we have
  # deg(K) = deg(Diff_{F/k(x)}) - 2*[F:k(x)], and
  # g = 1 - n + deg(Diff_{F/k(x)}) / 2

  d1 = degree(discriminant(finite_maximal_order(F)))
  d2 = degree(discriminant(infinite_maximal_order(F)))
  # note that we need valuation at infinity: degree in t = 1/x (hence minus)
  dDiff = d1 - d2
  @assert iseven(dDiff)

  m = constant_field_degree(F)
  return 1 + divexact(dDiff - 2*degree(F), 2*m)
end


################################################################################
#
#  Riemann-Roch computation
#
#  implements Riemann-Roch computation from Hess'
#  "Computing Riemann-Roch Spaces in Algebraic Function Fields and Related Topics"
#
################################################################################
@doc raw"""
    riemann_roch_space(D::Divisor) -> Vector{FunFieldElem}

Return a basis of the Riemann-Roch space L(D).
"""
function riemann_roch_space(D::Divisor)
  F = function_field(D)
  if !has_inverse_ideals(D) && has_proj_representation(D)
    # L(D) = a * L(A + r*(x)_inf) for D = A + r*(x)_inf - div(a)
    B = _riemann_roch_space(_shifted_reduced_inverse_ideals(D)..., F)
    a = _evaluate_fac_elem(D.a)
    return elem_type(F)[a * b for b in B]
  end
  J_fin, J_inf = inverse_ideals(D)
  return _riemann_roch_space(J_fin, J_inf, F)
end

# we have two functions: _riemann_roch_space to compute Riemann-Roch space itself
#   and _riemann_roch_dim to compute its dimension
# Their inputs are:
#   J_fin is the inverse of the finite ideal
#   J_inf is the inverse of the infinite ideal
#   F is the ambient function field

# common setup for Riemann-Roch
# B_fin and B_inf are coordinate matrices (basis elements in the power basis)
function _riemann_roch_common_setup(B_fin, B_inf)
  # express B_fin in terms of B_inf
  M = solve(B_inf, B_fin; side = :left)

  # clear denominators
  d = mapreduce(denominator, lcm, M)

  return change_base_ring(parent(d), d*M), degree(d)
end

# computes the basis of the Riemann-Roch space
function _riemann_roch_space(J_fin, J_inf, F)
  x = gen(base_ring(F))
  n = degree(F)

  B_fin = _coordinate_matrix(J_fin)
  B_inf = _coordinate_matrix(J_inf)
  dM, d_deg = _riemann_roch_common_setup(B_fin, B_inf)

  # weak Popov reduction of dM (no denominators)
  T, U = _weak_popov_with_transform!(dM)

  # v_i in Hess paper: rows have v_i coordinates in power basis
  basis_gens = change_base_ring(base_ring(B_fin), U) * B_fin

  RR_basis = elem_type(F)[]
  for i in 1:n
    d_i = maximum(degree(T[i, k]) for k in 1:n)
    g = F(vec(collect(basis_gens[i, :])))
    for _ in 0:(d_deg - d_i)
      push!(RR_basis, g)
      g = x*g # this is x^j * basis_gens[i] for j = 0 .. d_deg - d_i
    end
  end
  return RR_basis
end

# computes the dimension of the Riemann-Roch space
function _riemann_roch_dim(J_fin, J_inf, F)
  n = degree(F)

  dM, d_deg = _riemann_roch_common_setup(_coordinate_matrix(J_fin), _coordinate_matrix(J_inf))

  # we need only weak Popov form itself, without transform
  T = _weak_popov!(dM)

  # same as above, but instead of constructing basis vectors we just count them
  dim = 0
  for i in 1:n
    d_i = maximum(degree(T[i, k]) for k in 1:n)
    dim += max(0, d_deg - d_i + 1)
  end

  return dim
end

@doc raw"""
    dimension(D::Divisor) -> Int

Return the dimension l(D) of the Riemann-Roch space L(D).
"""
function dimension(D::Divisor)
  F = function_field(D)
  if !has_inverse_ideals(D) && has_proj_representation(D)
    # l(D) = l(A + r*(x)_inf) for D = A + r*(x)_inf - div(a)
    return _riemann_roch_dim(_shifted_reduced_inverse_ideals(D)..., F)
  end
  J_fin, J_inf = inverse_ideals(D)
  return _riemann_roch_dim(J_fin, J_inf, F)
end

@doc raw"""
    index_of_speciality(D::Divisor) -> Int

Return the index of speciality of D, which is the dimension Riemann-Roch space
L(K - D), where K is the canonical divisor of the function field of D.
"""
function index_of_speciality(D::Divisor)
  F = function_field(D)
  @req _is_separable(F) "Currently assumes separable extension"

  return dimension(canonical_divisor(F) - D)
end

################################################################################
#
#  Separability
#
#  Current implementation assumes that the defining polynomial is separable
#  While this might change in the future, we are not yet sure how this will be handled
#    so just isolate the related things in one place
#
################################################################################

# NOTE: we use the "is separable" check in plenty of places
#   and it turned out that this "looking trivial" check generates quite a lot
#   of memory garbage.
@attr Bool function _is_separable(F::Generic.AbsSimpleFunctionField)
  return is_separable(defining_polynomial(F))
end

function separating_element(F::Generic.AbsSimpleFunctionField)
  # TODO: currently we support ONLY extensions with separable defining polynomial
  @req _is_separable(F) "Currently assumes separable extension"

  return F(gen(base_ring(F)))
end
