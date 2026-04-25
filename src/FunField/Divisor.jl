################################################################################
#
#  Constructors
#
################################################################################


mutable struct Divisor{S <: Generic.FunctionField, T1 <: PolyRing, T2 <: KInftyRing}
  function_field::S
  finite_ideal::GenOrdFracIdl{S, T1}
  infinite_ideal::GenOrdFracIdl{S, T2}
  finite_support::Dict{Hecke.GenOrdIdl{S, T1}, Int64}
  infinite_support::Dict{Hecke.GenOrdIdl{S, T2}, Int64}

  function Divisor(I::GenOrdFracIdl{S, T1}, J::GenOrdFracIdl{S, T2}) where {S, T1, T2}
    r = new{S, T1, T2}()

    K = function_field(order(I))
    @req K == function_field(order(J)) "Ideals need to belong to orders of the same function field."

    r.function_field = K
    r.finite_ideal = I
    r.infinite_ideal = J

    return r
  end

end

@attributes AbstractAlgebra.Generic.FunctionField

function trivial_divisor(F::Generic.FunctionField)
  return divisor(one(F))
end

@doc raw"""
    divisor(I::GenOrdFracIdl, J::GenOrdFracIdl) -> Divisor

Return the divisor corresponding to the factorization of the ideal I (for the finite places) and ideal J (for the infinite places)
"""
divisor(I::GenOrdFracIdl, J::GenOrdFracIdl) = Divisor(I, J)
divisor(I::GenOrdIdl,     J::GenOrdIdl)     = Divisor(GenOrdFracIdl(I), GenOrdFracIdl(J))
divisor(I::GenOrdFracIdl, J::GenOrdIdl)     = Divisor(I, GenOrdFracIdl(J))
divisor(I::GenOrdIdl,     J::GenOrdFracIdl) = Divisor(GenOrdFracIdl(I), J)

@doc raw"""
    divisor(I::GenOrdFracIdl) -> Divisor

Return the divisor corresponding to the factorization of the ideal I
"""

function divisor(I::GenOrdFracIdl{<: Generic.FunctionField, <: KInftyRing})
  Ofin = finite_maximal_order(function_field(order(I)))
  return divisor(ideal(Ofin, one(Ofin)), I)
end

function divisor(I::GenOrdFracIdl{<: Generic.FunctionField, <: PolyRing})
  Oinf = infinite_maximal_order(function_field(order(I)))
  return divisor(I, ideal(Oinf, one(Oinf)))
end

function divisor(I::GenOrdIdl)
  return divisor(GenOrdFracIdl(I))
end

@doc raw"""
    divisor(f::Generic.FunctionFieldElem) -> Divisor

Return the principal divisor consisting of the sum of zeroes and poles of f
"""
function divisor(f::Generic.FunctionFieldElem{T}) where {T <: FieldElement}
  @req !is_zero(f) "Element must be non-zero"
  F = parent(f)

  Ofin, Oinf = finite_maximal_order(F), infinite_maximal_order(F)
  return divisor(Ofin * f, Oinf * f)
end

@doc raw"""
    zero_divisor(f::Generic.FunctionFieldElem) -> Divisor

Return the divisor consisting of the zeroes of f
"""
function zero_divisor(f::Generic.FunctionFieldElem{T}) where {T <: FieldElement}
  F = parent(f)

  Ofin, Oinf = finite_maximal_order(F), infinite_maximal_order(F)
  f_num, f_denom = integral_split(f, Ofin)
  g_num, g_denom = integral_split(f, Oinf)

  return divisor(ideal(Ofin, f_num), ideal(Oinf, g_num))
end

@doc raw"""
    pole_divisor(f::Generic.FunctionFieldElem) -> Divisor

Return the divisor consisting of the poles of f
"""
function pole_divisor(f::Generic.FunctionFieldElem{T}) where {T <: FieldElement}
  F = parent(f)

  Ofin, Oinf = finite_maximal_order(F), infinite_maximal_order(F)
  f_num, f_denom = integral_split(f, Ofin)
  g_num, g_denom = integral_split(f, Oinf)

  return divisor(ideal(Ofin, f_denom), ideal(Oinf, g_denom))
end

################################################################################
#
#  IO
#
################################################################################

function show(io::IO, D::Divisor)
  print(io, "Divisor in ideal representation:")
  print(io, "\nFinite ideal: ", D.finite_ideal)
  print(io, "\nInfinite ideal: ", D.infinite_ideal)
end

################################################################################
#
#  Field Access
#
################################################################################

@doc raw"""
    function_field(D::Divisor) -> FunctionField

Return the function field to which D belongs
"""
function function_field(D::Divisor)
  return D.function_field
end

@doc raw"""
    ideals(D::Divisor) -> GenOrdFracIdl, GenOrdFracIdl

Return a pair of ideals I, J that represent the divisor D. Here I is the ideal for the finite maximal order
and J is the ideal of the infinite maximal order.
"""
function ideals(D::Divisor)
  return D.finite_ideal, D.infinite_ideal
end

@doc raw"""
    function_field(O::GenOrd) -> FunctionField

Return the function field of O.
"""
function function_field(O::GenOrd)
  return O.F
end

@doc raw"""
    constant_field(K::FunctionField) -> Field

Return the field of constants of K.
"""
function constant_field(K::AbstractAlgebra.Generic.FunctionField)
  return base_ring(base_ring(K))
end

@doc raw"""
    finite_maximal_order(K::FunctionFIeld) -> GenOrd

Return the finite maximal order of K
"""
function finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField{T}) where {T <: FieldElement}
  get_attribute!(K, :finite_maximal_order) do
    return _finite_maximal_order(K)
  end::GenOrd{AbstractAlgebra.Generic.FunctionField{T}, parent_type(poly_type(T))}
end

function _finite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  kx = parent(numerator(gen(base_ring(K))))
  return integral_closure(kx, K)
end

@doc raw"""
    infinite_maximal_order(K::FunctionFIeld) -> GenOrd

Return the infinite maximal order of K
"""
function infinite_maximal_order(K::AbstractAlgebra.Generic.FunctionField{T}) where {T <: FieldElement}
  get_attribute!(K, :infinite_maximal_order) do
    return _infinite_maximal_order(K)
  end::GenOrd{AbstractAlgebra.Generic.FunctionField{T}, KInftyRing{T}}
end

function _infinite_maximal_order(K::AbstractAlgebra.Generic.FunctionField)
  R = localization(base_ring(K),degree)
  Oinf = integral_closure(R, K)
  return Oinf
end

################################################################################
#
#  Equality / Comparison
#
################################################################################

function Base.:(==)(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  return D1.finite_ideal == D2.finite_ideal && D1.infinite_ideal == D2.infinite_ideal
end
function Base.isequal(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  return D1 == D2
end

function Base.hash(D::Divisor, h::UInt)
  return hash(ideals(D), h)
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
################################################################################

function Base.:+(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  D1_fin, D1_inf = ideals(D1)
  D2_fin, D2_inf = ideals(D2)
  Dnew = Divisor(D1_fin * D2_fin, D1_inf * D2_inf)

  if has_support(D1) && has_support(D2)
    _merge_support!(Dnew, +, D1, D2)
  end
  return Dnew
end

function Base.:*(n::Int, D::Divisor)
  I, J = ideals(D)

  Dnew = Divisor(I^n, J^n)

  if has_support(D)
    fin_supp = finite_support(D)
    inf_supp = infinite_support(D)
    Dnew.finite_support = Dict((p, n*e) for (p, e) in fin_supp)
    Dnew.infinite_support = Dict((p, n*e) for (p, e) in inf_supp)
  end

  return Dnew
end

Base.:*(D::Divisor, n::Int) = n * D
Base.:-(D::Divisor) = (-1)*D

function Base.:(-)(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  return D1 + (-D2)
end

function gcd(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  D1_fin, D1_inf = ideals(D1)
  D2_fin, D2_inf = ideals(D2)
  Dnew = Divisor(D1_fin + D2_fin, D1_inf + D2_inf)

  if has_support(D1) && has_support(D2)
    _merge_support!(Dnew, min, D1, D2)
  end
  return Dnew
end

function lcm(D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  D1_fin, D1_inf = ideals(D1)
  D2_fin, D2_inf = ideals(D2)
  Dnew = Divisor(intersect(D1_fin, D2_fin), intersect(D1_inf, D2_inf))

  if has_support(D1) && has_support(D2)
    _merge_support!(Dnew, max, D1, D2)
  end
  return Dnew
end

################################################################################
#
#  Support
#
################################################################################

function has_support(D::Divisor)
  return isdefined(D, :finite_support) && isdefined(D, :infinite_support)
end

function assure_has_support(D::Divisor)
  if !has_support(D)
    D1, D2 = ideals(D)
    D.finite_support = factor(D1)
    D.infinite_support = factor(D2)
  end
end

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
function valuation(D::Divisor{S, T1, T2}, p::GenOrdIdl{S, T1}) where {S, T1, T2}
  @req is_prime(p) "p must be prime ideal"

  #Might not always want to compute support for a simple valuation
  assure_has_support(D)
  return get(D.finite_support, p, 0)
end

function valuation(D::Divisor{S, T1, T2}, p::GenOrdIdl{S, T2}) where {S, T1, T2}
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

function _merge_support!(D::Divisor{S, T1, T2}, op, D1::Divisor{S, T1, T2}, D2::Divisor{S, T1, T2}) where {S, T1, T2}
  D.finite_support   = _merge_support_dict(op, D1.finite_support,   D2.finite_support)
  D.infinite_support = _merge_support_dict(op, D1.infinite_support, D2.infinite_support)
end

# trivial helper to filter support
function _filter_support(D::Divisor, pred)
  s_fin = filter(t -> pred(t), D.finite_support)
  s_inf = filter(t -> pred(t), D.infinite_support)

  F = function_field(D)
  Ofin, Oinf = finite_maximal_order(F), infinite_maximal_order(F)

  d_fin = prod(p^e for (p, e) in s_fin; init = Ofin(1)*Ofin)
  d_inf = prod(p^e for (p, e) in s_inf; init = Oinf(1)*Oinf)

  r = divisor(d_fin, d_inf)
  r.finite_support   = s_fin
  r.infinite_support = s_inf
  return r
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
  return divisor(D.finite_ideal)
end

@doc raw"""
    infinite_divisor(D::Divisor) -> Divisor

Return the divisor whose support is equal to the support of D in the infinite places
"""
function infinite_divisor(D::Divisor)
  return divisor(D.infinite_ideal)
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
  assure_has_support(D)
  return _filter_support(D, x -> x.second > 0)
end

@doc raw"""
    pole_divisor(D::Divisor) -> Divisor

Return the divisor whose support consists exactly of all poles in the support of D.
"""
function pole_divisor(D::Divisor)
  assure_has_support(D)
  return _filter_support(D, x -> x.second < 0)
end

################################################################################
#
#  Properties
#
################################################################################

@doc raw"""
    degree(D::Divisor) -> Int

Return the degree of D.
"""
function degree(D::Divisor)
  # A divisor D = sum_P n_P * P has degree sum_P n_P * deg(P), where P ranges
  #   over *places* of F/K (K the field of constants).
  #
  # For a place P lying over a (finite) prime p in the base ring,
  #   deg(P) = [F_P : K] = f(P) * deg(p),
  # where f(P) is the inertia degree and deg(p) is the degree of p as a
  # polynomial in the base ring.
  #
  # For infinite places, p lies in KInftyRing.
  # The formula above stays correct if we read deg(p) as the degree of p
  # as a polynomial in the local parameter t = 1/x.
  # However, `degree(::KInftyElem)` returns the degree in x, which is -(degree in t).
  # We therefore compensate by subtracting the infinite contribution rather than adding it.
  function deg_place(p::GenOrdIdl, e::Integer)
    return degree(p)*degree(minimum(p))*e
  end

  fin_deg = sum(deg_place(f, e) for (f, e) in finite_support(D); init = zero(Int))
  inf_deg = sum(deg_place(f, e) for (f, e) in infinite_support(D); init = zero(Int))

  return fin_deg - inf_deg
end

@doc raw"""
    is_effective(D::Divisor) -> Bool

Return true if D is an effective divisor.
"""
function is_effective(D::Divisor)
  return isempty(support(pole_divisor(D)))
end

@doc raw"""
    is_principal(D::Divisor) -> Bool

Return true if D is a principal divisor.
"""
function is_principal(D::Divisor)
  return degree(D) == 0 && dimension(D) == 1
end

@doc raw"""
    is_zero(D::Divisor) -> Bool

Return true if D is the trivial divisor.
"""
function is_zero(D::Divisor)
  D1, D2 = ideals(D)
  return is_one(D1) && is_one(D2)
end

################################################################################
#
#  Different
#
################################################################################
@doc raw"""
    different_divisor(F::FunctionField) -> Divisor

Return the different divisor of F.
"""
function different_divisor(F::AbstractAlgebra.Generic.FunctionField{T}) where {T <: FieldElement}
  return divisor(different(finite_maximal_order(F)), different(infinite_maximal_order(F)))
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
    canonical_divisor(F::FunctionField) -> Divisor

Return the canonical divisor of F.
"""
function canonical_divisor(F::AbstractAlgebra.Generic.FunctionField)
  @req is_separable(defining_polynomial(F)) "Currently assumes separable extension"

  dx = differential(separating_element(F))
  return divisor(dx)
end

function separating_element(F::AbstractAlgebra.Generic.FunctionField)
  # TODO: we need to search for one, instead of using x
  @req is_separable(defining_polynomial(F)) "Currently assumes separable extension"

  return F(gen(base_ring(F)))
end

@doc raw"""
    genus(F::FunctionField) -> Int

Return the genus of F.
"""
function genus(F::AbstractAlgebra.Generic.FunctionField)
  @req is_separable(defining_polynomial(F)) "Currently assumes separable extension"

  return length(basis_of_differentials(F))
end

################################################################################
#
#  Riemann-Roch computation
#
################################################################################
@doc raw"""
    riemann_roch_space(D::Divisor) -> Vector{FunFieldElem}

Return a basis of the Riemann-Roch space L(D).
"""
function riemann_roch_space(D::Divisor)
  I_fin, I_inf = ideals(D)
  J_fin = inv(I_fin)
  J_inf = inv(I_inf)

  F = function_field(D)
  return _riemann_roch_space(J_fin, J_inf, F)
end


#J_fin is inverse of finite ideal
#J_inf is inverse of infinite ideal
#F is functionfield
function _riemann_roch_space(J_fin, J_inf, F)

  x = gen(base_ring(F))
  n = degree(F)

  basis_gens = basis(J_fin)

  B_fin = matrix(map(coordinates, basis_gens))
  B_inf = matrix(map(coordinates, basis(J_inf)))

  M = solve(B_inf, B_fin; side = :left)
  d = lcm(vec(map(denominator,collect(M))))
  d_deg = degree(d)
  Mnew = change_base_ring(parent(d), d*M)

  T, U = weak_popov_with_transform(Mnew)

  basis_gens = change_base_ring(F, U) * basis(J_fin)

  RR_basis = elem_type(F)[]
  for i in (1:n)
    d_i = maximum(map(degree, T[i,1:n]))
    for j in (0: - d_i + d_deg)
      push!(RR_basis, x^(j) * basis_gens[i])
    end
  end
  return RR_basis
end

@doc raw"""
    dimension(D::Divisor) -> Int

Return the dimension l(D) of the Riemann-Roch space L(D).
"""
function dimension(D::Divisor)
  return length(riemann_roch_space(D))
end

@doc raw"""
    index_of_speciality(D::Divisor) -> Int

Return the index of speciality of D, which is the dimension Riemann-Roch space
L(K - D), where K is the canonical divisor of the function field of D.
"""
function index_of_speciality(D::Divisor)
  F = function_field(D)
  @req is_separable(defining_polynomial(F)) "Currently assumes separable extension"

  K = canonical_divisor(F)
  return length(riemann_roch_space(K - D))
end

