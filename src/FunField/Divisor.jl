################################################################################
#
#  Constructors
#
################################################################################


mutable struct Divisor{S <: Generic.AbsSimpleFunctionField, T1 <: PolyRing, T2 <: KInftyRing}
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

function trivial_divisor(F::Generic.AbsSimpleFunctionField)
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

function divisor(I::GenOrdFracIdl{<: Generic.AbsSimpleFunctionField, <: KInftyRing})
  Ofin = finite_maximal_order(function_field(order(I)))
  return divisor(ideal(Ofin, one(Ofin)), I)
end

function divisor(I::GenOrdFracIdl{<: Generic.AbsSimpleFunctionField, <: PolyRing})
  Oinf = infinite_maximal_order(function_field(order(I)))
  return divisor(I, ideal(Oinf, one(Oinf)))
end

function divisor(I::GenOrdIdl)
  return divisor(GenOrdFracIdl(I))
end

@doc raw"""
    divisor(f::Generic.AbsSimpleFunctionFieldElem) -> Divisor

Return the principal divisor consisting of the sum of zeroes and poles of f
"""
function divisor(f::Generic.AbsSimpleFunctionFieldElem{T, U}) where {T, U}
  @req !is_zero(f) "Element must be non-zero"
  F = parent(f)

  Ofin, Oinf = finite_maximal_order(F), infinite_maximal_order(F)
  return divisor(Ofin * f, Oinf * f)
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
    function_field(D::Divisor) -> AbsSimpleFunctionField

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
    function_field(O::GenOrd) -> AbsSimpleFunctionField

Return the function field of O.
"""
function function_field(O::GenOrd)
  return O.F
end

@doc raw"""
    constant_field(K::AbsSimpleFunctionField) -> Field

Return the field of constants of K.
"""
function constant_field(K::AbstractAlgebra.Generic.AbsSimpleFunctionField)
  return base_ring(base_ring(K))
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
  #   polynomial in the base ring.
  #
  # For infinite places, p lies in KInftyRing.
  # The formula above stays correct if we read deg(p) as the degree of p
  #   as a polynomial in the local parameter t = 1/x.
  #
  # If we do NOT know the support, we proceed via the ideals directly.
  # let D = D_fin + D_inf with fractional ideals
  #   J_fin = I_fin / d_fin and J_inf = I_inf / d_inf. Then
  # deg(D) = deg_x(det(basis_matrix(J_fin))) + v_inf(det(basis_matrix(J_inf)))
  #        = deg_x( norm(I_fin) / d_fin^n ) + v_inf( norm(I_inf) / d_inf^n ),
  #   where we write n = [F : k(x)] for a degree.
  #
  # As before, v_inf(f) = -deg_x(f) is the degree in the local parameter t = 1/x, so
  #   we always compute degrees in x and SUBTRACT the infinite contribution.
  # This matches the support branch, where `degree(::KInftyElem)` also returns
  #   the degree in x.

  if has_support(D)
    function deg_place(p::GenOrdIdl, e::Integer)
      return degree(p)*degree(minimum(p))*e
    end

    fin_deg = sum(deg_place(f, e) for (f, e) in D.finite_support; init = zero(Int))
    inf_deg = sum(deg_place(f, e) for (f, e) in D.infinite_support; init = zero(Int))

    return fin_deg - inf_deg
  else
    n = degree(function_field(D))

    I_fin = numerator(D.finite_ideal; copy = false)
    d_fin = denominator(D.finite_ideal; copy = false)
    fin_deg = degree(norm(I_fin)) - n*degree(d_fin)

    I_inf = numerator(D.infinite_ideal; copy = false)
    d_inf = denominator(D.infinite_ideal; copy = false)
    inf_deg = degree(norm(I_inf)) - n*degree(d_inf)

    return fin_deg - inf_deg
  end
end

@doc raw"""
    is_effective(D::Divisor) -> Bool

Return true if D is an effective divisor.
"""
function is_effective(D::Divisor)
  # effective = no poles
  # if we know the support: check multiplicities (all non-negative)
  # otherwise check that ideals are integral (that is, no denominators)
  if has_support(D)
    return all(>=(0), values(D.finite_support)) && all(>=(0), values(D.infinite_support))
  else
    return is_integral(D.finite_ideal) && is_integral(D.infinite_ideal)
  end
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
  D1, D2 = ideals(D)
  return is_one(D1) && is_one(D2)
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

  return 1 - degree(F) + divexact(dDiff, 2)
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
  I_fin, I_inf = ideals(D)
  return _riemann_roch_space(inv(I_fin), inv(I_inf), function_field(D))
end

# we have two functions: _riemann_roch_space to compute Riemann-Roch space itself
#   and _riemann_roch_dim to compute its dimension
# Their inputs are:
#   J_fin is the inverse of the finite ideal
#   J_inf is the inverse of the infinite ideal
#   F is the ambient function field

# common setup for Riemann-Roch
function _riemann_roch_common_setup(basis_fin, basis_inf)
  # express basis_fin in terms of basis_inf
  B_fin = matrix(map(coordinates, basis_fin))
  B_inf = matrix(map(coordinates, basis_inf))
  M = solve(B_inf, B_fin; side = :left)

  # clear denominators
  d = mapreduce(denominator, lcm, M)

  return change_base_ring(parent(d), d*M), degree(d)
end

# computes the basis of the Riemann-Roch space
function _riemann_roch_space(J_fin, J_inf, F)
  x = gen(base_ring(F))
  n = degree(F)

  basis_fin = basis(J_fin)
  basis_inf = basis(J_inf)
  dM, d_deg = _riemann_roch_common_setup(basis_fin, basis_inf)

  # weak Popov reduction of dM (no denominators)
  T, U = weak_popov_with_transform(dM)

  # v_i in Hess paper
  basis_gens = change_base_ring(F, U) * basis_fin

  RR_basis = elem_type(F)[]
  for i in 1:n
    d_i = maximum(degree(T[i, k]) for k in 1:n)
    g = basis_gens[i]
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

  dM, d_deg = _riemann_roch_common_setup(basis(J_fin), basis(J_inf))

  # we need only weak Popov form itself, without transform
  T = weak_popov(dM)

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
  I_fin, I_inf = ideals(D)
  return _riemann_roch_dim(inv(I_fin), inv(I_inf), function_field(D))
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
