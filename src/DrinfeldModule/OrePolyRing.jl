################################################################################
#
#  DrinfeldModule/OrePolyRing.jl : Ore polynomial ring K{tau}
#
#  The ring K{tau} is the free left K-module with basis 1, tau, tau^2, ...
#  subject to the commutation rule tau * a = a^q * tau for a in K,
#  where q = order(F_q) for the base finite field F_q.
#
#  Multiplication:
#    (a_i * tau^i) * (b_j * tau^j) = a_i * b_j^{q^i} * tau^{i+j}
#
#  Right Euclidean division: f = q * g + r with deg(r) < deg(g).
#
################################################################################

################################################################################
#
#  Constructor
#
################################################################################

@doc raw"""
    ore_polynomial_ring(K::Ring, q::ZZRingElem, var::VarName = :tau)
      -> OrePolyRing, OrePoly

Return the Ore polynomial ring `K{tau}` with twist map `a -> a^q`, together
with the generator `tau`.
"""
function ore_polynomial_ring(K::Ring, q::ZZRingElem, var::VarName = :tau)
  T = elem_type(K)
  R = OrePolyRing{T}(K, q, Symbol(var))
  tau = OrePoly{T}(R, T[zero(K), one(K)])
  return R, tau
end

function ore_polynomial_ring(K::Ring, q::Integer, var::VarName = :tau)
  return ore_polynomial_ring(K, ZZRingElem(q), var)
end

################################################################################
#
#  AbstractAlgebra interface
#
################################################################################

elem_type(::Type{OrePolyRing{T}}) where {T} = OrePoly{T}

parent_type(::Type{OrePoly{T}}) where {T} = OrePolyRing{T}

base_ring(R::OrePolyRing) = R.base_ring

base_ring_type(::Type{OrePolyRing{T}}) where {T} = parent_type(T)

parent(f::OrePoly) = f.parent

base_ring(f::OrePoly) = base_ring(parent(f))

is_domain_type(::Type{OrePoly{T}}) where {T} = false

is_exact_type(::Type{OrePoly{T}}) where {T} = true

################################################################################
#
#  Zero and one
#
################################################################################

function zero(R::OrePolyRing{T}) where {T}
  return OrePoly{T}(R)
end

function one(R::OrePolyRing{T}) where {T}
  K = base_ring(R)
  return OrePoly{T}(R, T[one(K)])
end

function (R::OrePolyRing{T})() where {T}
  return zero(R)
end

# Coerce a base ring element to a constant Ore polynomial
function (R::OrePolyRing{T})(c::T) where {T}
  iszero(c) && return zero(R)
  return OrePoly{T}(R, T[c])
end

function (R::OrePolyRing{T})(c::Integer) where {T}
  K = base_ring(R)
  return R(K(c))
end

function (R::OrePolyRing{T})(c::ZZRingElem) where {T}
  K = base_ring(R)
  return R(K(c))
end

################################################################################
#
#  Generator
#
################################################################################

@doc raw"""
    gen(R::OrePolyRing{T}) -> OrePoly{T}

Return the generator `tau` of the Ore polynomial ring `R`.
"""
function gen(R::OrePolyRing{T}) where {T}
  K = base_ring(R)
  return OrePoly{T}(R, T[zero(K), one(K)])
end

var(R::OrePolyRing) = R.var

################################################################################
#
#  Basic predicates
#
################################################################################

function iszero(f::OrePoly)
  return isempty(f.coeffs)
end

function isone(f::OrePoly)
  return length(f.coeffs) == 1 && isone(f.coeffs[1])
end

################################################################################
#
#  Degree and coefficients
#
################################################################################

@doc raw"""
    degree(f::OrePoly) -> Int

Return the degree of `f`, i.e., the largest `i` with nonzero `tau^i`
coefficient. Returns `-1` for the zero element.
"""
function degree(f::OrePoly)
  return length(f.coeffs) - 1
end

@doc raw"""
    leading_coefficient(f::OrePoly{T}) -> T

Return the leading coefficient of `f`, i.e., the coefficient of the
highest-degree term. Errors on the zero element.
"""
function leading_coefficient(f::OrePoly{T}) where {T}
  @req !iszero(f) "leading coefficient of zero is undefined"
  return f.coeffs[end]
end

@doc raw"""
    constant_coefficient(f::OrePoly{T}) -> T

Return the constant term of `f`, i.e., the coefficient of `tau^0`.
"""
function constant_coefficient(f::OrePoly{T}) where {T}
  iszero(f) && return zero(base_ring(f))
  return f.coeffs[1]
end

@doc raw"""
    coeff(f::OrePoly{T}, i::Int) -> T

Return the coefficient of `tau^i` in `f`.
"""
function coeff(f::OrePoly{T}, i::Int) where {T}
  (i < 0 || i > degree(f)) && return zero(base_ring(f))
  return f.coeffs[i + 1]
end

@doc raw"""
    coefficients(f::OrePoly{T}) -> Vector{T}

Return the coefficients of `f` as a vector `[a_0, a_1, ..., a_d]`
where `f = a_0 + a_1*tau + ... + a_d*tau^d`.
"""
function coefficients(f::OrePoly{T}) where {T}
  return copy(f.coeffs)
end

################################################################################
#
#  Equality and hashing
#
################################################################################

function ==(f::OrePoly{T}, g::OrePoly{T}) where {T}
  parent(f) == parent(g) || return false
  return f.coeffs == g.coeffs
end

function ==(R::OrePolyRing{T}, S::OrePolyRing{T}) where {T}
  return R.base_ring === S.base_ring && R.q == S.q && R.var == S.var
end

function Base.hash(f::OrePoly{T}, h::UInt) where {T}
  b = 0x9f4a5b3c1e2d8f7a % UInt
  return xor(hash(f.coeffs, h), b)
end

function Base.hash(R::OrePolyRing{T}, h::UInt) where {T}
  b = 0x3a7c6e2b1d5f9840 % UInt
  return xor(hash(R.base_ring, xor(hash(R.q, h))), b)
end

################################################################################
#
#  Arithmetic: negation and scalar multiplication
#
################################################################################

function Base.:-(f::OrePoly{T}) where {T}
  R = parent(f)
  return OrePoly{T}(R, map(-, f.coeffs))
end

# Left scalar multiplication: c * f (c in K acts on the left)
function Base.:*(c::T, f::OrePoly{T}) where {T}
  R = parent(f)
  iszero(c) && return zero(R)
  return OrePoly{T}(R, T[c * a for a in f.coeffs])
end

# Right scalar multiplication: f * c
# tau^i * c = c^{q^i} * tau^i, so (f * c)_i = f_i * c^{q^i}
function Base.:*(f::OrePoly{T}, c::T) where {T}
  R = parent(f)
  iszero(c) && return zero(R)
  q = R.q
  n = length(f.coeffs)
  coeffs = Vector{T}(undef, n)
  for i in 0:n - 1
    coeffs[i + 1] = f.coeffs[i + 1] * _twist_n(c, i, q)
  end
  return OrePoly{T}(R, coeffs)
end

################################################################################
#
#  Arithmetic: addition and subtraction
#
################################################################################

function Base.:+(f::OrePoly{T}, g::OrePoly{T}) where {T}
  parent(f) === parent(g) ||
    error("Ore polynomials have different parents")
  R = parent(f)
  K = base_ring(R)
  n = max(length(f.coeffs), length(g.coeffs))
  coeffs = Vector{T}(undef, n)
  for i in 1:n
    ai = i <= length(f.coeffs) ? f.coeffs[i] : zero(K)
    bi = i <= length(g.coeffs) ? g.coeffs[i] : zero(K)
    coeffs[i] = ai + bi
  end
  return OrePoly{T}(R, coeffs)
end

function Base.:-(f::OrePoly{T}, g::OrePoly{T}) where {T}
  return f + (-g)
end

################################################################################
#
#  Arithmetic: multiplication
#
#  (a_i * tau^i) * (b_j * tau^j) = a_i * b_j^{q^i} * tau^{i+j}
#  so (f*g)_k = sum_{i+j=k} a_i * b_j^{q^i}
#
################################################################################

function Base.:*(f::OrePoly{T}, g::OrePoly{T}) where {T}
  parent(f) === parent(g) ||
    error("Ore polynomials have different parents")
  iszero(f) && return zero(parent(f))
  iszero(g) && return zero(parent(g))
  R = parent(f)
  K = base_ring(R)
  q = R.q
  m = degree(f)
  n = degree(g)
  coeffs = T[zero(K) for _ in 0:m + n]
  for i in 0:m
    ai = f.coeffs[i + 1]
    iszero(ai) && continue
    for j in 0:n
      bj = g.coeffs[j + 1]
      iszero(bj) && continue
      # contribution: a_i * b_j^{q^i} * tau^{i+j}
      coeffs[i + j + 1] += ai * _twist_n(bj, i, q)
    end
  end
  return OrePoly{T}(R, coeffs)
end

function Base.:^(f::OrePoly{T}, n::Int) where {T}
  n < 0 && error("negative exponent not supported for Ore polynomials")
  n == 0 && return one(parent(f))
  n == 1 && return deepcopy(f)
  R = parent(f)
  result = one(R)
  base = f
  while n > 0
    if isodd(n)
      result = result * base
    end
    n >>= 1
    n > 0 && (base = base * base)
  end
  return result
end

################################################################################
#
#  Internal helper: iterated Frobenius twist
#
#  _twist_n(a, n, q) computes a^{q^n} by applying the q-power map n times.
#
################################################################################

function _twist_n(a::T, n::Int, q::ZZRingElem) where {T}
  n == 0 && return a
  result = a
  for _ in 1:n
    result = result^q
  end
  return result
end

################################################################################
#
#  Right Euclidean division
#
#  right_quo_rem(f, g) returns (q, r) such that f = q * g + r, deg(r) < deg(g).
#
#  Algorithm: at each step, eliminate the leading term a_m * tau^m of f by
#  subtracting c * tau^{m-n} * g where c = a_m / b_n^{q^{m-n}} and b_n is
#  the leading coefficient of g.
#
################################################################################

@doc raw"""
    right_quo_rem(f::OrePoly{T}, g::OrePoly{T}) -> (OrePoly{T}, OrePoly{T})

Compute the right Euclidean division of `f` by `g`: return `(q, r)` such
that `f = q * g + r` and `degree(r) < degree(g)`.
"""
function right_quo_rem(f::OrePoly{T}, g::OrePoly{T}) where {T}
  @req !iszero(g) "divisor must be nonzero"
  parent(f) === parent(g) ||
    error("Ore polynomials have different parents")
  R = parent(f)
  q_order = R.q
  K = base_ring(R)
  n = degree(g)
  bn = leading_coefficient(g)

  if degree(f) < n
    return zero(R), deepcopy(f)
  end

  # work with a mutable copy of f's coefficients
  rem_coeffs = copy(f.coeffs)
  # pad to at least degree(f)+1
  deg_rem = length(rem_coeffs) - 1
  quot_len = deg_rem - n + 1
  quot_coeffs = T[zero(K) for _ in 1:quot_len]

  while deg_rem >= n
    k = deg_rem - n
    am = rem_coeffs[deg_rem + 1]
    # c = am / bn^{q^k}
    bn_k = _twist_n(bn, k, q_order)
    c = am * inv(bn_k)
    quot_coeffs[k + 1] = c
    # subtract c * tau^k * g from rem_coeffs:
    # (c * tau^k * g)_{k+j} = c * g_j^{q^k}
    for j in 0:n
      bj = coeff(g, j)
      rem_coeffs[k + j + 1] -= c * _twist_n(bj, k, q_order)
    end
    # update deg_rem: position deg_rem should now be zero
    while deg_rem >= 0 && iszero(rem_coeffs[deg_rem + 1])
      deg_rem -= 1
    end
  end

  r_coeffs = deg_rem < 0 ? T[] : rem_coeffs[1:deg_rem + 1]
  return OrePoly{T}(R, quot_coeffs), OrePoly{T}(R, r_coeffs)
end

################################################################################
#
#  Ore polynomial valuation (minimum non-zero coefficient index)
#
################################################################################

@doc raw"""
    ore_poly_valuation(f::OrePoly) -> Int

Return the smallest index `i` such that the coefficient of `tau^i` in `f`
is nonzero. Returns `degree(f) + 1` for the zero polynomial.
"""
function ore_poly_valuation(f::OrePoly)
  for i in 0:degree(f)
    !iszero(f.coeffs[i + 1]) && return i
  end
  return degree(f) + 1
end

################################################################################
#
#  Show
#
################################################################################

function AbstractAlgebra.expressify(R::OrePolyRing; context = nothing)
  return Expr(:sequence,
    Expr(:text, "Ore polynomial ring in "),
    Expr(:text, string(R.var)),
    Expr(:text, " over "),
    AbstractAlgebra.expressify(base_ring(R); context = context))
end

AbstractAlgebra.show_via_expressify(R::OrePolyRing) = true

function Base.show(io::IO, R::OrePolyRing)
  print(io, "Ore polynomial ring in ", R.var, " over ")
  print(io, base_ring(R))
end

function AbstractAlgebra.expressify(f::OrePoly; context = nothing)
  R = parent(f)
  x = string(R.var)
  if iszero(f)
    return Expr(:text, "0")
  end
  sum = Expr(:call, :+)
  for i in 0:degree(f)
    c = f.coeffs[i + 1]
    iszero(c) && continue
    if i == 0
      push!(sum.args, AbstractAlgebra.expressify(c; context = context))
    elseif i == 1
      term = Expr(:call, :*, AbstractAlgebra.expressify(c; context = context),
        Expr(:text, x))
      push!(sum.args, term)
    else
      term = Expr(:call, :*, AbstractAlgebra.expressify(c; context = context),
        Expr(:call, :^, Expr(:text, x), i))
      push!(sum.args, term)
    end
  end
  length(sum.args) == 1 && return sum.args[1]
  return sum
end

AbstractAlgebra.show_via_expressify(f::OrePoly) = true

function Base.show(io::IO, f::OrePoly)
  print(io, AbstractAlgebra.obj_to_string(f))
end

################################################################################
#
#  Scalar exact division and right GCD
#
################################################################################

# Left-divide all coefficients by scalar c (c must be invertible)
function divexact(f::OrePoly{T}, c::T; check::Bool = true) where {T}
  return OrePoly{T}(parent(f), T[a * inv(c) for a in f.coeffs])
end

@doc raw"""
    right_gcd(f::OrePoly{T}, g::OrePoly{T}) -> OrePoly{T}

Return the monic right GCD of `f` and `g`, i.e., the monic Ore polynomial
`d` of largest degree such that `f = a*d` and `g = b*d` for some Ore
polynomials `a`, `b`.
"""
function right_gcd(f::OrePoly{T}, g::OrePoly{T}) where {T}
  @req parent(f) == parent(g) "polynomials must have the same parent"
  R = parent(f)
  iszero(f) && iszero(g) && return zero(R)
  iszero(g) && return divexact(f, leading_coefficient(f))
  iszero(f) && return divexact(g, leading_coefficient(g))
  while !iszero(g)
    _, r = right_quo_rem(f, g)
    f, g = g, r
  end
  return divexact(f, leading_coefficient(f))
end
