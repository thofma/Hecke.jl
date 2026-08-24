################################################################################
#
#  Fractional Ideals
#
################################################################################

Hecke.order(a::GenOrdFracIdl) = a.order

function_field(a::GenOrdFracIdl) = a.order.F

function is_one(A::GenOrdFracIdl)
  is_zero(A) && return false

  d = denominator(A; copy = false)
  # A = I/d = O iff I = d*O
  if isdefined(A, :num)
    # intersection of A and R is minimum(A)*R. minimum(A) = d gives d*O subset I
    minimum(A.num; copy = false) == d || return false
    # this gives I subset d*O
    return is_one(norm(A; copy = false))
  end

  A = simplify(A)
  return is_one(denominator(A; copy = false)) && is_one(norm(A; copy = false))
end

function is_zero(A::GenOrdFracIdl)
  return isdefined(A, :num) ? is_zero(A.num) : is_zero(_basis_matrix_numerator(A))
end

################################################################################
#
#  Constructors
#
################################################################################

@doc raw"""
    fractional_ideal(I::GenOrdIdl) -> GenOrdFracIdl
    fractional_ideal(I::GenOrdIdl, d::RingElement) -> GenOrdFracIdl

Return the fractional ideal $I/d$ of `order(I)`, where $d = 1$ by default.
"""
function fractional_ideal(I::GenOrdIdl)
  R = coefficient_ring(order(I))
  return GenOrdFracIdl(I, one(R))
end

function fractional_ideal(I::GenOrdIdl, d::RingElement)
  R = coefficient_ring(order(I))

  d = R(d)
  @req !is_zero(d) "denominator must be non-zero"
  return GenOrdFracIdl(I, d)
end

@doc raw"""
    fractional_ideal(O::GenOrd, M::MatElem, d::RingElement) -> GenOrdFracIdl

Return the fractional ideal of $O$ with basis matrix $M/d$, where the entries of
$M$ lie in the coefficient ring of $O$. The rows of $M$ must be a basis of the
numerator module; no canonical form is assumed.
"""
function fractional_ideal(O::GenOrd, M::MatElem, d::RingElement)
  n = degree(O)
  R = coefficient_ring(O)
  @req base_ring(M) === R "basis matrix numerator must be over the coefficient ring of the order"
  @req nrows(M) == n && ncols(M) == n "basis matrix numerator must be square of size degree(O) = $n"

  d = R(d)
  @req !is_zero(d) "denominator must be non-zero"

  return _fractional_ideal_from_basis_matrix(O, M, d; reduced = false)
end

@doc raw"""
    fractional_ideal(O::GenOrd, M::MatElem) -> GenOrdFracIdl

Return the fractional ideal of $O$ with basis matrix $M$, where the entries of
$M$ lie in the base field of `field(O)`.
"""
function fractional_ideal(O::GenOrd, M::MatElem)
  n = degree(O)
  @req base_ring(M) === base_field(field(O)) "basis matrix must be over the base field of the order"
  @req nrows(M) == n && ncols(M) == n "basis matrix must be square of size degree(O) = $n"

  M, d = integral_split(M, coefficient_ring(O))
  return _fractional_ideal_from_basis_matrix(O, M, d; reduced = false)
end

fractional_ideal(I::GenOrdFracIdl) = I

################################################################################
#
#  IO
#
################################################################################


function show(io::IO, id::GenOrdFracIdl)
  if isdefined(id, :num) && isdefined(id, :den)
    print(io, "1//(", denominator(id; copy = false), ") * ")
    print(io, numerator(id; copy = false))
  else
    print(io, "Fractional ideal of ",id.order ," with basis matrix\n")
    print(io, basis_matrix(id; copy = false))
  end
end

################################################################################
#
#  Basis matrix
#
################################################################################

function _assure_has_basis_matrix(I::GenOrdFracIdl{S, T}) where {S, T}
  isdefined(I, :basis_matrix) && return nothing
  @assert isdefined(I, :den) "Not a valid fractional ideal"

  bm = _numerator_matrix(I)
  k = base_field(field(order(I)))::base_field_type(S)
  I.basis_matrix = divexact(change_base_ring(k, bm), k(denominator(I; copy = false)))
  return nothing
end

function Hecke.basis_matrix(I::GenOrdFracIdl{S, T}; copy::Bool = true) where {S, T}
  _assure_has_basis_matrix(I)

  M = I.basis_matrix::dense_matrix_type(elem_type(base_field_type(S)))
  return copy ? deepcopy(M) : M
end

function _basis_matrix_pair(I::GenOrdFracIdl{S, T}) where {S, T}
  return (_basis_matrix_numerator(I), I.den::elem_type(T))
end

function _assure_has_basis_matrix_inv(I::GenOrdFracIdl{S, T}) where {S, T}
  isdefined(I, :basis_matrix_inv_num) && return nothing

  # basis_matrix(a) = N/d, so its inverse is d*N^{-1}
  K = base_field(field(order(I)))::base_field_type(S)
  X, e = _inv_pair(_basis_matrix_numerator(I), K)
  I.basis_matrix_inv_num, I.basis_matrix_inv_den = _strip_pair_content(denominator(I; copy = false)*X, e)

  return nothing
end

function _basis_matrix_inv_pair(I::GenOrdFracIdl{S, T}) where {S, T}
  _assure_has_basis_matrix_inv(I)
  return (I.basis_matrix_inv_num::dense_matrix_type(elem_type(T)), I.basis_matrix_inv_den::elem_type(T))
end

################################################################################
#
#  Basis
#
################################################################################

@doc raw"""
    basis(I::GenOrdFracIdl) -> Vector{FunFieldElem}

Returns the basis over the maximal Order of $I$.
"""
function basis(a::GenOrdFracIdl)
  B = basis_matrix(a)
  d = degree(order(a))
  O = order(a)
  K = function_field(O)
  Oba = basis(O)
  res = Array{elem_type(K)}(undef, d)
  for i in 1:d
    z = K()
    for j in 1:d
      z = z + B[i, j]*K(Oba[j])
    end
    res[i] = z
  end

  return res
end

################################################################################
#
#  Numerator and denominator
#
################################################################################

function _assure_has_numerator(a::GenOrdFracIdl)
  isdefined(a, :num) && return nothing
  @assert isdefined(a, :basis_matrix_num) "Not a valid fractional ideal"

  a.num = ideal(order(a), _basis_matrix_numerator(a))
  return nothing
end

function Base.numerator(x::GenOrdFracIdl{S, T}; copy::Bool = true) where {S, T}
  _assure_has_numerator(x)
  return (copy ? deepcopy(x.num) : x.num)::GenOrdIdl{S, T}
end

function Base.denominator(x::GenOrdFracIdl{S, T}; copy::Bool = true) where {S, T}
  @assert isdefined(x, :den)
  return (copy ? deepcopy(x.den) : x.den)::elem_type(T)
end

function _assure_has_basis_matrix_numerator(a::GenOrdFracIdl{S, T}) where {S, T}
  isdefined(a, :basis_matrix_num) && return nothing
  @assert isdefined(a, :num) "Not a valid fractional ideal"

  # NOTE: this aliases the cached basis matrix of a.num; should not be mutated in place
  a.basis_matrix_num = basis_matrix(a.num; copy = false)
  return nothing
end

function _basis_matrix_numerator(a::GenOrdFracIdl{S, T}) where {S, T}
  _assure_has_basis_matrix_numerator(a)
  return a.basis_matrix_num::dense_matrix_type(elem_type(T))
end

# Numerator matrix without populating the cache
function _numerator_matrix(a::GenOrdFracIdl)
  @assert isdefined(a, :num) || isdefined(a, :basis_matrix_num) "Not a valid fractional ideal"

  if isdefined(a, :basis_matrix_num)
    return _basis_matrix_numerator(a)
  else
    return basis_matrix(a.num; copy = false)
  end
end

################################################################################
#
#  Containment
#
################################################################################

function Base.in(x::FieldElem, A::GenOrdFracIdl)
  O = order(A)
  @req parent(x) === field(O) "Element must be in field(order(A))"
  # x is in I/d iff d*x is in I (and integral)
  # note that den lives in the order ring, which lies in the base field
  K  = field(O)
  den = K(base_field(K)(denominator(A; copy = false)))
  y = x * den
  dy = integral_split(y, O)[2]
  return isone(dy) && O(y; check = false) in numerator(A; copy = false)
end

Base.in(x::GenOrdElem, A::GenOrdFracIdl) = data(x) in A

################################################################################
#
#  Binary operations
#
################################################################################


function Base.:(+)(a::GenOrdFracIdl{S, T}, b::GenOrdFracIdl{S, T}) where {S, T}
  @req order(a) === order(b) "Ideals must have same order"

  den_a, den_b = denominator(a; copy=false), denominator(b; copy=false)
  d = lcm(den_a, den_b)

  I = _ideal_by_scaling_matrix(divexact(d, den_a), numerator(a; copy=false))
  J = _ideal_by_scaling_matrix(divexact(d, den_b), numerator(b; copy=false))
  return fractional_ideal(I + J, d)
end

function Base.intersect(a::GenOrdFracIdl{S, T}, b::GenOrdFracIdl{S, T}) where {S, T}
  @req order(a) === order(b) "Ideals must have same order"

  den_a, den_b = denominator(a; copy=false), denominator(b; copy=false)
  d = lcm(den_a, den_b)

  I = _ideal_by_scaling_matrix(divexact(d, den_a), numerator(a; copy=false))
  J = _ideal_by_scaling_matrix(divexact(d, den_b), numerator(b; copy=false))
  return fractional_ideal(intersect(I, J), d)
end

################################################################################
#
#  Powering
#
################################################################################

function Base.:^(A::GenOrdFracIdl, a::Int)

  O = order(A)
  if a == 0
    B = fractional_ideal(ideal(order(A), one(O)), O.R(1))
    return B
  end

  if a == 1
    return A
  end

  if a < 0
    return inv(A^(-a))
  end

  if a == 2
    return A*A
  end

  if mod(a, 2) == 0
    return (A^div(a, 2))^2
  else
    return A * A^(a - 1)
  end
end


################################################################################
#
#  Simplification
#
################################################################################


function Hecke.simplify(A::GenOrdFracIdl)
  is_one(denominator(A; copy = false)) && return A

  # The content is a module invariant, so any numerator representation can be used.
  # Simplify does NOT change basis_matrix or norm.
  # TODO: check two-element representation of numerator, if we can avoid basis matrix materialization
  N = _numerator_matrix(A)
  den = denominator(A; copy = false)
  g = _make_canonical_in(order(A), gcd(den, content(N)))
  is_one(g) && return A

  A.basis_matrix_num = divexact(N, g)
  A.den = divexact(den, g)
  if isdefined(A, :num)
    A.num = divexact(A.num, g)
  end

  return A
end

################################################################################
#
#   Is integral
#
################################################################################

Hecke.is_integral(I::GenOrdIdl) = true

function Hecke.is_integral(I::GenOrdFracIdl)
  simplify(I)
  return is_one(denominator(I; copy = false))
end

################################################################################
#
#  Ad hoc binary operations
#
################################################################################

# scale ideal by the base field element: this is simple scalar multiplication,
#   and it preserves HNF form
function _scale_by_base_field_scalar(I::GenOrdFracIdl, c)
  O = order(I)
  c_num, c_den = integral_split(c, coefficient_ring(O))
  I_den = c_den * denominator(I; copy = false)

  is_zero(c_num) && return fractional_ideal(ideal(O, c_num), I_den)
  if isdefined(I, :num)
    return fractional_ideal(_ideal_by_scaling_matrix(c_num, I.num), I_den)
  else
    return fractional_ideal(O, c_num*_numerator_matrix(I), I_den)
  end
end

function Base.:*(x::GenOrdElem, I::GenOrdFracIdl)
  O = order(I)
  @req parent(x) === O "Element and ideal must belong to the same order"

  if _is_in_base_field(x)
    return _scale_by_base_field_scalar(I, coeff(data(x), 0))
  end

  return ideal(O, x) * I
end

function Base.:*(x::FieldElem, O::GenOrd)
  @req parent(x) === field(O) "Element must lie in the field of the order"
  x_num, x_denom = integral_split(x, O)
  return fractional_ideal(ideal(O, x_num), x_denom)
end

function Base.:*(c::Generic.RationalFunctionFieldElem, I::GenOrdFracIdl)
  @req parent(c) === base_field(field(order(I))) "scalar must lie in the base field of the function field"
  return _scale_by_base_field_scalar(I, c)
end

# multiplying by field element always returns fractional ideal (for type stability)
function Base.:*(c::Generic.RationalFunctionFieldElem, I::GenOrdIdl)
  return c * fractional_ideal(I)
end

Base.:*(I::GenOrdFracIdl, x::GenOrdElem) = x * I
Base.:*(O::GenOrd, f::FieldElem) = f * O
Base.:*(I::GenOrdFracIdl, c::Generic.RationalFunctionFieldElem) = c * I
Base.:*(I::GenOrdIdl, c::Generic.RationalFunctionFieldElem) = c * I

################################################################################
#
#  Norm
#
################################################################################

@doc raw"""
    norm(I::GenOrdFracIdl; copy::Bool = true) -> FieldElem

Returns the norm of $I$.
"""
function norm(A::GenOrdFracIdl{S, T}; copy::Bool = true) where {S, T}
  if !isdefined(A, :norm)
    O = order(A)

    num = if isdefined(A, :num)
      norm(numerator(A; copy = false); copy = false)
    else
      _make_canonical_in(O, det(_basis_matrix_numerator(A)))
    end

    A.norm = num // denominator(A; copy = false)^degree(O)
  end

  # The norm of a fractional ideal is a quotient of two coefficient ring elements,
  #   and it has to stay in the fraction field of the *coefficient* ring:
  #   for example, factor() splits it into numerator and denominator and hands the parts to
  #   prime_decomposition, which for the infinite order needs KInftyRing elements
  #   rather than k[x] polynomials.
  # Since we consider orders as extensions of the fraction field (of coefficient ring),
  #   this is sound mathematically too. For the infinite order (KInftyRing),
  #   the coefficient ring is not k[x]
  # NOTE: Nemo's fraction_field(ZZ) returns QQField, so we special case here
  _norm_elem_type(::Type{R}) where {R <: Ring} = elem_type(fraction_field_type(R))
  _norm_elem_type(::Type{ZZRing}) = QQFieldElem
  return (copy ? deepcopy(A.norm) : A.norm)::_norm_elem_type(T)
end

################################################################################
#
#  Copy
#
################################################################################

function Base.deepcopy_internal(I::GenOrdFracIdl{S, T}, dict::IdDict) where {S, T}
  J = GenOrdFracIdl(order(I))
  for f in fieldnames(typeof(I))
    f === :order && continue
    if isdefined(I, f)
      setfield!(J, f, Base.deepcopy_internal(getfield(I, f), dict))
    end
  end
  return J
end

################################################################################
#
#  Equality
#
################################################################################

function ==(A::GenOrdFracIdl{S, T}, B::GenOrdFracIdl{S, T}) where {S, T}
  order(A) === order(B) || return false

  is_zero(A) && return is_zero(B)
  is_zero(B) && return false

  O = order(A)
  if is_maximal_known_and_maximal(O)
    return is_one(A * inv(B))
  else
    da = denominator(A; copy = false)
    db = denominator(B; copy = false)
    d  = lcm(da, db)

    I = O(divexact(d, da)) * numerator(A; copy = false)
    J = O(divexact(d, db)) * numerator(B; copy = false)
    return I == J
  end
end

function ==(A::GenOrdFracIdl{S, T}, B::GenOrdIdl{S, T}) where {S, T}
  return A == fractional_ideal(B)
end

function ==(A::GenOrdIdl{S, T}, B::GenOrdFracIdl{S, T}) where {S, T}
  return fractional_ideal(A) == B
end

function Base.hash(A::GenOrdFracIdl, h::UInt)
  n = norm(A; copy = false)
  n_num, n_den = numerator(n), denominator(n)
  return hash(n_num, hash(n_den, hash(order(A), h)))
end

################################################################################
#
#  Factor
#
################################################################################

function Hecke.factor(A::GenOrdFracIdl)
  O = A.order
  N = numerator(norm(A)) * denominator(norm(A))

  A_num = numerator(A; copy = false)
  A_den = ideal(O, denominator(A; copy = false))

  factors = factor(N)
  primes = Dict{GenOrdIdl,Int}()
  for (f,e) in factors
    for (p,r) in prime_decomposition(O,f)
      p_val = valuation(A_num, p) - valuation(A_den, p)
      if p_val != 0
        primes[p] = p_val
      end
    end
  end

  return primes
end

function Hecke.valuation(A::GenOrdFracIdl{S, T}, p::GenOrdIdl{S, T}) where {S, T}
  O = A.order
  A_num = numerator(A; copy = false)
  A_den = ideal(O, denominator(A; copy = false))
  return valuation(A_num, p) - valuation(A_den, p)
end
