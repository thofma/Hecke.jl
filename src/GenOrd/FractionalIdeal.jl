################################################################################
#
#  Fractional Ideals
#
################################################################################

Hecke.order(a::GenOrdFracIdl) = a.order

function_field(a::GenOrdFracIdl) = a.order.F

fractional_ideal(h::GenOrdIdl) = GenOrdFracIdl(h)

function fractional_ideal(O::GenOrd, M::MatElem)
  @assert base_ring(M) == base_field(function_field(O))
  return GenOrdFracIdl(O, M)
end

function is_one(A::GenOrdFracIdl)
  A = simplify(A)
  return is_one(denominator(A; copy = false)) && is_one(numerator(A; copy = false))
end

function is_zero(x::GenOrdFracIdl)
  return is_zero(numerator(x; copy = false))
end

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

function assure_has_basis_matrix(a::GenOrdFracIdl{S, T}) where {S, T}
  isdefined(a, :basis_matrix) && return nothing
  isdefined(a, :num) || error("Not a valid fractional ideal")

  k = base_field(field(order(a)))::base_field_type(S)
  a.basis_matrix = divexact(change_base_ring(k, basis_matrix(numerator(a; copy = false))), k(denominator(a)))
  return nothing
end

function Hecke.basis_matrix(x::GenOrdFracIdl{S, T}; copy::Bool = true) where {S, T}
  assure_has_basis_matrix(x)

  M = x.basis_matrix::dense_matrix_type(elem_type(base_field_type(S)))
  return copy ? deepcopy(M) : M
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

function assure_has_numerator_and_denominator(a::GenOrdFracIdl{S, T}) where {S, T}
  if isdefined(a, :num) && isdefined(a, :den)
    return nothing
  end
  if !isdefined(a, :basis_matrix)
    error("Not a valid fractional ideal")
  end

  B, d = integral_split(basis_matrix(a; copy = false), coefficient_ring(order(a)))
  a.num = ideal(order(a), B)
  a.den = d::elem_type(T)
  return nothing
end

function Base.numerator(x::GenOrdFracIdl{S, T}; copy::Bool = true) where {S, T}
  assure_has_numerator_and_denominator(x)
  return (copy ? deepcopy(x.num) : x.num)::GenOrdIdl{S, T}
end

function Base.denominator(x::GenOrdFracIdl{S, T}; copy::Bool = true) where {S, T}
  assure_has_numerator_and_denominator(x)
  return (copy ? deepcopy(x.den) : x.den)::elem_type(T)
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


function Base.prod(a::GenOrdFracIdl{S, T}, b::GenOrdFracIdl{S, T}) where {S, T}
  @req order(a) === order(b) "Ideals must have same order"

  A = numerator(a; copy = false)*numerator(b; copy = false)
  return GenOrdFracIdl(A, denominator(a; copy = false)*denominator(b; copy = false))
end

function Base.:*(a::GenOrdFracIdl{S, T}, b::GenOrdFracIdl{S, T}) where {S, T}
  return prod(a, b)
end

function Base.:(+)(a::GenOrdFracIdl{S, T}, b::GenOrdFracIdl{S, T}) where {S, T}
  @req order(a) === order(b) "Ideals must have same order"

  den_a, den_b = denominator(a; copy=false), denominator(b; copy=false)
  d = lcm(den_a, den_b)

  I = _ideal_by_scaling_matrix(divexact(d, den_a), numerator(a; copy=false))
  J = _ideal_by_scaling_matrix(divexact(d, den_b), numerator(b; copy=false))
  return GenOrdFracIdl(I + J, d)
end

function Base.intersect(a::GenOrdFracIdl{S, T}, b::GenOrdFracIdl{S, T}) where {S, T}
  @req order(a) === order(b) "Ideals must have same order"

  den_a, den_b = denominator(a; copy=false), denominator(b; copy=false)
  d = lcm(den_a, den_b)

  I = _ideal_by_scaling_matrix(divexact(d, den_a), numerator(a; copy=false))
  J = _ideal_by_scaling_matrix(divexact(d, den_b), numerator(b; copy=false))
  return GenOrdFracIdl(intersect(I, J), d)
end

################################################################################
#
#  Powering
#
################################################################################

function Base.:^(A::GenOrdFracIdl, a::Int)

  O = order(A)
  if a == 0
    B = GenOrdFracIdl(ideal(order(A), one(O)), O.R(1))
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
  assure_has_numerator_and_denominator(A)
  if isone(A.den)
    return A
  end

  b = basis_matrix(A.num)
  g = gcd(denominator(A; copy = false), content(b))

  if g != 1
    A.num = divexact(A.num, g)
    A.den = divexact(A.den, g)
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

function Base.:*(A::GenOrdIdl{S, T}, B::GenOrdFracIdl{S, T}) where {S, T}
  @req order(A) === order(B) "Ideals must have same order"
  return GenOrdFracIdl(A*numerator(B; copy = false), denominator(B; copy = false))
end

function Base.:*(A::GenOrdFracIdl{S, T}, B::GenOrdIdl{S, T}) where {S, T}
  @req order(A) === order(B) "Ideals must have same order"
  return GenOrdFracIdl(numerator(A; copy = false)*B, denominator(A; copy = false))
end

function Base.:*(x::GenOrdElem, I::GenOrdFracIdl)
  O = order(I)
  @req parent(x) === O "Element and ideal must belong to the same order"

  if _is_in_base_field(x)
    c, den = integral_split(coeff(data(x), 0), base_ring(O))
    @assert is_one(den)

    num = _ideal_by_scaling_matrix(c, numerator(I; copy = false))
    return GenOrdFracIdl(num, denominator(I; copy = false))
  end

  return ideal(O, x) * I
end

function Base.:*(x::FieldElem, O::GenOrd)
  @req parent(x) === field(O) "Element must lie in the field of the order"
  x_num, x_denom = integral_split(x, O)
  return GenOrdFracIdl(ideal(O, x_num), x_denom)
end

function Base.:*(c::Generic.RationalFunctionFieldElem, I::GenOrdFracIdl)
  @req parent(c) === base_field(function_field(order(I))) "scalar must lie in the base field of the function field"
  return GenOrdFracIdl(order(I), c * basis_matrix(I; copy = false))
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
    norm(I::GenOrdFracIdl) -> GenOrd

Returns the norm of $I$.
"""
function norm(A::GenOrdFracIdl)
  if isdefined(A, :norm)
    return deepcopy(A.norm)
  else
    A.norm = norm(numerator(A; copy = false))//denominator(A; copy = false)^degree(order(A))
    return deepcopy(A.norm)
  end
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
  C = simplify(A * inv(B))
  return isone(denominator(C; copy = false)) && isone(norm(C))
end

function ==(A::GenOrdFracIdl{S, T}, B::GenOrdIdl{S, T}) where {S, T}
  return A == fractional_ideal(B)
end

function ==(A::GenOrdIdl{S, T}, B::GenOrdFracIdl{S, T}) where {S, T}
  return fractional_ideal(A) == B
end

function Base.hash(A::GenOrdFracIdl, h::UInt)
  return hash(order(A), hash(basis_matrix(A), h))
end

################################################################################
#
#  Colon
#
################################################################################

function Hecke.colon(I::GenOrdFracIdl, J::GenOrdFracIdl)
  # Let I = a/c and J = b/d, a and b integral ideals, c, d \in Z, then
  # \{ x \in K | xJ \subseteq I \} = \{ x \in K | xcb \subseteq da \}

  O = order(I)
  II = numerator(I; copy = false)*O(denominator(J; copy = false))
  JJ = numerator(J; copy = false)*O(denominator(I; copy = false))
  return Hecke.colon(II, JJ)
end

function Hecke.colon(I::GenOrdIdl, J::GenOrdFracIdl)
  return colon(fractional_ideal(I), J)
end

function Hecke.colon(I::GenOrdFracIdl, J::GenOrdIdl)
  return colon(I, fractional_ideal(J))
end

function inv(A::GenOrdFracIdl)
  # inv(N/d) = d * inv(N): factor the scalar denominator out
  #   instead of routing the whole fractional ideal through colon
  #   which involves O(denominator) and extra ideal arithmetic
  O = order(A)
  k = base_field(field(O))

  invN = inv(numerator(A; copy = false))
  M = k(denominator(A; copy = false)) * basis_matrix(invN; copy = false)
  return GenOrdFracIdl(O, M)
end

Base.://(I::GenOrdFracIdl, J::GenOrdFracIdl) = colon(I, J)

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
