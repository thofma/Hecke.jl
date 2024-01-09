fractional_ideal(h::GenOrdIdl) = GenOrdFracIdl(h)

function fractional_ideal(O::GenOrd, M::MatElem)
  @assert base_ring(M) == base_ring(function_field(O))
  return GenOrdFracIdl(O, M)
end

function Base.isone(A::GenOrdFracIdl)
  A = simplify(A)
  return isone(denominator(A)) && isone(numerator(A))
end

################################################################################
#
#  Fractional Ideals
#
################################################################################

Hecke.order(a::GenOrdFracIdl) = a.order

function_field(a::GenOrdFracIdl) = a.order.F

function AbstractAlgebra.iszero(x::GenOrdFracIdl)
  return iszero(numerator(x))
end

################################################################################
#
#  IO
#
################################################################################


function show(io::IO, id::GenOrdFracIdl)
  if isdefined(id, :num) && isdefined(id, :den)
    print(io, "1//(", denominator(id, copy = false), ") * ")
    print(io, numerator(id, copy = false))
  else
    print(io, "Fractional ideal of ",id.order ," with basis matrix\n")
    print(io, basis_matrix(id, copy = false))
  end
end

################################################################################
#
#  Basis matrix
#
################################################################################

function assure_has_basis_matrix(a::GenOrdFracIdl)
  if isdefined(a, :basis_matrix)
    return nothing
  end
  if !isdefined(a, :num)
    error("Not a valid fractional ideal")
  end

  k = base_field(function_field(order(a)))

  a.basis_matrix = divexact(change_base_ring(k, basis_matrix(numerator(a, copy = false))), k(denominator(a)))
  return nothing
end

function Hecke.basis_matrix(x::GenOrdFracIdl; copy::Bool = true)
  assure_has_basis_matrix(x)
  if copy
    return deepcopy(x.basis_matrix)
  else
    return x.basis_matrix
  end
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

function assure_has_numerator_and_denominator(a::GenOrdFracIdl)
  if isdefined(a, :num) && isdefined(a, :den)
    return nothing
  end
  if !isdefined(a, :basis_matrix)
    error("Not a valid fractional ideal")
  end

  B, d = integral_split(basis_matrix(a, copy = false), coefficient_ring(order(a)))
  a.num = GenOrdIdl(order(a), B)
  a.den = d
  return nothing
end

function Base.numerator(x::GenOrdFracIdl; copy::Bool = true)
  assure_has_numerator_and_denominator(x)
  return x.num
end

function Base.denominator(x::GenOrdFracIdl; copy::Bool = true)
  assure_has_numerator_and_denominator(x)
  if copy
    return deepcopy(x.den)
  else
    return x.den
  end
end



################################################################################
#
#  Binary operations
#
################################################################################


function Base.prod(a::T, b::T) where T <: GenOrdFracIdl
  A = numerator(a)*numerator(b)
  return GenOrdFracIdl(A, denominator(a)*denominator(b))
end

Base.:*(A::T, B::T) where T <: GenOrdFracIdl = prod(A, B)


################################################################################
#
#  Powering
#
################################################################################

function Base.:^(A::GenOrdFracIdl, a::Int)

  O = order(A)
  if a == 0
    B = GenOrdFracIdl(ideal(order(A), 1), O.R(1))
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
  g = gcd(denominator(A), content(b))

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
  return denominator(I) == 1
end

################################################################################
#
#  Ad hoc binary operations
#
################################################################################

function Base.:*(A::GenOrdIdl, B::GenOrdFracIdl)
  z = GenOrdFracIdl(A*numerator(B, copy = false), denominator(B))
  return z
end

Base.:*(A::GenOrdFracIdl, B::GenOrdIdl) = GenOrdFracIdl(numerator(A, copy = false)*B, denominator(A))


function Base.:*(x::GenOrdElem, y::GenOrdFracIdl)
  #parent(x) !== order(y) && error("GenOrds of element and ideal must be equal")
  return GenOrdIdl(parent(x), x) * y
end

Base.:*(x::GenOrdFracIdl, y::GenOrdElem) = y * x

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
    A.norm = norm(numerator(A, copy = false))//denominator(A, copy = false)^degree(order(A))
    return deepcopy(A.norm)
  end
end

################################################################################
#
#  Equality
#
################################################################################

function ==(A::GenOrdFracIdl, B::GenOrdFracIdl)
  D = inv(B)
  E = prod(A, D)
  C = simplify(E)
  return isone(denominator(C, copy = false)) && isone(norm(C))
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
  II = numerator(I, copy = false)*O(denominator(J, copy = false))
  JJ = numerator(J, copy = false)*O(denominator(I, copy = false))
  return Hecke.colon(II, JJ)
end

function Hecke.colon(I::GenOrdIdl, J::GenOrdFracIdl)
  return colon(fractional_ideal(I), J)
end

function Hecke.colon(I::GenOrdFracIdl, J::GenOrdIdl)
  return colon(I, fractional_ideal(J))
end

function inv(A::GenOrdFracIdl)
  O = order(A)
  return colon(O(1)*O, A)
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

  A_num = numerator(A)
  A_den = ideal(O, denominator(A))

  factors = factor(N)
  primes = Dict{GenOrdIdl,Int}()
  for (f,e) in factors
    for (p,r) in prime_decomposition(O,f)
      p_val = valuation(p,A_num) - valuation(p, A_den)
      if p_val != 0
        primes[p] = p_val
      end
    end
  end

  return primes
end

