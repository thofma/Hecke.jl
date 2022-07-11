export GenOrdFracIdl

fractional_ideal(h::GenOrdIdl) = GenOrdFracIdl

################################################################################
#
#  Fractional Ideals
#
################################################################################

Hecke.order(a::GenOrdFracIdl) = a.order

function AbstractAlgebra.iszero(x::GenOrdFracIdl)
  return iszero(numerator(x))
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

  a.basis_matrix = FakeFracFldMat(basis_matrix(numerator(a, copy = false)), denominator(a))
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

@doc Markdown.doc"""
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
      z = z + K(B.num[i, j])*K(Oba[j])
    end
    z = divexact(z, B.den)
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




