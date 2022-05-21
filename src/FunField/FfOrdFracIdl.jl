export FfOrdFracIdl

################################################################################
#
#  Fractional Ideals
#
################################################################################

mutable struct FfOrdFracIdl
  order::GenericRound2.Order
  num::FfOrdIdl
  den::RingElem
  norm::RingElem
  basis_matrix::FakeFracFldMat
  basis_mat_inv::FakeFracFldMat

  function FfOrdFracIdl(O::GenericRound2.Order)
    z = new()
    z.order = O
    return z
  end

  function FfOrdFracIdl(a::FfOrdIdl, b::RingElem)
    z = new()
    z.order = order(a)
    b = Hecke.AbstractAlgebra.MPolyFactor.make_monic(b)
    z.num = a
    z.den = b
    return z
  end

   function FfOrdFracIdl(a::FfOrdIdl)
    z = new()
    O = order(a)
    z.order = order(a)
    z.num = a
    z.den = O.R(1)
    return z
  end


  function FfOrdFracIdl(O::GenericRound2.Order, a::FakeFracFldMat)
    z = new()
    z.order = O
    z.basis_matrix = a
    return z
  end
end

Hecke.order(a::FfOrdFracIdl) = a.order

function AbstractAlgebra.iszero(x::FfOrdFracIdl)
  return iszero(numerator(x))
end

################################################################################
#
#  Basis matrix
#
################################################################################

function assure_has_basis_matrix(a::FfOrdFracIdl)
  if isdefined(a, :basis_matrix)
    return nothing
  end
  if !isdefined(a, :num)
    error("Not a valid fractional ideal")
  end

  a.basis_matrix = FakeFracFldMat(basis_matrix(numerator(a, copy = false)), denominator(a))
  return nothing
end

function Hecke.basis_matrix(x::FfOrdFracIdl; copy::Bool = true)
  assure_has_basis_matrix(x)
  if copy
    return deepcopy(x.basis_matrix)
  else
    return x.basis_matrix
  end
end

################################################################################
#
#  Numerator and denominator
#
################################################################################

function assure_has_numerator_and_denominator(a::FfOrdFracIdl)
  if isdefined(a, :num) && isdefined(a, :den)
    return nothing
  end
  if !isdefined(a, :basis_matrix)
    error("Not a valid fractional ideal")
  end

  a.num = FfOrdIdl(order(a), numerator(basis_matrix(a, copy = false)))
  a.den = denominator(basis_matrix(a, copy = false))
  return nothing
end

function Base.numerator(x::FfOrdFracIdl; copy::Bool = true)
  assure_has_numerator_and_denominator(x)
  if copy
    return deepcopy(x.num)
  else
    return x.num
  end
end

function Base.denominator(x::FfOrdFracIdl; copy::Bool = true)
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


function Base.prod(a::T, b::T) where T <: FfOrdFracIdl
  A = a.num*b.num
  return FfOrdFracIdl(A, a.den*b.den)
end

Base.:*(A::T, B::T) where T <: FfOrdFracIdl = prod(A, B)


################################################################################
#
#  Powering
#
################################################################################

function Base.:^(A::FfOrdFracIdl, a::Int)
  
  O = order(A)
  if a == 0
    B = FfOrdFracIdl(ideal(order(A), 1), O.R(1))
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


function Hecke.simplify(A::FfOrdFracIdl)
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

Hecke.is_integral(I::FfOrdIdl) = true

function Hecke.is_integral(I::FfOrdFracIdl)
  simplify(I)
  return denominator(I) == 1
end

################################################################################
#
#  Ad hoc binary operations
#
################################################################################

function Base.:*(A::FfOrdIdl, B::FfOrdFracIdl)
  z = FfOrdFracIdl(A*numerator(B, copy = false), denominator(B))
  return z
end

Base.:*(A::FfOrdFracIdl, B::FfOrdIdl) = FfOrdFracIdl(numerator(A, copy = false)*B, denominator(A))


function Base.:*(x::GenericRound2.OrderElem, y::FfOrdFracIdl)
  #parent(x) !== order(y) && error("Orders of element and ideal must be equal")
  return FfOrdIdl(parent(x), x) * y
end

Base.:*(x::FfOrdFracIdl, y::GenericRound2.OrderElem) = y * x


################################################################################
#
#  Colon
#
################################################################################

function Hecke.colon(I::FfOrdFracIdl, J::FfOrdFracIdl)
  # Let I = a/c and J = b/d, a and b integral ideals, c, d \in Z, then
  # \{ x \in K | xJ \subseteq I \} = \{ x \in K | xcb \subseteq da \}

  O = order(I)
  II = numerator(I, copy = false)*O(denominator(J, copy = false))
  JJ = numerator(J, copy = false)*O(denominator(I, copy = false))
  return Hecke.colon(II, JJ)
end


