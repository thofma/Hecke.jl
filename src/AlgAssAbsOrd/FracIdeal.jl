function isone(a::AlgAssAbsOrdFracIdl)
  a = simplify!(a)
  return isone(denominator(a, copy = false)) && isone(numerator(a, copy = false))
end

function one(S::AlgAssAbsOrdFracIdlSet)
  return frac_ideal(order(S), ideal(order(S), one(order(S))), fmpz(1))
end

function one(I::AlgAssAbsOrdFracIdl)
  return frac_ideal(order(I), ideal(order(I), one(order(I))), fmpz(1))
end

function Base.copy(I::AlgAssAbsOrdFracIdl)
  return I
end

###############################################################################
#
#  String I/O
#
###############################################################################

function show(io::IO, a::AlgAssAbsOrdFracIdl)
  print(io, "Fractional Ideal of ")
  show(IOContext(io, :compact => true), order(a))
  println(io, " with basis matrix ")
  print(io, basis_mat(a, copy = false))
end

###############################################################################
#
#  Deepcopy
#
###############################################################################

function Base.deepcopy_internal(a::AlgAssAbsOrdFracIdl, dict::IdDict)
  b = typeof(a)(order(a), numerator(a), denominator(a))
  for i in fieldnames(typeof(a))
    if isdefined(a, i)
      if i != :order && i != :num && i != :den
        setfield!(b, i, Base.deepcopy_internal(getfield(a, i), dict))
      end
    end
  end
  return b
end

###############################################################################
#
#  Field access
#
###############################################################################

order(a::AlgAssAbsOrdFracIdl) = a.order

function numerator(a::AlgAssAbsOrdFracIdl; copy::Bool = true)
  if !isdefined(a, :num)
    if !isdefined(a, :basis_mat)
      error("No basis matrix defined")
    end
    a.num = ideal(order(a), numerator(basis_mat(a)))
  end
  if copy
    return deepcopy(a.num)
  else
    return a.num
  end
end

function denominator(a::AlgAssAbsOrdFracIdl; copy::Bool = true)
  if !isdefined(a, :den)
    if !isdefined(a, :basis_mat)
      error("No basis matrix defined")
    end
    a.den = denominator(basis_mat(a))
  end
  if copy
    return deepcopy(a.den)
  else
    return a.den
  end
end

function basis_mat(a::AlgAssAbsOrdFracIdl; copy::Bool = true)
  if !isdefined(a, :basis_mat)
    if !isdefined(a, :num) || !isdefined(a, :den)
      error("Numerator and/or denominator not defined")
    end
    a.basis_mat = FakeFmpqMat(basis_mat(a.num, copy = false), a.den)
  end
  if copy
    return deepcopy(a.basis_mat)
  else
    return a.basis_mat
  end
end

function basis_mat_inv(a::AlgAssAbsOrdFracIdl; copy::Bool = true)
  if !isdefined(a, :basis_mat_inv)
    a.basis_mat_inv = inv(basis_mat(a, copy = false))
  end
  if copy
    return deepcopy(a.basis_mat_inv)
  else
    return a.basis_mat_inv
  end
end

################################################################################
#
#  Basis
#
################################################################################

function basis(a::AlgAssAbsOrdFracIdl)
  B = basis_mat(a, copy = false)
  O = order(a)
  A = algebra(O)
  d = dim(A)
  Oba = basis(O, copy = false)
  res = Array{elem_type(A)}(undef, d)

  for i in 1:d
    z = A()
    for j in 1:d
      z = z + B.num[i, j]*elem_in_algebra(Oba[j], copy = false)
    end
    z = divexact(z, A(B.den))
    res[i] = z
  end

  return res
end

################################################################################
#
#  Construction
#
################################################################################

function frac_ideal(O::AlgAssAbsOrd{S, T}, M::FakeFmpqMat, M_in_hnf::Bool = false) where {S, T}
  !M_in_hnf ? M = hnf(M, :lowerleft) : nothing

  return AlgAssAbsOrdFracIdl{S, T}(O, M)
end

function frac_ideal(O::AlgAssAbsOrd{S, T}, a::AlgAssAbsOrdIdl{S, T}, d::fmpz) where {S, T}
  return AlgAssAbsOrdFracIdl{S, T}(O, a, d)
end

function frac_ideal(O::AlgAssAbsOrd{S, T}, a::T) where {S, T}
  d = denominator(a, O)
  return frac_ideal(O, ideal(O, O(d*a)), d)
end

*(O::AlgAssAbsOrd{S, T}, a::T) where {S, T} = frac_ideal(O, a)
*(a::T, O::AlgAssAbsOrd{S, T}) where {S, T} = frac_ideal(O, a)

function frac_ideal_from_z_gens(O::AlgAssAbsOrd{S, T}, b::Vector{T}) where {S, T}
  d = degree(O)
  den = lcm([ denominator(bb, O) for bb in b ])
  num = ideal_from_z_gens(O, [ O(den*bb) for bb in b ])
  return frac_ideal(O, num, den)
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(a::AlgAssAbsOrdFracIdl{S, T}, b::AlgAssAbsOrdFracIdl{S, T}) where {S, T}
  d = lcm(denominator(a, copy = false), denominator(b, copy = false))
  ma = div(d, denominator(a, copy = false))
  mb = div(d, denominator(b, copy = false))
  return frac_ideal(order(a), numerator(a, copy = false)*ma + numerator(b, copy = false)*mb, d)
end

function *(a::AlgAssAbsOrdFracIdl{S, T}, b::AlgAssAbsOrdFracIdl{S, T}) where {S, T}
  d = denominator(a, copy = false)*denominator(b, copy = false)
  return frac_ideal(order(a), numerator(a, copy = false)*numerator(b, copy = false), d)
end

^(A::AlgAssAbsOrdFracIdl, e::Int) = Base.power_by_squaring(A, e)
^(A::AlgAssAbsOrdFracIdl, e::fmpz) = Base.power_by_squaring(A, BigInt(e))

################################################################################
#
#  Ad hoc binary operations
#
################################################################################

function +(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdFracIdl{S, T}) where {S, T}
  c = a*denominator(b, copy = false) + numerator(b, copy = false)
  return frac_ideal(order(a), c, denominator(b))
end

+(a::AlgAssAbsOrdFracIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T} = b + a

function *(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdFracIdl{S, T}) where {S, T}
  return typeof(b)(order(a), a*numerator(b, copy = false), denominator(b))
end

function *(a::AlgAssAbsOrdFracIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  return typeof(a)(order(a), numerator(a, copy = false)*b, denominator(a))
end

function *(x::T, a::AlgAssAbsOrdFracIdl{S, T}) where {S, T}
  O = order(a)
  return frac_ideal(O, x)*a
end

function *(a::AlgAssAbsOrdFracIdl{S, T}, x::T) where {S, T}
  O = order(a)
  return a*frac_ideal(O, x)
end

function *(x::T, a::AlgAssAbsOrdIdl{S, T}) where {S, T}
  O = order(a)
  return frac_ideal(O, x)*a
end

function *(a::AlgAssAbsOrdIdl{S, T}, x::T) where {S, T}
  O = order(a)
  return a*frac_ideal(O, x)
end

################################################################################
#
#  Equality
#
################################################################################

function ==(A::AlgAssAbsOrdFracIdl, B::AlgAssAbsOrdFracIdl)
  order(A) !== order(B) && return false
  return basis_mat(A, copy = false) == basis_mat(B, copy = false)
end

################################################################################
#
#  Simplification
#
################################################################################

function simplify!(a::AlgAssAbsOrdFracIdl)
  b = basis_mat(numerator(a, copy = false), copy = false)
  g = gcd(denominator(a, copy = false), content(b))

  if g != 1
    a.num = divexact(a.num, g)
    a.den = divexact(a.den, g)
  end

  return a
end

################################################################################
#
#  Random elements
#
################################################################################

function rand(a::AlgAssAbsOrdFracIdl, B::Int)
  z = rand(numerator(a, copy = false), B)
  return fmpq(1, denominator(a, copy = false))*elem_in_algebra(z, copy = false)
end

################################################################################
#
#  Inclusion of elements
#
################################################################################

function in(x::AbsAlgAssElem, a::AlgAssAbsOrdFracIdl)
  O = order(a)
  M = zero_matrix(FlintZZ, 1, degree(O))
  t = FakeFmpqMat(M)
  elem_to_mat_row!(t.num, 1, t.den, x)
  v = t*basis_mat_inv(O, copy = false)
  v = v*basis_mat_inv(a, copy = false)

  return v.den == 1
end

################################################################################
#
#  Colon
#
################################################################################

function colon(I::AlgAssAbsOrdFracIdl, J::AlgAssAbsOrdFracIdl)
  # Let I = a/c and J = b/d, a and b integral ideals, c, d \in Z, then
  # \{ x \in K | xJ \subseteq I \} = \{ x \in K | xcb \subseteq da \}

  II = numerator(I, copy = false)*denominator(J, copy = false)
  JJ = numerator(J, copy = false)*denominator(I, copy = false)
  return colon(II, JJ)
end

################################################################################
#
#  Move ideals to another order
#
################################################################################

function extend(I::AlgAssAbsOrdFracIdl, O::AlgAssAbsOrd)
  J = extend(numerator(I, copy = false), O)
  return frac_ideal(O, J, denominator(I, copy = false))
end

*(I::AlgAssAbsOrdFracIdl, O::AlgAssAbsOrd) = extend(I, O)
*(O::AlgAssAbsOrd, I::AlgAssAbsOrdFracIdl) = extend(I, O)

function _as_frac_ideal_of_smaller_order(O::AlgAssAbsOrd, I::AlgAssAbsOrdIdl)
  M = basis_mat(I, copy = false)
  M = M*basis_mat(order(I), copy = false)*basis_mat_inv(O, copy = false)
  return frac_ideal(O, M)
end

function _as_frac_ideal_of_smaller_order(O::AlgAssAbsOrd, I::AlgAssAbsOrdFracIdl)
  J = _as_frac_ideal_of_smaller_order(O, numerator(I, copy = false))
  return algebra(O)(fmpq(1, denominator(I, copy = false)))*J
end

################################################################################
#
#  Ideal Set
#
################################################################################

function show(io::IO, a::AlgAssAbsOrdFracIdlSet)
  print(io, "Set of fractional ideals of $(order(a))")
end

order(a::AlgAssAbsOrdFracIdlSet) = a.order

parent(I::AlgAssAbsOrdFracIdl) = AlgAssAbsOrdFracIdlSet(order(I))

function FracIdealSet(O::AlgAssAbsOrd)
   return AlgAssAbsOrdFracIdlSet(O)
end

elem_type(::Type{AlgAssAbsOrdFracIdlSet{S, T}}) where {S, T} = AlgAssAbsOrdFracIdl{S, T}

elem_type(::AlgAssAbsOrdFracIdlSet{S, T}) where {S, T} = AlgAssAbsOrdFracIdl{S, T}

parent_type(::Type{AlgAssAbsOrdFracIdl{S, T}}) where {S, T} = AlgAssAbsOrdFracIdlSet{S, T}
