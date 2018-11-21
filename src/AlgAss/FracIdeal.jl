function isone(a::AlgAssAbsOrdFracIdl)
  a = simplify!(a)
  return isone(denominator(a, false)) && isone(numerator(a, false))
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
  print(io, basis_mat(a, false))
end

###############################################################################
#
#  Deepcopy
#
###############################################################################

function Base.deepcopy_internal(a::AlgAssAbsOrdFracIdl, dict::IdDict)
  b = typeof(a)(order(a), deepcopy(a.num), deepcopy(a.den))
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

function numerator(a::AlgAssAbsOrdFracIdl, copy::Bool = true)
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

function denominator(a::AlgAssAbsOrdFracIdl, copy::Bool = true)
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

function basis_mat(a::AlgAssAbsOrdFracIdl, copy::Bool = true)
  if !isdefined(a, :basis_mat)
    if !isdefined(a, :num) || !isdefined(a, :den)
      error("Numerator and/or denominator not defined")
    end
    a.basis_mat = FakeFmpqMat(basis_mat(a.num, Val{false}), a.den)
  end
  if copy
    return deepcopy(a.basis_mat)
  else
    return a.basis_mat
  end
end

function basis_mat_inv(a::AlgAssAbsOrdFracIdl, copy::Bool = true)
  if !isdefined(a, :basis_mat_inv)
    a.basis_mat_inv = inv(basis_mat(a, false))
  end
  if copy
    return deepcopy(a.basis_mat_inv)
  else
    return a.basis_mat_inv
  end
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

function frac_ideal_from_z_gens(O::AlgAssAbsOrd{S, T}, b::Vector{T}) where {S, T}
  d = degree(O)
  den = lcm([ denominator(bb) for bb in b ])
  num = ideal_from_z_gens(O, [ O(den*bb) for bb in b ])
  return frac_ideal(O, num, den)
end

################################################################################
#
#  Arithmetic
#
################################################################################

function +(a::AlgAssAbsOrdFracIdl{S, T}, b::AlgAssAbsOrdFracIdl{S, T}) where {S, T}
  d = lcm(denominator(a, false), denominator(b, false))
  ma = div(d, denominator(a, false))
  mb = div(d, denominator(b, false))
  return frac_ideal(order(a), numerator(a, false)*ma + numerator(b, false)*mb, d)
end

function *(a::AlgAssAbsOrdFracIdl{S, T}, b::AlgAssAbsOrdFracIdl{S, T}) where {S, T}
  d = denominator(a, false)*denominator(b, false)
  return frac_ideal(order(a), numerator(a, false)*numerator(b, false), d)
end

^(A::AlgAssAbsOrdFracIdl, e::Int) = Base.power_by_squaring(A, e)
^(A::AlgAssAbsOrdFracIdl, e::fmpz) = Base.power_by_squaring(A, BigInt(e))

################################################################################
#
#  Ad hoc binary operations
#
################################################################################

function +(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdFracIdl{S, T}) where {S, T}
  c = a*denominator(b, false) + numerator(b, false)
  return frac_ideal(order(a), c, denominator(b))
end

+(a::AlgAssAbsOrdFracIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T} = b + a

function *(a::AlgAssAbsOrdIdl{S, T}, b::AlgAssAbsOrdFracIdl{S, T}) where {S, T}
  return typeof(b)(order(a), a*numerator(b, false), denominator(b))
end

function *(a::AlgAssAbsOrdFracIdl{S, T}, b::AlgAssAbsOrdIdl{S, T}) where {S, T}
  return typeof(a)(order(a), numerator(a, false)*b, denominator(a))
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
  order(A) != order(B) && return false
  return basis_mat(A, false) == basis_mat(B, false)
end

################################################################################
#
#  Simplification
#
################################################################################

function simplify!(a::AlgAssAbsOrdFracIdl)
  b = basis_mat(numerator(a, false), Val{false})
  g = gcd(denominator(a, false), content(b))

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
  z = rand(numerator(a, false), B)
  return fmpq(1, denominator(a, false))*elem_in_algebra(z, Val{false})
end
