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
#  Equality
#
################################################################################

function ==(A::AlgAssAbsOrdFracIdl, B::AlgAssAbsOrdFracIdl)
  order(A) != order(B) && return false
  return basis_mat(A, false) == basis_mat(B, false)
end
