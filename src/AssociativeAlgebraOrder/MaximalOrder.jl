is_maximal_known(O::AssociativeAlgebraOrder) = O.is_maximal != 0

is_known(::typeof(is_maximal), O::AssociativeAlgebraOrder) = is_maximal_known(O)

@inline is_maximal_known_and_maximal(O::AssociativeAlgebraOrder) = isone(O.is_maximal)

@doc raw"""
    is_maximal(O::AssociativeAlgebraOrder) -> Bool

Returns `true` if $O$ is a maximal order and `false` otherwise.
"""
function is_maximal(O::AssociativeAlgebraOrder)
  if O.is_maximal == 1
    return true
  end
  if O.is_maximal == 2
    return false
  end

  A = algebra(O)
  d = discriminant(O)
  if isdefined(A, :maximal_order)
    if d == discriminant(maximal_order(A))
      O.is_maximal = 1
      return true
    else
      O.is_maximal = 2
      return false
    end
  end

  if typeof(A) <: GroupAlgebra
    fac = factor(degree(O))
  else
    fac = factor(abs(d))
  end

  for (p, j) in fac
    # This can be improved a bit. Even in the GroupAlgebra case, we should
    # only look at the primes dividing d with power > 1
    if !(typeof(A) <: GroupAlgebra) && j == 1
      continue
    end
    d2 = discriminant(pmaximal_overorder(O, p))
    if d != d2
      O.is_maximal = 2
      return false
    end
  end
  O.is_maximal = 1
  return true
end

function new_maximal_order(O::AssociativeAlgebraOrder, cache_in_substructures::Bool = true)
  A = algebra(O)

  if false degree(O) >= 30 && !is_simple(A)
    OO = _maximal_order_via_decomposition(O, cache_in_substructures)
  else
    d = discriminant(O)
    @vtime :AbsNumFieldOrder fac = factor(d)

    OO = O
    for (p, j) in fac
      if !is_divisible_by(d, p^2)
        continue
      end
      OO += pmaximal_overorder(O, p)
    end
    OO.is_maximal = 1
  end

  # TODO: fix this nonsense
  # if !isdefined(A, :maximal_order)
  #   A.maximal_order = [OO]
  # else
  #   push!(A.maximal_order, OO)
  # end
  return OO
end

#function maximal_order(O::AlgAssAbsOrd{T, S}) where { S <: GroupAlgebra, T <: GroupAlgebraElem }
#  A = algebra(O)
#
#  if isdefined(A, :maximal_order)
#    for OO::order_type(A) in A.maximal_order
#      d = denominator(basis_matrix(O, copy = false)*basis_matrix_inverse(OO, copy = false))
#      if isone(d)
#        return OO
#      end
#    end
#  end
#
#  if degree(O) > 40 # group algebra is never simple
#    OO = _maximal_order_via_decomposition(O)
#  else
#    d = discriminant(O)
#    @assert degree(O) < 2^31 # squares do not overflow
#    fac = factor(degree(O)) # the order of the group
#
#    OO = O
#    for (p, j) in fac
#      if mod(d, p^2) != 0
#        continue
#      end
#      OO += pmaximal_overorder(O, p)
#    end
#
#    for (p, _) in factor(ppio(discriminant(OO), ZZ(degree(O)))[2])
#      OO += pmaximal_overorder(O, p)
#    end
#
#    OO.is_maximal = 1
#  end
#
#  if !isdefined(A, :maximal_order)
#    A.maximal_order = [OO]
#  else
#    push!(A.maximal_order::Vector{order_type(A)}, OO)
#  end
#
#  return OO
#end
#
#function _denominator_of_mult_table(A::AbstractAssociativeAlgebra{QQFieldElem})
#  return _denominator_of_mult_table(A, ZZ)
#end
#
#function _denominator_of_mult_table(A::AbstractAssociativeAlgebra, R::Ring)
#  l = one(R)
#  for i = 1:dim(A)
#    for j = 1:dim(A)
#      for k = 1:dim(A)
#        l = lcm(l, denominator(multiplication_table(A, copy = false)[i, j, k], R))
#      end
#    end
#  end
#  return l
#end
#
#_denominator_of_mult_table(A::GroupAlgebra{QQFieldElem}) = ZZRingElem(1)
#
#@doc raw"""
#    any_order(A::AbstractAssociativeAlgebra{QQFieldElem}) -> AlgAssAbsOrd
#
#Returns any order of $A$.
#"""
#function any_order(A::AbstractAssociativeAlgebra{QQFieldElem})
#  return any_order(A, ZZ)
#end
#
#function any_order(A::AbstractAssociativeAlgebra{QQFieldElem}, ::ZZRing)
#  return get_attribute!(A, :any_order) do
#    d = _denominator_of_mult_table(A)
#    di = dim(A)
#    M = vcat(zero_matrix(QQ, 1, di), d*identity_matrix(QQ, di))
#    oneA = one(A)
#    for i = 1:di
#      M[1, i] = deepcopy(coefficients(oneA, copy = false)[i])
#    end
#    M = _hnf!_integral(M, :lowerleft)
#    O = order(A, sub(M, 2:di + 1, 1:di))
#    return O
#  end::order_type(A)
#end
#
#function any_order(A::AbstractAssociativeAlgebra, R::Ring)#PolyRing{<:FieldElem})
#  # TODO: fix caching
#  #return get_attribute!(A, :any_order) do
#    K = base_ring(A)
#    d = _denominator_of_mult_table(A, R)
#    di = dim(A)
#    M = vcat(zero_matrix(K, 1, di), d*identity_matrix(K, di))
#    oneA = one(A)
#    for i = 1:di
#      M[1, i] = deepcopy(coefficients(oneA, copy = false)[i])
#    end
#    M = _hnf!_integral(M, R, :lowerleft)
#    O = order(A, R, sub(M, 2:di + 1, 1:di))
#    return O
#  #end::order_type(A, R)
#end
#
#_default_domain(::QQField) = ZZ
#
#@doc raw"""
#    maximal_order(A::AbstractAssociativeAlgebra{QQFieldElem}) -> AlgAssAbsOrd
#
#Returns a maximal order of $A$.
#"""
#function maximal_order(A::AbstractAssociativeAlgebra{S}, R = _default_domain(base_ring(A))) where S
#  # TODO: fix the caching
#  if isdefined(A, :maximal_order) && R === _default_domain(base_ring(A))
#    return first(A.maximal_order)::order_type(A)
#  end
#
#  O = any_order(A, R)
#  OO = maximal_order(O)
#  if !isdefined(A, :maximal_order) && R === _default_domain(base_ring(A))
#    A.maximal_order = [OO]
#  end
#  return OO
#end
#
