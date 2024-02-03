################################################################################
#
#  Basic field access
#
################################################################################

@doc raw"""
    nf(O::NumFieldOrder) -> NumField

Returns the ambient number field of $\mathcal O$.
"""
nf(O::NumFieldOrder)

@inline nf(O::AbsNumFieldOrder{S, T}) where {S, T} = O.nf::S

@inline nf(O::RelNumFieldOrder{S, T, U}) where {S, T, U} = O.nf::parent_type(U)

_algebra(O::NumFieldOrder) = nf(O)

@doc raw"""
    number_field(O::NumFieldOrder)

Return the ambient number field of $\mathcal O$.
"""
@inline function number_field(O::NumFieldOrder)
  return nf(O)
end

is_simple(O::NumFieldOrder) = is_simple(nf(O))

is_commutative(O::NumFieldOrder) = true

@doc raw"""
    is_equation_order(O::NumFieldOrder) -> Bool

Returns whether $\mathcal O$ is the equation order of the ambient number
field $K$.
"""
@inline is_equation_order(O::NumFieldOrder) = O.is_equation_order

@inline is_maximal_known(O::NumFieldOrder) = O.is_maximal != 0

@inline is_maximal_known_and_maximal(O::NumFieldOrder) = isone(O.is_maximal)

@doc raw"""
    is_maximal(R::AbsNumFieldOrder) -> Bool

Tests if the order $R$ is maximal. This might trigger the
computation of the maximal order.
"""
function is_maximal(R::NumFieldOrder)
  if R.is_maximal == 1
    return true
  end
  if R.is_maximal == 2
    return false
  end
  S = maximal_order(R)
  if discriminant(S) == discriminant(R)
    R.is_maximal = 1
  else
    R.is_maximal = 2
  end
  return R.is_maximal == 1
end

################################################################################
#
#  Degree
#
################################################################################

@doc raw"""
    degree(O::NumFieldOrder) -> Int

Returns the degree of $\mathcal O$.
"""
degree(O::NumFieldOrder) = degree(O.nf)

function absolute_degree(O::NumFieldOrder)
  return absolute_degree(nf(O))
end

################################################################################
#
#  Signature
#
################################################################################

@doc raw"""
    signature(O::NumFieldOrder) -> Tuple{Int, Int}

Returns the signature of the ambient number field of $\mathcal O$.
"""
function signature(x::NumFieldOrder)
  return signature(nf(x))
end

################################################################################
#
#  Discriminant
#
################################################################################

function discriminant(O::NumFieldOrder, K::NumField)
  K = nf(O)
  if K == base_field(K)
    return discriminant(O)
  else
    return norm(discriminant(O), K)*discriminant(base_ring(O), K)^degree(O)
  end
end

discriminant(O::NumFieldOrder, ::QQField) = absolute_discriminant(O)


################################################################################
#
#   Absolute basis
#
################################################################################

function absolute_basis(O::AbsNumFieldOrder)
  return basis(O)
end

function absolute_basis(O::RelNumFieldOrder)
  pb = pseudo_basis(O, copy = false)
  res = Vector{elem_type(O)}()
  for i = 1:degree(O)
    for b in absolute_basis(pb[i][2])
      push!(res, O(b*pb[i][1]))
    end
  end
  return res
end
