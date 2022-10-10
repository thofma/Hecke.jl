################################################################################
#
#  Basic field access
#
################################################################################

@doc Markdown.doc"""
    nf(O::NumFieldOrd) -> NumField

Returns the ambient number field of $\mathcal O$.
"""
nf(O::NumFieldOrd)

@inline nf(O::NfAbsOrd{S, T}) where {S, T} = O.nf::S

@inline nf(O::NfRelOrd{S, T, U}) where {S, T, U} = O.nf::parent_type(U)

_algebra(O::NumFieldOrd) = nf(O)

@doc Markdown.doc"""
    number_field(O::NumFieldOrd)

Return the ambient number field of $\mathcal O$.
"""
@inline function NumberField(O::NumFieldOrd)
  return nf(O)
end

is_simple(O::NumFieldOrd) = is_simple(nf(O))

is_commutative(O::NumFieldOrd) = true

@doc Markdown.doc"""
    is_equation_order(O::NumFieldOrd) -> Bool

Returns whether $\mathcal O$ is the equation order of the ambient number
field $K$.
"""
@inline is_equation_order(O::NumFieldOrd) = O.is_equation_order

@inline is_maximal_known(O::NumFieldOrd) = O.is_maximal != 0

@inline is_maximal_known_and_maximal(O::NumFieldOrd) = isone(O.is_maximal)

@doc Markdown.doc"""
    is_maximal(R::NfAbsOrd) -> Bool

Tests if the order $R$ is maximal. This might trigger the
computation of the maximal order.
"""
function is_maximal(R::NumFieldOrd)
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

@doc Markdown.doc"""
    degree(O::NumFieldOrd) -> Int

Returns the degree of $\mathcal O$.
"""
degree(O::NumFieldOrd) = degree(O.nf)

function absolute_degree(O::NumFieldOrd)
  return absolute_degree(nf(O))
end

################################################################################
#
#  Signature
#
################################################################################

@doc Markdown.doc"""
    signature(O::NumFieldOrd) -> Tuple{Int, Int}

Returns the signature of the ambient number field of $\mathcal O$.
"""
function signature(x::NumFieldOrd)
  return signature(nf(x))
end

################################################################################
#
#  Discriminant
#
################################################################################

function discriminant(O::NumFieldOrd, K::NumField)
  K = nf(O)
  if K == base_field(K)
    return discriminant(O)
  else
    return norm(discriminant(O), K)*discriminant(base_ring(O), K)^degree(O)
  end
end

discriminant(O::NumFieldOrd, ::FlintRationalField) = absolute_discriminant(O)


################################################################################
#
#   Absolute basis
#
################################################################################

function absolute_basis(O::NfAbsOrd)
  return basis(O)
end

function absolute_basis(O::NfRelOrd)
  pb = pseudo_basis(O, copy = false)
  res = Vector{elem_type(O)}()
  for i = 1:degree(O)
    for b in absolute_basis(pb[i][2])
      push!(res, O(b*pb[i][1]))
    end
  end
  return res
end
