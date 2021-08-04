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
  return O.nf
end

issimple(O::NumFieldOrd) = issimple(nf(O))

iscommutative(O::NumFieldOrd) = true

@doc Markdown.doc"""
    isequation_order(O::NumFieldOrd) -> Bool

Returns whether $\mathcal O$ is the equation order of the ambient number
field $K$.
"""
@inline isequation_order(O::NumFieldOrd) = O.isequation_order

@inline ismaximal_known(O::NumFieldOrd) = O.ismaximal != 0

@inline ismaximal_known_and_maximal(O::NumFieldOrd) = isone(O.ismaximal)

@doc Markdown.doc"""
    ismaximal(R::NfAbsOrd) -> Bool

Tests if the order $R$ is maximal. This might trigger the
computation of the maximal order.
"""
function ismaximal(R::NumFieldOrd)
  if R.ismaximal == 1
    return true
  end
  if R.ismaximal == 2
    return false
  end
  S = maximal_order(R)
  if discriminant(S) == discriminant(R)
    R.ismaximal = 1
  else
    R.ismaximal = 2
  end
  return R.ismaximal == 1
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