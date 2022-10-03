################################################################################
#
#  Testing for invertibility
#
################################################################################

@doc Markdown.doc"""
    is_unit(x::NfOrdElem) -> Bool

Returns whether $x$ is invertible or not.
"""
function is_unit(x::NfOrdElem)
  return abs(norm(x)) == 1
end

_isunit(x::NfOrdElem) = is_unit(x)

function _isunit(x::T) where T <: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}
  return abs(norm(x)) == 1
end



