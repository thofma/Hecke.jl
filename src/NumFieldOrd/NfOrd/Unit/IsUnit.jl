################################################################################
#
#  Testing for invertibility
#
################################################################################

@doc Markdown.doc"""
    isunit(x::NfOrdElem) -> Bool

Returns whether $x$ is invertible or not.
"""
function isunit(x::NfOrdElem)
  return abs(norm(x)) == 1
end

_isunit(x::NfOrdElem) = isunit(x)

function _isunit(x::T) where T <: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}
  return abs(norm(x)) == 1
end



