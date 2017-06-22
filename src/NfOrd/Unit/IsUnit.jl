################################################################################
#
#  Testing for invertibility
#
################################################################################

doc"""
***
    isunit(x::NfOrdElem) -> Bool

> Returns whether $x$ is invertible or not.
"""
function isunit(x::NfOrdElem)
  return abs(norm(x)) == 1 
end

_isunit(x::NfOrdElem) = isunit(x)

function _isunit{T <: Union{nf_elem, FacElem{nf_elem, AnticNumberField}}}(x::T)
  return abs(norm(x)) == 1
end



