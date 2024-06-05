################################################################################
#
#  Testing for invertibility
#
################################################################################

@doc raw"""
    is_unit(x::AbsSimpleNumFieldOrderElem) -> Bool

Returns whether $x$ is invertible or not.
"""
function is_unit(x::AbsSimpleNumFieldOrderElem)
  return abs(norm(x)) == 1
end

_isunit(x::AbsSimpleNumFieldOrderElem) = is_unit(x)

function _isunit(x::T) where T <: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
  return abs(norm(x)) == 1
end



