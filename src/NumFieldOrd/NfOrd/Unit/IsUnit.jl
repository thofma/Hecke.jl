################################################################################
#
#  Testing for invertibility
#
################################################################################

@doc raw"""
    is_unit(x::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> Bool

Returns whether $x$ is invertible or not.
"""
function is_unit(x::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return abs(norm(x)) == 1
end

_isunit(x::AbsNumFieldOrderElem{AbsSimpleNumField, AbsSimpleNumFieldElem}) = is_unit(x)

function _isunit(x::T) where T <: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
  return abs(norm(x)) == 1
end



