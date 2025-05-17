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

function _isunit(x::AbsSimpleNumFieldElem)
  return abs(norm(x)) == 1
end

function _isunit(x::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
  #this avoids a complicated, exepensive evaluation if the norm is not
  #one (or -1)
  #assumes that x actually represents an order element...
  n = simplify(factored_norm(x))
  if all(iszero, values(n.fac))
    return true
  end
  if all(x->isone(x) || x == -1, keys(n.fac))
    return true
  end
  return abs(norm(x)) == 1
end




