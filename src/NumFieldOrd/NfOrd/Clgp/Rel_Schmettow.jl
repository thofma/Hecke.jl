################################################################################
#
#  Algorithm of Schmettow
#
################################################################################

function one_step(b::AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; prec::Int = 100)
  b = p*b
  simplify(b)
  g1 = short_elem(b, prec = prec)
  b = g1*inv(b)
  simplify(b)
  g2 = short_elem(b, prec = prec)
  return simplify(g2*inv(b)), g1, g2
end

