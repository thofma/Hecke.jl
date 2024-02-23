function is_locally_isometric_kirschmer(L::QuadLat, M::QuadLat, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  R = base_ring(L)
  base_ring(L) != base_ring(M) && error("Lattices must have the same base ring")
  order(p) != R && error("Ideal must be in the base ring of the lattices")
  d = rank(L)
  if d != rank(M)
    return false
  elseif d == 0
    return true
  end

  if minimum(p) != 2
    SL = _genus_symbol_kirschmer(L, p)
    SM = _genus_symbol_kirschmer(M, p, uniformizer = uniformizer(SL))
    return (data(SL) == data(SM))::Bool
  end

  if !is_rationally_isometric(L, M, p)
    return false
  end

  dimL1, sL1, wL1, aL1, fL1, G1 = data(_genus_symbol_kirschmer(L, p))
  dimL2, sL2, wL2, aL2, fL2, G2 = data(_genus_symbol_kirschmer(M, p))

  if (dimL1 != dimL2) || (sL1 != sL2) || (wL1 != wL2)
    return false
  end

  uL1 = [valuation(aL1[k], p) for k in 1:length(aL1)]
  uL2 = [valuation(aL2[k], p) for k in 1:length(aL2)]
  if uL1 != uL2
    return false
  end

  bL = [aL1[k]//aL2[k] for k in 1:length(aL1)];
  qL = [quadratic_defect(bL[k], p) for k in 1:length(bL)]

  if reduce((x, y) -> (x || y), qL[k] < wL1[k] - uL2[k] for k in 1:length(qL))
    return false
  end

  e = ramification_index(p)
  # GL, GM: Gram matrix
  d1 = [ diagonal_matrix([G1[i] for i in 1:t]) for t in 1:length(G1)]
  d2 = [ diagonal_matrix([G2[i] for i in 1:t]) for t in 1:length(G2)]

  for i in 1:length(fL1)
    detquot = det(d1[i])//det(d2[i])
    if valuation(detquot, p) != 0
      return false
    end
    if quadratic_defect(detquot, p) < fL1[i]
      return false
    end
    if (fL1[i] > 2*e + uL1[i+1] - wL2[i+1]) && !(_comp_hasse(d1[i], diagonal_matrix(d2[i], matrix(base_ring(d2[i]), 1, 1, [aL2[i+1]])), p))
      return false
    end
    if (fL1[i] > 2*e + uL1[i  ] - wL2[i  ]) && !(_comp_hasse(d1[i], diagonal_matrix(d2[i], matrix(base_ring(d2[i]), 1, 1, [aL2[i]])), p))
      return false
    end
  end

  return true
end

# nrows(G2) = nrows(G1) + 1
function _comp_hasse(G1, G2, p)
  G1o = diagonal(_gram_schmidt(G1, identity)[1])
  G2o = diagonal(_gram_schmidt(G2, identity)[1])
  push!(G1o, prod(G1o) * prod(G2o))
  return _hasse_invariant(G1o, p) == _hasse_invariant(G2o, p)
end

