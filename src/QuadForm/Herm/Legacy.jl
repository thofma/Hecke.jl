################################################################################
#
#  Genus symbol
#
################################################################################

function _genus_symbol_kirschmer(L::HermLat, p; uniformizer = zero(order(p)))
  @assert order(p) == base_ring(base_ring(L))

  B, G, S = jordan_decomposition(L, p)
  R = base_ring(L)
  E = nf(R)
  K = base_field(E)
  if !is_dyadic(p) || !is_ramified(R, p)
    sym = Tuple{Int, Int, Bool}[ (nrows(B[i]), S[i], is_local_norm(E, coeff(det(G[i]), 0), p)) for i in 1:length(B)]
  else
    P = prime_decomposition(R, p)[1][1]
    pi = E(K(Hecke.uniformizer(p)))
    sym = Tuple{Int, Int, Bool, Int, elem_type(K)}[]
    for i in 1:length(B)
      normal = (_get_norm_valuation_from_gram_matrix(G[i], P)::Int == S[i])::Bool
      GG = diagonal_matrix(dense_matrix_type(E)[pi^(max(0, S[i] - S[j])) * G[j] for j in 1:length(B)])::dense_matrix_type(E)
      v = _get_norm_valuation_from_gram_matrix(GG, P)::Int
      s = (nrows(B[i]), S[i], normal, v, coeff(det(diagonal_matrix([G[j] for j in 1:i])), 0))
      push!(sym, s)
    end
  end
  return sym
end

################################################################################
#
#  Local isometry
#
################################################################################

function _islocally_isometric_kirschmer(L1::HermLat, L2::HermLat, p)
  R = base_ring(L1)
  E = nf(R)
  S1 = _genus_symbol_kirschmer(L1, p)
  S2 = _genus_symbol_kirschmer(L2, p)
  if !is_dyadic(p) || !is_ramified(R, p)
    return S1 == S2
  end

  t = length(S1)
  if t != length(S2)
    return false
  end
  for i in 1:t
    for k in 1:4
      if S1[i][k] != S2[i][k]
        return false
      end
    end
  end

  if !is_local_norm(E, S1[t][5]//S2[t][5], p)
    return false
  end

  for i in 1:(t-1)
    @assert valuation(S1[i][5], p) == valuation(S2[i][5], p)
    x = S1[i][5]//S2[i][5]
    n = normic_defect(E, x, p)
    n = n == inf ? inf : 2*n
    if n < (S1[i][4] + S1[i + 1][4]) - 2 * S1[i][2]
      return false
    end
  end
  return true
end

