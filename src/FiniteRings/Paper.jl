function find_group_and_subgroup(grpid, quotid)
  G = small_group(grpid...)
  local S, StoG
  local H
  for g in G
    if order(g) != divexact(grpid[1], quotid[1])
      continue
    end
    S, StoG = sub(G, [g])
    if !is_normalized_by(S, G)
      continue
    end
    H = quo(G, S)
    if small_group_identification(H[1]) == quotid
      break
    end
  end
  @assert Oscar.small_group_identification(quo(G, S)[1]) == quotid
  return G, StoG
end

function gamma(grpid, quotid)
  G = small_group(grpid...)
  local S, StoG
  local H
  for g in G
    if order(g) != divexact(grpid[1], quotid[1])
      continue
    end
    S, StoG = sub(G, [g])
    if !is_normalized_by(S, G)
      continue
    end
    H = quo(G, S)
    if small_group_identification(H[1]) == quotid
      break
    end
  end
  QG = QQ[G]
  ZG = Order(QG, basis(QG), isbasis = true; check = false)
  @assert Oscar.small_group_identification(quo(G, S)[1]) == quotid
  trN = sum(QG(StoG(s)) for s in S)
  Gamma, =  Hecke.quotient_order(ZG, trN * ZG)
  QH = QQ[H[1]]
  ZH = Order(QH, basis(QH), isbasis = true; check = false)
  return ZG, ZH, Gamma
end

function example1()
  ZG, ZH, Gamma = gamma((288, 409), (144, 127)) # this is Ttilde x Q_{12}
  F = TestingSFC.fibre_product_from_eichler_splitting(Gamma)
  h2 = TestingSFC.h2(F)
  Rmodh2, = quo(F.R2, h2 * F.R2)
  RR, = FiniteRings.finite_ring(Rmodh2);
  return Rmodh2, RR
end

function example2()
  ZG, ZH, Gamma = gamma((480, 266), (240, 108)) # this is Ttilde x Q_{20}
  F = TestingSFC.fibre_product_from_eichler_splitting(Gamma)
  h2 = TestingSFC.h2(F)
  Rmodh2, = quo(F.R2, h2 * F.R2)
  RR, = FiniteRings.finite_ring(Rmodh2);
  return Rmodh2, RR
end

function example3() # Q8 ⋊ T ̃
  _, _, Gamma = gamma((192, 1022), (96, 204))
  F = TestingSFC.fibre_product_from_eichler_splitting(Gamma)
  h2 = TestingSFC.h2(F)
  Rmodh2, = quo(F.R2, h2 * F.R2)
  RR, = FiniteRings.finite_ring(Rmodh2);
  return Rmodh2, RR
end

function example4() # F_2[H], H = 96, 204
  QH = QQ[small_group(96, 204)]
  ZH = integral_group_ring(QH)
  Rmodh2, = quo(ZH, 2 * ZH)
  RR, = FiniteRings.finite_ring(Rmodh2);
  return Rmodh2, RR
end

function example5() # F_2[H], H = 96, 204
  QH = QQ[small_group(16, 5)]
  ZH = integral_group_ring(QH)
  Rmodh2, = quo(ZH, 2 * ZH)
  RR, = FiniteRings.finite_ring(Rmodh2);
  return Rmodh2, RR
end
