module module_RelNeq

using Hecke

struct RelNeq
  k::AnticNumberField
  K::AnticNumberField
  Kk::Hecke.NfRel{nf_elem}
  m_k_K::Map
  m_Kk_K::Map
  function RelNeq(k::AnticNumberField, Kk::Hecke.NfRel{nf_elem})
    @assert base_ring(Kk) == k
    K, m_Kk_K, m_k_K = absolute_field(Kk)
    return new(k, K, Kk, m_k_K, m_Kk_K)
  end
end

function norm_1_subgroup(A::RelNeq)
  k = A.k
  K = A.K
  Kk = A.Kk

  d = lcm([numerator(discriminant(k)), numerator(discriminant(K)), numerator(norm(discriminant(Kk)))])

  @show I = Hecke.lorenz_module(k, degree(Kk), containing = discriminant(maximal_order(Kk)))
  Hecke.assure_2_normal(I)

  I_K = ideal(maximal_order(K), I.gen_one, maximal_order(K)(A.m_k_K(I.gen_two.elem_in_nf)))
  r, mr = ray_class_group(I_K, real_places(K))

  q, mq = quo(r, elem_type(r)[])

  S = PrimesSet(degree(K), -1)
  gens = Set{NfOrdIdl}()
  gg = []

  max_stable = 2*ngens(r)
  stable = max_stable

  for p = S
    @show p
    if d % p == 0
      continue
    end
    if minimum(I) % p == 0
      continue
    end

    lp = prime_decomposition(maximal_order(k), p)
    for P = lp
      lP = Hecke.prime_decomposition_nonindex(A.m_k_K, P[1])
      f = [fmpz(div(degree(Q[1]), degree(P[1]))) for Q = lP]
      m = matrix(FlintZZ, 1, length(f), f)
      r, n = nullspace(m)

      decom = [mq(mr\Q[1]) for Q = lP]
      for i=1:r
        a = sum(n[j,i] * decom[j] for j = 1:length(decom))
        if iszero(a)
          stable -= 1
          continue
        end
        stable = max_stable

        q, nq = quo(q, [a])
        mq = mq*nq
        decom = [nq(x) for x = decom]
        push!(gens, P[1])
        push!(gg, FacElem(Dict((lP[j][1], n[j, i]) for j=1:length(decom) if n[j,i] != 0)))
      end
    end
    if stable <= 0
      break
    end
  end

  return mr, mq, gens, gg
end

end



