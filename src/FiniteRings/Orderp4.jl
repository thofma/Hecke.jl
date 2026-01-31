function _p2_char_noncomm(p)
  F = GF(p)
  A = zeros(F, 2, 2, 2)

end
function _p4_charp1_radicalp2(p)
  res = FiniteRing[]
  let
    F = GF(p^2)
    B = basis(F)
    A = matrix_algebra(F, 2)
    gens = Oscar.dense_matrix_type(F)[]
    for b in B
      x = matrix(F, 2, 2, [b, 0, 0, b^p])
      push!(gens, x)
      x = matrix(F, 2, 2, [0, b, 0, 0])
      push!(gens, x)
    end
    _, f = Oscar.restrict_scalars(A, GF(p))
    elts = preimage.(f, A.(gens))
    R = finite_ring(Oscar.Hecke._subalgebra(domain(f), preimage.(f, A.(gens)))[1])[1]
    push!(res, R)
  end
  let
    F = GF(p)
    A = matrix_algebra(F, 3)
    gens = Oscar.dense_matrix_type(F)[]
    mats = [
            [1, 0, 0,
             0, 1, 0,
             0, 0, 0],
            [0, 0, 0,
             1, 0, 0,
             0, 0, 0],
            [0, 0, 0,
             0, 0, 0,
             1, 0, 0],
            [0, 0, 0,
             0, 0, 0,
             0, 0, 1]
           ]
    gens = A.(matrix.(Ref(F), 3, 3, mats))
    R = finite_ring(Oscar.Hecke._subalgebra(A, gens)[1])[1]
    push!(res, R)
  end
  return res
end

function _collect_glns(n, p)
  res = []
  for p in p #Oscar.PrimesSet(2, n + 1)
    for e in 1:Oscar.clog(n + 1, p)
      q = p^e
      k = 1
      while true
        G = Oscar.GL(k, q)
        if order(G) > n
          break
        end
        push!(res, G)
        k += 1
      end
    end
  end
  D = Dict{Int, Any}(Int(order(G)) => G for G in res)
  k = sort!(collect(keys(D)))
  rr = []
  for i in 2:n
    pa = collect(Oscar.partitions(i, k))
    for pp in pa
      G = direct_product([D[i] for i in collect(pp)])
      push!(rr, G)
    end
  end
  push!(rr, GL(1, 2))
  return rr
end

function _collect_nilpotent_groups(n, p)
  res = []
  for e in 1:Oscar.clog(n, p)
    if p^e > n
      continue
    end
    for j in 1:Oscar.number_of_small_groups(p^e)
      G = Oscar.small_group(p^e, j)
      if Oscar.is_nilpotent(G)
        push!(res, G)
      end
    end
  end
  push!(res, Oscar.small_group(1, 1))
  return res
end  

function _collect_all(n, p)
  glns = _collect_glns(n, p)
  nil = _collect_nilpotent_groups(n, p)
  res = []
  for i in 2:n
    for j in 1:Oscar.number_of_small_groups(i)
      G = Oscar.small_group(i, j)
      for N in Oscar.normal_subgroups(G)
        if any(x -> Oscar.is_isomorphic(N, x), nil)
          Q, = quo(G, N)
          if any(x -> Oscar.is_isomorphic(Q, x), glns)
            push!(res, (G, (i, j), N, Q))
          end
        end
      end
    end
  end
  res
end




