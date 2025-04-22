module Jordan
using Hecke

function rref_with_trans(M::T) where {T <: MatElem{S} where {S <: FieldElem}}
  #does row ops
  n = hcat(M, identity_matrix(base_ring(M), nrows(M)))
  rref!(n)
  s = nrows(n)
  while s>0 && iszero(sub(n, s:s, 1:ncols(M)))
    s -= 1
  end
  return s, sub(n, 1:nrows(M), 1:ncols(M)), sub(n, 1:nrows(M), ncols(M)+1:ncols(n))
end

function quo_gens(A, B)
  n, B = rref(transpose(B))
  B = transpose(sub(B, 1:n, 1:ncols(B)))
  fl, T = can_solve_with_solution(A, B; side = :right)  # A T = B
  d, r = rref(transpose(T))
  t = sub(r, 1:d, 1:ncols(r))
  t = Hecke.reduce_mod(identity_matrix(base_ring(t), ncols(t)), t)
  d = rref!(t)
  t = t[1:d, :]
  return A*transpose(t)
end

function rational_normal_form(M::T) where {T <: MatElem{S} where {S <: FieldElem}}
  f = minpoly(M)
  lf = factor(f)
  all_b = zero_matrix(base_ring(M), nrows(M), 0)
  for (g, v) = lf.fac
    m = (g^v)(M)
    this_g = zero_matrix(base_ring(M), nrows(M), 0)
    while true
      km = kernel(m, side = :right)
      km = quo_gens(km, this_g)
      if ncols(km) == 0
        break
      end
      ex = v
      while true
        b = quo_gens(km, g(M)*km)
        if ncols(b) > 0
          break
        end
        ex -= 1
        km = g(M)*km
        d, km = rref(transpose(km))
        km = transpose(km[1:d, :])
      end
      b = b[:, 1]
    #any 0 ne b in km/g(M)km will generate a sigma cyclic subspace
    # b, Mb M^2b ... g(M)b, M g(M) b, ... g^2(M)b, ....
      ve = deepcopy(b)
      b = zero_matrix(base_ring(M), nrows(M), 0)
      for k = 1:ex
        for j = 1:degree(g)
          b = hcat(b, (M^(j-1))*((g^(k-1))(M))*ve)
        end
      end
      this_g = hcat(this_g, b)
    end
    all_b = hcat(all_b, this_g)
  end
  return all_b
end

end
