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
  n, B = rref(B')
  B = sub(B, 1:n, 1:ncols(B))'
  fl, T = can_solve(A, B)  # A T = B
  d, r = rref(T')
  t = sub(r, 1:d, 1:ncols(r))
  t = Hecke.reduce_mod(identity_matrix(base_ring(t), ncols(t)), t)
  d = rref!(t)
  t = t[1:d, :]
  return A*t'
end

function rational_normal_form(M::T) where {T <: MatElem{S} where {S <: FieldElem}}
  f = minpoly(M)
  lf = factor(f)
  all_b = zero_matrix(base_ring(M), nrows(M), 0)
  for (g, v) = lf.fac
    m = (g^v)(M)
    this_g = zero_matrix(base_ring(M), nrows(M), 0)
    while true
      d, km = nullspace(m)
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
        @show ex -= 1
        km = g(M)*km
        d, km = rref(km')
        km = km[1:d, :]'
      end
      b = b[:, 1]
    #any 0 ne b in km/g(M)km will generate a sigma cyclic subspace
    # b, Mb M^2b ... g(M)b, M g(M) b, ... g^2(M)b, ....
      ve = deepcopy(b)
      b = zero_matrix(base_ring(M), nrows(M), 0)
      for k = 1:ex
        for j = 1:degree(g)
          @show k, j
          b = hcat(b, (M^(j-1))*((g^(k-1))(M))*ve)
        end
      end
      @show this_g = hcat(this_g, b)
    end
    all_b = hcat(all_b, this_g)
  end
  return all_b
end

end
