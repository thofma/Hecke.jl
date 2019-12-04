module Suri
using Hecke

#= follows Sebastian Posur's idea
  Start with a pseudo_matrix with ideals A_i and rows alpha_i
  plus an additional pseudo-element      A            alpha
  assume, at least for now, the alpha_i are independent.
  assume sum gamma_i alpha_i + gamma alpha = 0
  (gamma are the dependency)
  Now P := 
  (inv(A_i) gamma_i)
  ( inv(A)  gamma  )
  is a (n+1) x 1 pseudo matrix. Using the (pseudo) HNF we find a matrix
  T in Gl(n+1, K) and ideals C_i s.th.
  T*P = H is a pseudo-HNF. By construction, H has 1. row 1, all other rows 0
  and the coeff. ideals C_i
  Then T is an isomorphism between
  sum inv(A_i) + inv(A) and sum C_i
  as zk-modules
  The inverse-transpose of T is an isomorphism between
  sum inv(C_i) and sum A_i + A
  the dual modules to the ones above

  The idea:
  T is an iso between all modules given by the ideals
  The construction forces inv(T) to have the relation as 1. row/col
  The dual of an abstract module is giving by the inverse ideals
  The corresponding map is transpose(inv(T)) = inv(T)'
  Thus it works...
=#

function extend(M::Hecke.PMat, b::Generic.MatSpaceElem{nf_elem}, gamma::Generic.MatSpaceElem{nf_elem})

  zk = base_ring(M)
  p = pseudo_matrix(gamma, vcat(map(inv, coefficient_ideals(M)), [1*zk]))
  h, T = Hecke.pseudo_hnf_with_transform(p)
  #for n x 1 matrices, the trasform, especially the inverse can more easily be computed
#  @assert prod(coefficient_ideals(p)) ==  (det(T))*(prod(coefficient_ideals(h)))
#  @assert all(T[j,i] in (coefficient_ideals(p)[i])*inv(coefficient_ideals(h)[j]) for i=1:nrows(M) for j=1:nrows(M))
  Ti = inv(T)
#  @assert all(Ti[i,j] in inv(coefficient_ideals(p)[i])*(coefficient_ideals(h)[j]) for i=1:nrows(M) for j=1:nrows(M))
  e = pseudo_matrix((Ti'*hcat(M.matrix', b)')[2:nrows(M)+1, :], map(inv, coefficient_ideals(h)[2:nrows(M)+1]))
  return e
end

function Hecke.denominator(P::Hecke.PMat, M::NfOrd)
  l = fmpz(1)
  p = matrix(P)
  for i=1:nrows(P)
    I = coefficient_ideals(P)[i]
    for j=1:ncols(P)
      l = lcm(l, denominator(simplify(p[i,j]*I)))
    end
  end
  return l
end

function Hecke.simplify(P::Hecke.PMat)
  c = copy(coefficient_ideals(P))
  m = deepcopy(matrix(P))
  for i=1:length(c)
    a, b = Hecke.reduce_ideal2(c[i])
    m[i, :] *= inv(b)
    c[i] = fractional_ideal(order(a), a)
  end
  return pseudo_matrix(m, c)
end

end

#= example

k, a = wildanger_field(3, 13)
m = rand(MatrixSpace(k, 10, 10), 1:10);
m = cat(m,m, dims=(1,2));
b = rand(MatrixSpace(k, 20, 1), 1:10);
S = kernel(hcat(m, b));

m1 = Suri.extend(pseudo_matrix(m'), b, S[2]);

norm(det(m))
norm(det(m1))

b = rand(MatrixSpace(k, 20, 1), 1:10);
S = kernel(hcat(m1.matrix', b));
m2 = Suri.extend(m1, b, S[2]);

norm(det(m2))

=#
