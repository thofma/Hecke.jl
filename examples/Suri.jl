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
  nc = ncols(gamma)
  @assert nc == ncols(b)
  p = pseudo_matrix(gamma, vcat(map(inv, coefficient_ideals(M)), [1*zk for i=1:nc]))
  h, T = Hecke.pseudo_hnf_with_transform(p)
  #for n x 1 matrices, the trasform, especially the inverse can more easily be computed
#  @assert prod(coefficient_ideals(p)) ==  (det(T))*(prod(coefficient_ideals(h)))
#  @assert all(T[j,i] in (coefficient_ideals(p)[i])*inv(coefficient_ideals(h)[j]) for i=1:nrows(M) for j=1:nrows(M))
  Ti = inv(T)
#  @assert all(Ti[i,j] in inv(coefficient_ideals(p)[i])*(coefficient_ideals(h)[j]) for i=1:nrows(M) for j=1:nrows(M))
  e = pseudo_matrix((Ti'*hcat(M.matrix', b)')[nc+1:nrows(M)+nc, :], map(inv, coefficient_ideals(h)[nc+1:nrows(M)+nc]))
  return e
end

function Hecke.denominator(P::Hecke.PMat, M::NfOrd)
  l = fmpz(1)
  p = matrix(P)
  for i=1:nrows(P)
    I = coefficient_ideals(P)[i]
    Hecke.assure_2_normal(I.num)
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

function Hecke.dual(P::Hecke.PMat)
  return pseudo_matrix(inv(P.matrix)', map(inv, coefficient_ideals(P)))
end

function Hecke.invmod(A::Generic.MatSpaceElem{nf_elem}, X::fmpz)
  k = base_ring(A)
  zk = maximal_order(k)
  q, mq = quo(zk, X*zk)
  if true
    iA = inv(A)
    id = lcm([denominator(x, zk) for x = iA])
    BX = map_entries(x->mq(zk(id*x)), iA)*invmod(id, X)
  else
    d = lcm([denominator(x, zk) for x= A])
    AX = map_entries(x->mq(zk(d*x)), A)
    BX = inv(AX)*invmod(d, X)
  end
  return map_entries(x->k(preimage(mq, x)), BX)
end

function Hecke.invmod(A::fmpz_mat, X::fmpz)
  B0 = map_entries(lift, inv(map_entries(quo(ZZ, X)[1], A)))
  mod_sym!(B0, X)
  return B0
end

function my_mod_sym!(A::fmpz_mat, X::fmpz, ::Any)
  mod_sym!(A, X)
end

function valuation(a::NfAbsOrdElem{AnticNumberField,nf_elem}, X::fmpz)
  v = 0
  first = true
  for x = coordinates(a)
    iszero(x) && continue
    if first
      v = valuation(x, X)
      first = false
    else
      v = min(v, valuation(x, X))
    end
    iszero(v) && return v
  end
  return v
end

function mod_sym(A::NfAbsOrdElem{AnticNumberField,nf_elem}, X::fmpz)
  c = coordinates(A)
  d = map(x->Hecke.mod_sym(x, X), c)
  return parent(A)(d)
end

function my_mod_sym!(A::Generic.MatSpaceElem{nf_elem}, X::fmpz)
  k = base_ring(A)
  zk = maximal_order(k)
  for i=1:nrows(A)
    for j=1:ncols(A)
      A[i,j] = k(mod_sym(zk(A[i,j]), X))
    end
  end
end


function DoublePlusOne(A, X::fmpz, k::Int)
  R = base_ring(A)

  B0 = invmod(A, X)
  R = [divexact(identity_matrix(R, nrows(A))-A*B0, X)]
  M = []

  for i=0:k
    r = R[end]^2
    m = B0*r
    my_mod_sym!(m, X)
    push!(M, m)
    push!(R, divexact(r-A*M[end], X))
    if iszero(R[end])
      break
    end
  end
  return B0, M, R
end

function getB(B0, M, R, X)
  B = [B0]
  I = identity_matrix(base_ring(B0), nrows(B0))
  XX = X
  for i=1:length(M)
    push!(B, B[end]*(I + R[i]*XX) + M[i]*XX^2)
    XX = XX^2*X
    my_mod_sym!(B[end], XX)
  end
  return B
end

end

#= example

Hecke.example("Suri.jl")
Hecke.revise("Suri.jl")

k, a = wildanger_field(3, 13)
m = rand(MatrixSpace(k, 02, 02), 1:10);
m = cat(m,m, dims=(1,2));
b = rand(MatrixSpace(k, 04, 1), 1:10);
S = kernel(hcat(m, b));

m1 = Suri.extend(pseudo_matrix(m'), b, S[2]);

norm(det(m))
norm(det(m1))

b = rand(MatrixSpace(k, 04, 1), 1:10);
S = kernel(hcat(m1.matrix', b));
m2 = Suri.extend(m1, b, S[2]);

norm(det(m2))

=#
