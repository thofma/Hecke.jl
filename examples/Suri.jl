module Suri
using Hecke
import Hecke: valuation, divexact, parent_type, elem_type, mul!, addeq!, parent
import Base: +, -, *, ^

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

function mod_lll(a::NfAbsOrdElem, I::NfAbsOrdIdl)
  l = lll(I)[2]
  S = l*basis_matrix(I)
  Si = pseudo_inv(S)
  c = matrix(FlintZZ, 1, nrows(l), coordinates(a)) * Si[1]
  d = matrix(FlintZZ, 1, nrows(l), [round(fmpz, x, Si[2]) for x = c])
  return a - Hecke.parent(a)(collect(d*S))
end

function mod_lll(a::nf_elem, I::Hecke.NfAbsOrdFracIdl)
  O = order(I)
  d = lcm(denominator(a, O), denominator(I))
  return divexact(Hecke.parent(a)(mod_lll(O(d*a), simplify(I*d).num)), d)
end

function _reduce(a::Hecke.PMat, T)
  A = a.coeffs
  M = a.matrix
  for i=2:nrows(M)
    for j=1:i-1
      if iszero(M[j, i])
        continue
      end
      I = A[i]*M[i,i]*inv(A[j])
      c = mod_lll(M[j,i], I)
      @assert (c - M[j,i]) in I
      d = divexact(M[j, i] -c, M[i,i])
      M[j, :] = M[j, :] - d*M[i, :]
      T[j, :] = T[j, :] - d*T[i, :]
      @assert M[j, i] == c
    end
  end
end

function extend(M::Hecke.PMat, b::Generic.MatSpaceElem{nf_elem}, gamma::Generic.MatSpaceElem{nf_elem})

  @assert iszero(hcat(M.matrix', b)*gamma) 
  zk = base_ring(M)
  nc = ncols(gamma)
  n = nrows(gamma) - 1
  @assert nc == ncols(b)
  p = pseudo_matrix(hcat(gamma, vcat(identity_matrix(zk, n), zero_matrix(zk, 1, n))), vcat(map(inv, coefficient_ideals(M)), [1*zk for i=1:nc]))
#  @show p

  h, T = Hecke.pseudo_hnf_with_transform(p)
#  @show T*p.matrix == h.matrix
  _reduce(h, T)
#  @show T*p.matrix == h.matrix
  for i=1:nrows(h)
    j, al = Hecke.reduce_ideal(h.coeffs[i])
    T[i, :] *= inv(al)
    h.coeffs[i] = j
    h.matrix[i, :] *= inv(al)
  end
#  @show pseudo_hnf(h) == pseudo_hnf(p)
#  @show T*p.matrix == h.matrix
  #for n x 1 matrices, the transform, especially the inverse can more easily be computed
#  @assert prod(coefficient_ideals(p)) ==  (det(T))*(prod(coefficient_ideals(h)))
#  @assert all(T[j,i] in (coefficient_ideals(p)[i])*inv(coefficient_ideals(h)[j]) for i=1:nrows(M) for j=1:nrows(M))
  Ti = inv(T)
#  @assert all(Ti[i,j] in inv(coefficient_ideals(p)[i])*(coefficient_ideals(h)[j]) for i=1:nrows(M) for j=1:nrows(M))
#there is a transpose problem somewhere...
  e = pseudo_matrix((hcat(M.matrix', b)*Ti)[:, nc+1:nrows(M)+nc]', map(inv, coefficient_ideals(h)[nc+1:nrows(M)+nc]))
  return e
end

function Hecke.denominator(P::Hecke.PMat, M::NfOrd)
  l = fmpz(1)
  p = matrix(P)
  for i=1:nrows(P)
    I = coefficient_ideals(P)[i]
    if isa(I, Hecke.NfAbsOrdFracIdl)
      Hecke.assure_2_normal(I.num)
    else
      Hecke.assure_2_normal(I)
    end
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
    a, b = Hecke.reduce_ideal(c[i])
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
  B = map_entries(x->k(preimage(mq, x)), BX)
  my_mod_sym!(B, X)
  return B
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

#modelled after
#  http://www.ti3.tu-harburg.de/paper/rump/NiRuOi11.pdf
#  On the generation of very ill-conditioned integer matrices
#  Tetsuo Nishi1a, Siegfried M. Rump, and Shin’ichi Oishi
#  Nonlinear Theory and Its Applications, IEICE, vol. 2, no. 2, pp. 226N245
#should generate a matrix where the entries are roughly U^2 (U a range)
#determinant 1, and the inverse should have much larger coefficients.
function bad_mat(R::Hecke.Ring, n::Int, U)
  z = zero_matrix(R, n, n)
  for i=1:n-1
    z[i+1,i] = one(R)
    z[i+1, i+1] = rand(R, U)
  end
  d = one(R)
  for i=n:-1:1
    k = rand(R, U)
    z[1, i] = d+k*z[i,i]
    d = k
  end
  return z
end

function bad_mat_suri(R::Hecke.Ring, n::Int, U)
  m = identity_matrix(R, n)
  for i=1:n
    for j=i+1:n
      m[i,j] = rand(R, U)
    end
  end
  return m
end

mutable struct RRS <: Hecke.Ring
  p::Array{fmpz, 1}
  P::Array{fmpz, 1}
  Pi::Array{fmpz, 1}
  r::fmpz
  N::fmpz
  ce

  function RRS(p::Array{fmpz, 1})
    s = new()
    s.p = p
    P = prod(p)
    s.P = [divexact(P, x) for x = p]
    s.Pi = [invmod(s.P[i], s.p[i]) for i=1:length(p)]
    s.r = next_prime(2^50)
    s.N = P
    s.ce = Hecke.crt_env(p)
    return s
  end

  function RRS(p::Array{<:Integer, 1})
    return RRS(fmpz[x for x = p])
  end
end
function Base.show(io::IO, R::RRS)
  print(io::IO, "crt ring with moduli ", R.p)
end

mutable struct RRSelem <: Hecke.RingElem
  x::Array{fmpz, 1}
  r::fmpz
  R::RRS
  function RRSelem(X::RRS, a::fmpz)
    s = new()
    s.x = [mod(a, p) for p = X.p]
    s.r = mod(a, X.r)
    s.R = X
    return s
  end
  function RRSelem(X::RRS, a::Integer)
    return RRSelem(X, fmpz(a))
  end
  function RRSelem(X::RRS, a::Array{fmpz, 1}, k::fmpz)
    r = new()
    r.R = X
    r.x = a
    r.r = k
    return r
  end
end

function Base.show(io::IO, a::RRSelem)
  print(io, "crt: ", a.x)
end

elem_type(::RRS) = RRSelem
parent_type(::RRSelem) = RRS
parent_type(::Type{RRSelem}) = RRS

parent(a::RRSelem) = a.R

-(a::RRSelem, b::RRSelem) = RRSelem(a.R, [mod(a.x[i]-b.x[i], a.R.p[i]) for i=1:length(a.x)], mod(a.r-b.r, a.R.r))
+(a::RRSelem, b::RRSelem) = RRSelem(a.R, [mod(a.x[i]+b.x[i], a.R.p[i]) for i=1:length(a.x)], mod(a.r+b.r, a.R.r))
*(a::RRSelem, b::RRSelem) = RRSelem(a.R, [mod(a.x[i]*b.x[i], a.R.p[i]) for i=1:length(a.x)], mod(a.r*b.r, a.R.r))
*(a::Integer, b::RRSelem) = RRSelem(b.R, [mod(a*b.x[i], b.R.p[i]) for i=1:length(b.x)], mod(a*b.r, b.R.r))
divexact(a::RRSelem, b::RRSelem) = RRSelem(a.R, [mod(a.x[i]*invmod(b.x[i], a.R.p[i]), a.R.p[i]) for i=1:length(a.x)], mod(a.r*invmod(b.r, a.R.r), a.R.r))
-(a::RRSelem) = RRSelem(a.R, [mod(-a.x[i], a.R.p[i]) for i=1:length(a.x)], -a.r)
^(a::RRSelem, e::Integer) = RRSelem(a.R, [powermod(a.x[i], e, a.R.p[i]) for i=1:length(a.x)], powermod(a.r, e, a.R.r))
(R::RRS)() = RRSelem(R, fmpz[0 for i=1:length(R.p)], fmpz(0))
(R::RRS)(a::Integer) = RRSelem(R, a)
(R::RRS)(a::RRSelem) = a

function addeq!(a::RRSelem, b::RRSelem)
  for i=1:length(a.x)
    a.x[i] = mod(a.x[i] + b.x[i], a.R.p[i])
    a.r    = mod(a.r    + b.r   , a.R.r)
  end
  return a
end

function mul!(a::RRSelem, b::RRSelem, c::RRSelem)
  for i=1:length(a.x)
    a.x[i] = mod(b.x[i] * c.x[i], a.R.p[i])
    a.r    = mod(b.r    * c.r   , a.R.r)
  end
  return a
end

function check(a::RRSelem)
  z = fmpz(a)
  @assert mod(z, a.R.r) == a.r
end

#given x mod p_i and p_r, find x mod p
function extend(R::RRS, a::RRSelem, p::fmpz)
  k = sum(((a.x[i]*R.Pi[i]) % R.p[i]) * (R.P[i] % R.r) for i=1:length(R.p)) - a.r
  k = (k*invmod(R.N, R.r)) % R.r
  @assert k <= length(R.p)
  return (sum(((a.x[i]*R.Pi[i]) % R.p[i]) * (R.P[i] % p) for i=1:length(R.p)) - k*(R.N % p)%p)%p
end

function mixed_radix(R::RRS, a::RRSelem, li::Int = typemax(Int))
  A = fmpz[]
  for i=1:min(length(a.x), li)
    y = a.x[i]
    for j=1:i-1
      y = mod(((y-A[j])*invmod(R.p[j], R.p[i])), R.p[i])
    end
    push!(A, y)
  end
  return A
  #so a = A[1] + A[2]*p[1] + A[3]*p[1]*p[2] ...s
end

function rss_elem_from_radix(R::RRS, a::Array{fmpz, 1})
  x = fmpz[]
  for i=1:length(R.p)
    z = a[1]
  end
end

function gen(R::RRS, i::Int)
  p = fmpz[0 for i=1:length(R.p)]
  p[i] = fmpz(1)
  r = mod(R.P[i]*R.Pi[i], R.r)
  return RRSelem(R, p, r)
end

Hecke.fmpz(a::RRSelem) = Hecke.crt(a.x, a.R.ce)


# a random invertable matrix with coeffs in R
#start with identity, do i rounds of random elementary row and column 
#operations
function rand_gl(R::Hecke.Ring, n::Int, u, i::Int)
  A = identity_matrix(R, n)
  for j=1:i
    a = rand(R, u)
    mu = rand(1:n)
    nu = rand(1:n)
    if mu == nu
      continue
    end
    A[mu, :] += a*A[nu, :]
    a = rand(R, u)
    mu = rand(1:n)
    nu = rand(1:n)
    if mu == nu
      continue
    end
    A[:, mu] += a*A[:, nu]
  end
  return A
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

n = 6

k, a = wildanger_field(3, 13)
k, a = quadratic_field(-11)
m = rand(MatrixSpace(k, n, n), 1:10);
m = cat(m,m, dims=(1,2));
b = rand(MatrixSpace(k, 2*n, 1), 1:10);
S = kernel(hcat(m, b));

m1 = Suri.extend(pseudo_matrix(m'), b, S[2]);

norm(det(m))
norm(det(m1))

b = rand(MatrixSpace(k, 2*n, 1), 1:10);
S = kernel(hcat(m1.matrix', b));
m2 = Suri.extend(m1, b, S[2]);

norm(det(m2))

=#
