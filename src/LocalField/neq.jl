#export: degree_relative, random_elem, one_root, norm_equation

degree(L::Hecke.LocalField, K::Union{FlintQadicField, Hecke.LocalField}) = divexact(absolute_degree(L), absolute_degree(K))

function degree(L::FinField, k::FinField)
  @assert characteristic(L) == characteristic(k)
  dL = absolute_degree(L)
  dk = absolute_degree(k)
  q, r = divrem(dL, dk)
  r == 0 && return q
  error("not a subfield")
end

##############################################
#random element with small coefficients
# BAD
##############################################

function random_elem(L::Union{FlintQadicField, Hecke.LocalField})
   b = basis(L)
   n = degree(L)
   r = [rand(1:5*n) for i in 1:n]   # Choose small coefficients
   return sum( [r[i]*b[i] for i in 1:n])
end


########### any_root computes a single root in the finite field extensions####

import Nemo:any_root
function any_root(f::Union{gfp_poly, fq_nmod_poly}, F::Union{FqNmodFiniteField, Hecke.RelFinField})
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f) ] )
   return any_root(g)
end

function roots(f::Union{gfp_poly, fq_nmod_poly}, F::Union{FqNmodFiniteField, Hecke.RelFinField})
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f) ] )
   return roots(g)
end

function any_root(f::Hecke.AbstractAlgebra.Generic.Poly, F::Hecke.RelFinField)
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f)])
   fac = factor(g)
   if length(fac) == 1
      error("no roots")
   end
   r = first(fac)[1]
   @assert degree(r) == 1
   return -coeff(r,0)
end

function trace_equation(F::Union{FlintQadicField, Hecke.LocalField}, a::Union{Hecke.LocalFieldElem, padic, qadic})
  A = random_elem(F)
  K = parent(a)
  while iszero(trace(A, K)) || valuation(trace(A, K)) > 0
    A = random_elem(F)
  end
  A = divexact(A, F(trace(A, K)))
  return A*F(a) #F(a) here and above due to missing promote rule
end

function norm_equation(F::Union{FlintQadicField, Hecke.LocalField{padic, Hecke.UnramifiedLocalField}}, a::padic)
  v = valuation(a)
  if v % degree(F) != 0
    error("no solution, wrong valuation")
  end
  a = divexact(a, prime(parent(a), v))
  k, mk = ResidueField(parent(a))
  K, mK = ResidueField(F)
  b = norm_equation(K, mk(a))
  T = preimage(mK, b)
  a = a//norm(T)
  #log forgets the finite field bit...
  la = log(a)
  lA = trace_equation(F, la)
  @assert trace(lA) == la
  A = exp(lA)*prime(parent(a))^divexact(v, degree(F))
  return A*T
end

function Nemo.basis(k::Nemo.GaloisField)
  return [k(1)]
end

function Nemo.basis(k::Nemo.GaloisField, l::Nemo.GaloisField)
  @assert k == l
  return [k(1)]
end

function Nemo.basis(K::FqNmodFiniteField, k::Nemo.GaloisField)
  @assert characteristic(K) == characteristic(k)
  return basis(K)
end

function Nemo.basis(K::FinField, k::FinField)
  b = basis(K)
  K = base_ring(K)
  while absolute_degree(K) > absolute_degree(k)
    b = [x*y for x = basis(K) for y = b]
    K = base_ring(K)
  end
  if K != k
    error("subfield not in tower")
  end
  return b
end

#Pauli: Constructing ClassFields over LocalFields, JTNB,
#Thm 2.2
#Thm 2.3 and the recognition is missing.
#Plan for the NEQ: compute norms of gens
#   find combinations that solve up to low precision 
#   use exp/log for the hight bit...
#alternatively just use the lin. alg
# 1+p^k/1+p^l, * = p^k/p^l, + for k<l<=2k ...

h2_is_iso(::FlintQadicField) = true
h2_is_iso(::FlintPadicField) = true
function h2_is_iso(K::Hecke.LocalField)
  p = prime(K)
  e = absolute_ramification_index(K)
  k, mk = ResidueField(K)
  pi = uniformizer(K)
  pi = setprecision(pi, 2*e)
  eps = setprecision(K, precision(K)+e) do
    -inv(divexact(pi^e, p))
  end
  #assert valuation(eps) == 0
  kt, t = PolynomialRing(k, "t", cached = false)
  f = t^(p-1)-mk(eps)
  return length(roots(f)) == 0
end

function one_unit_group_gens(K::Union{FlintQadicField, Hecke.LocalField})
  p = prime(K)
  e = absolute_ramification_index(K)
  f = absolute_inertia_degree(K)
  if e %(p-1) == 0 && !h2_is_iso(K)
    return _unit_group_gens_case2(K)
  else
    return _unit_group_gens_case1(K)
  end
end

function root(a::FinFieldElem, n::fmpz)
  return root(a, Int(n))
end
function root(a::FinFieldElem, n::Integer)
  k = parent(a)
  kt, t = PolynomialRing(k, "t", cached = false)
  r = roots(t^n-a)
  return r[1]
end

function _unit_group_gens_case2(K::Union{FlintQadicField, Hecke.LocalField})
  p = prime(K)
  e = absolute_ramification_index(K)
  f = absolute_inertia_degree(K)

  k, mk = ResidueField(K)
  @assert absolute_degree(k) == f
  omega = basis(k, prime_field(k))
  @assert isone(omega[1]) #this has to change...
  mu_0 = valuation(e, p)+1
  e_0 = divexact(e, (p-1)*p^(mu_0-1))

  kt, t = PolynomialRing(k, "t", cached = false)
  pi = uniformizer(K)
  #we need p/pi^e, the unit, with enough precision,
  #precision(eps) = k -> p, pi needs 2k
  pi = setprecision(pi, precision(K)+2*e)
  eps = setprecision(K, precision(K)+e) do
    -inv(divexact(pi^e, p))
  end
  #  @assert precision(eps) >= precision(K) # does not (quite) work
  @assert valuation(eps) == 0
  rts = roots(t^(p-1) - mk(eps)) #same as in h2_is_iso, maybe restructure...
  @assert length(rts) == p-1
  #the roots should form an additive (cyclic) group, we need a generator.
  #well 0 is missing, but the original poly was t^p-eps*t
  #thus any non-zero root should do
  r = rts[1]
  r = root(r, p^mu_0)
  #now we need s.th. such that t^p-eps*t = x is irred:
  #degree is prime, char p and Artin-Schreier poly, thus
  #irred == no roots
  omega_s = rand(k)
  while length(roots(t^p-mk(eps)*t-omega_s)) > 0
    omega_s = rand(k)
  end
  omega[1] = r

  b = [preimage(mk, x) for x = omega]
  F_K = [ lambda for lambda = 1:ceil(Int, p*e//(p-1))-1 if lambda % p != 0]
  @assert length(F_K) == e

  one = K(1)
  gens = [ one+x*pi^l for x = b for l = F_K]
  push!(gens, one+preimage(mk, omega_s)*pi^(p^mu_0*e_0))
  return gens
end

function _unit_group_gens_case1(K::Union{FlintQadicField, Hecke.LocalField})
  p = prime(K)
  e = absolute_ramification_index(K)
  f = absolute_inertia_degree(K)

  k, mk = ResidueField(K)
  @assert absolute_degree(k) == f

  b = [preimage(mk, x) for x = basis(k, prime_field(k))]
  F_K = [ lambda for lambda = 1:ceil(Int, p*e//(p-1))-1 if lambda % p != 0]
  @assert length(F_K) == e

  pi = uniformizer(K)
  one = K(1)
  
  return [ one+x*pi^l for x = b for l = F_K]
end

function coefficients(a::Union{qadic, LocalFieldElem}, k)
  c = [coeff(a, i) for i=0:degree(parent(a))-1]
  while absolute_degree(parent(c[1])) > absolute_degree(k)
    c = vcat([[coeff(x, i) for i=0:(degree(parent(c[1]))-1)] for x = c]...)
  end
  if parent(c[1]) != k
    error("bad tower")
  end
  return c
end
coefficients(a::padic, ::FlintPadicField) = [a]
prime_field(k::FlintPadicField) = k
lift(a::Hecke.QadicRingElem{FlintPadicField, padic}) = lift(a.x)

function setprecision!(A::Generic.MatSpaceElem{Hecke.QadicRingElem{FlintPadicField, padic}}, n::Int)
  for i=1:nrows(A)
    for j=1:ncols(A)
      setprecision!(A[i,j], n)
    end
  end
end


function solve_1_units(a::Vector{T}, b::T) where T
  #assumes that T is a local field element - they don't have a 
  #common abstract type
  #
  #tries to write b as a power product of elements in a
  #Z_p (and Z) operates on the 1-units...
  k = precision(b)
  K = parent(b)
  old = precision(K)
  setprecision!(K, k)
  one = K(1)
  @assert all(x->parent(x) == K , a)
  #plan:
  # (1+p^k/1+p^l, *) = (p^k/p^l, +) for k<=l<=2k
  #so we start with k=1, l=2 to find the exponents mod p
  #remove this from b 
  #try to find the next part (mod p^2), ...
  #
  e = absolute_ramification_index(K)
  f = absolute_inertia_degree(K)
  pi = uniformizer(K)
  p = prime(K)
  l = 1
  cur_a = copy(a)
  cur_b = b
#  @assert degree(K) == e
  Qp = prime_field(K)
  Zp = ring_of_integers(Qp)
  expo_mult = [fmpz(1) for x = cur_a]
  expo = [fmpz(0) for x = cur_a]
  pk = fmpz(p)
  while l <= k
    ps = findall(x-> l <= e*valuation(x-one) < 2*l, cur_a)
    if length(ps) == 0
      @assert e*valuation(cur_b-1)>= 2*l
      if l == k
        break
      end
      l *= 2
      l = min(l, k)
      pk *= pk
      continue
    end
    @assert e*valuation(cur_b-1) >= l
    #now for a lin. sys: 
    # (b-1)/pi^l mod pi^l = sum x_i (a_i-1)/pi^p mod pi^l
    rhs = divexact(cur_b-one, pi^l)
    lhs = [divexact(cur_a[x]-one, pi^l) for x = ps]
    #a basis for <pi^k> should be pi^k, ..., pi^(k+e-1)
    #(over a lift of the residue field basis)
    #for the time being, I assume that the base_field is unramified
    R = matrix(Zp, 1, absolute_degree(K), coefficients(rhs, Qp))
    L = matrix(Zp, length(lhs), absolute_degree(K), vcat([coefficients(x, Qp) for x= lhs]...))

    setprecision!(R, k) #neccessary - don't understand why
    setprecision!(L, k)

    s = solve_left(L, R)

    for i=1:length(ps)
      li = lift(s[1, i])
      expo[ps[i]] += expo_mult[ps[i]]*li
      cur_a[ps[i]] = cur_a[ps[i]]^pk
      expo_mult[ps[i]] *= pk
    end
 
    cur_b = divexact(b, prod(a[i]^expo[i] for i=1:length(a)))
    if valuation(cur_b-one) >= k
      break
    end
#    @show expo
    if l == k
      break
    end
    l *= 2
    l = min(l, k)
    pk *= pk
  end
  setprecision!(K, old)
  return expo
end

function norm_equation(K:: Hecke.LocalField, b::Union{qadic,padic,Hecke.LocalFieldElem})
  if iszero(b)
    return zero(K)
  end
  if ramification_index(K, parent(b)) == 1
    return norm_equation_unramified(K, b)
  end
  #multi-step algo:
  # - reduce to norm equation in units, by removing valuation:
  e = absolute_ramification_index(K)
  v = e*valuation(b)
  @assert denominator(v) == 1
  v = numerator(v)
  pi = uniformizer(K)
  p = prime(K)
  so = pi^v
  setprecision!(so, precision(b)*ramification_index(K))
  b *= inv(norm(pi^v))
  #now b is a unit, next reduction:
  # - reduce to 1-units by solving in finite fields and lifting
  # Note: we don't need (or use) the Techmueller lift as it is not
  # available in general. We need any element X s.th. N(X) = b mod p
  # then b/N(X) is a 1-unit
  @assert valuation(b) == 0
  k, mk = ResidueField(K)
  c = preimage(mk, root(mk(K(b)), e))
  so *= c
  b *= inv(norm(c))
  @assert valuation(b-1) > 0
  #so b is a 1-unit!
  # - if v(b-1) > 1/(p-1), then exp/log work and we can reduce
  #   to trace equation..
  bb = setprecision(b, ceil(Int, e//(p-1)))
  g = setprecision(K, precision(bb)*ramification_index(K)) do
    one_unit_group_gens(K)
  end
  ng = map(norm, g)
  s = solve_1_units(ng, bb)
  c = setprecision(prod(g[i]^s[i] for i=1:length(s)), precision(b)*e)

  so *= c
  b  *= inv(norm(c)) 
  @assert valuation(b-1) > 1//(p-1)
  # Last step: norm/trace..
  bt = log(b)
  st = trace_equation(K, bt)
  so *= exp(st)
  return so
end

#=
function test_neq(L, n::Int = 5)
  for i=1:n
    a = norm(random_elem(L))
    global last_aa = a
    b = norm_equation(L, a)
    global last_bb = b
    @assert (norm(b) == a) || valuation(norm(b)- a) >= precision(a)-1
  end
end

=#
    



######################### norm equation over finite fields ##############
@doc Markdown.doc"""
    norm_equation(F::Union{FqNmodFiniteField, Hecke.RelFinField}, b::Union{gfp_elem, fq_nmod})

Find an element `x` in `F` such that the norm from `F` down to the parent of
`b` is exactly `b`.
"""
function norm_equation(F::Union{FqNmodFiniteField, Hecke.RelFinField}, b::Union{gfp_elem, fq_nmod})
   if iszero(b)
      return zero(F)
   end
   k = parent(b)
   n = degree(F,k)
   f = polynomial(k,vcat([b],[rand(k) for i = 1:n-1],[1]))
   while !is_irreducible(f)
      f = polynomial(k,vcat([b],[rand(k) for i = 1:n-1],[1]))
   end
   return (-1)^(n)*any_root(f,F)
end

function basis(K::RelFinField)
  b = [gen(K)^0]
  while length(b) < degree(K)
    push!(b, b[end]*gen(K))
  end
  return b
end

function base_field(K::FqNmodFiniteField)
  return GF(Int(characteristic(K)))
end

absolute_frobenius_matrix(K::FqNmodFiniteField, d::Int = 1) = frobenius_matrix(K, d)
absolute_frobenius_matrix(K::Nemo.GaloisField, d::Int = 1) = matrix(K, 1, 1, [1])

function absolute_frobenius_matrix(K::RelFinField, d::Int=1)
  b = absolute_basis(K)
  q = characteristic(K)^d
  b = [x^q for x = b]
  return matrix([absolute_coordinates(x) for x = b])
end

absolute_representation_matrix(a::FqNmodFiniteField) = representation_matrix(a)
absolute_representation_matrix(a::gfp_elem) = matrix(parent(a), 1, 1, [a])

function absolute_representation_matrix(a::RelFinFieldElem)
  b = a .* absolute_basis(parent(a))
  return matrix([absolute_coordinates(x) for x = b])
end

function frobenius_matrix(K::RelFinField, d::Int = 1)
  k = base_field(K)
  q = order(k)^d
  b = [x^q for x = basis(K)]
  m = matrix(k, degree(K), degree(K), [coeff(x, i) for x = b for i=0:degree(K)-1])
  return m
end

function representation_matrix(a::RelFinFieldElem)
  K = parent(a)
  k = base_field(K)
  b = a .* basis(K)
  m = matrix(k, degree(K), degree(K), [coeff(x, i) for x = b for i=0:degree(K)-1])
end

@doc Markdown.doc"""
    frobenius_equation(d::Int, c::Union{gfp_elem, fq_nmod})

    Find an element `x` in `parent(c)` such that `frobenius(x, d) = x*c`.
    If the norm of `c` is one, this is supposed to work.
"""
function frobenius_equation(d::Int, c::FinFieldElem)
   F = parent(c)
   if iszero(c)
      return zero(F)
   end
   p = characteristic(F)
   #F is a GF(p) vector space and x->x^(p^d)-cx is a linear map
   M = absolute_frobenius_matrix(F, d) - absolute_representation_matrix(c)
   r, k = kernel(M, side = :left)
   @assert r > 0
   return dot(absolute_basis(F), k[1, :])
end

@doc Markdown.doc"""
    artin_schreier_equation(d::Int, c::Union{gfp_elem, fq_nmod})

    Find an element `x` in `parent(c)` such that `frobenius(x, d) -x = c`.
"""
function artin_schreier_equation(d::Int, c::FinFieldElem)
   F = parent(c)
   p = characteristic(F)
   #F is a GF(p) vector space and x->x^(p^d)-x is a linear map
   M = absolute_frobenius_matrix(F, d)
   M = M-identity_matrix(base_ring(M), nrows(M))
   b = matrix(base_ring(M), 1, ncols(M), absolute_coordinates(c))
   s = solve_left(M, b)
   return dot(absolute_basis(F), s)
end

function frobenius(E::Hecke.LocalField, F::Union{Hecke.LocalField, FlintPadicField, FlintQadicField})
  a = automorphism_list(E, F)
  K, mK = ResidueField(E)
  k, mk = ResidueField(F)
  b = gen(E)
  bb = [mK(x(b)) for x = a]
  f = findall(isequal(mK(b)), bb)
  @assert length(f) == 1
  f = findall(isequal(bb[f[1]]^order(k)), bb)
  @assert length(f) == 1
  return a[f[1]]
end

"""
solve, hopefully,
    x^phi//x = c
    for phi the frobenius of parent(c) over F
"""
function frobenius_equation(c::Hecke.LocalFieldElem, F::Union{FlintPadicField, FlintQadicField, Hecke.LocalField})
  E = parent(c)
  pr = precision(c)
  K, mK = ResidueField(parent(c))
  d = absolute_inertia_degree(base_field(E))
  a0 = preimage(mK, frobenius_equation(d, mK(c)))

  fr = frobenius(E, base_field(E))
  #so we have (should have) valuation(fr(a0)//a0 -c) > 0
  #since a0 better be a unit, this becomes valuation(fr(a0) - c*a0) > 0
  if fr(a0) == c*a0
    return a0
  end
  @assert valuation(fr(a0) - c*a0)>0
  s = a0
  p = uniformizer(F)
  eF = absolute_ramification_index(F)
  eE = absolute_ramification_index(E)
  @assert valuation(p)*eF == 1
  bla = 1
  while true
    cc = c*s//fr(s)
    if isone(cc)
      return s
    end
    v = valuation(cc-1)
    @assert v > 0
    x = mK(divexact(cc-1, p^Int(v*eF)))
    a = preimage(mK, artin_schreier_equation(d, x))
    t = (1+p^Int(v*eF)*a)
    s *= t
    t = c*s//fr(s)
    if isone(t)
      return s
    end
    vv = valuation(t - 1)
    if vv*eE >= pr
      return s
    end
    @assert vv > v "does not converge"

    bla += 1
    if bla*eE > precision(c)
      error("does not converge")
    end
  end
end

function local_fundamental_class_serre(L::Hecke.LocalField, K::Union{Hecke.LocalField, FlintPadicField, FlintQadicField})

  e = divexact(absolute_ramification_index(L), absolute_ramification_index(K))
  d = divexact(absolute_inertia_degree(L), absolute_inertia_degree(K))
  E = unramified_extension(L, e)[1]
  G = automorphism_list(L, K)
  @assert Base.length(G) == absolute_degree(L)/absolute_degree(K)

  u = L(uniformizer(K))//uniformizer(L)^e
  @assert valuation(u) == 0
  v = norm_equation(E, u)
  @assert valuation(v) == 0
  @assert norm(v) == u
  pi = v*uniformizer(L)
  GG = automorphism_list(E, K)


  rE, mE = ResidueField(E)
  rL, mL = ResidueField(L)
  rK, mK = ResidueField(K)
  q = order(rK)

  power_frob_L = [gen(rL)]
  while length(power_frob_L) < absolute_degree(rL)/absolute_degree(rK)
    push!(power_frob_L, power_frob_L[end]^q)
  end

  power_frob_E = [gen(rE)]
  while length(power_frob_E) < absolute_degree(rE)/absolute_degree(rK)
    push!(power_frob_E, power_frob_E[end]^q)
  end

  fr = frobenius(E, L)
  @show z = findall(isequal(mE(fr(preimage(mE, gen(rE))))), power_frob_E)
  @assert length(z) == 1
  @assert z[1] == d+1

  beta = []
  sigma_hat = []
  imGG = map(x->x(E(gen(L))), GG)

  function G_mul(i::Int, j::Int)
    f = findall(isequal(G[i]*G[j]), G)
    @assert length(f) == 1
    return f[1]
  end

#=
  imG = map(x->x(gen(E)), GG)

  @show id = findfirst(x->imG[x] == gen(E) && imGG[x] == E(gen(L)), 1:length(GG))
  function GG_mul(i::Int, j::Int)
    f = findall(isequal(GG[i]*GG[j]), GG)
    @assert length(f) == 1
    return f[1]
  end

  @show inv_ = [ findall(x->GG_mul(x, i) == id, 1:length(GG)) for i=1:length(GG)]
  @assert all(x->length(x) == 1, inv_)
  inv_ = [x[1] for x = inv_]
=#

  for sigma = G
    #sigma induces on the residue field a power of frobenius - we want the
    #power...
    fa = findall(isequal(E(sigma(gen(L)))), imGG)
    #fa are all extensions of sigma to L...
    #but now we want a specific one:
    #sigma, restricted to the residue field is some power of frobenius
    #we want sigma^-1 restricted to be frob^j for small j
    power_L = 1
    if !isa(rL, Nemo.GaloisField)
      power_L = findfirst(isequal(mL(sigma(preimage(mL, gen(rL))))), power_frob_L)
      @assert length(findall(isequal(mL(sigma(preimage(mL, gen(rL))))), power_frob_L)) == 1
    end
#    @show power_L
     power_E = [findfirst(isequal(mE(GG[i](preimage(mE, gen(rE))))), power_frob_E) for i = fa]

#    @show fb = findall(isequal(power_L), power_E)
#    @assert length(fb) == 1
#    @assert fb[1] == argmin(power_E)


    i = power_L = power_L == 1 ? d : power_L-1
    #now i in Debeerst (2.2) is power_L
    fb_inv = [x == 1 ? x : (length(G) - (x-1) + 1) for x = power_E]
    fb = [argmin(fb_inv)] #the uniqe elem <= d

    c = GG[fa[fb[1]]](pi)//pi
    us = frobenius_equation(c, K)
    #think...
    @assert fr(us) == c*us || valuation(fr(us) - c*us) > 20
    uv = us*GG[fa[fb[1]]](pi)
    push!(beta, vcat([us for i=1:power_L], [uv for i=1:d-power_L]))
    push!(sigma_hat, (GG[fa[fb[1]]], d-power_L))
  end

  function action(i::Int, t::Vector)
    if sigma_hat[i][2] == d
      return map(sigma_hat[i][1], t)
    else
      s = map(sigma_hat[i][1], t)
      s = vcat(s[sigma_hat[i][2]+1:end], map(fr, s[1:sigma_hat[i][2]]))
      t = map(sigma_hat[i][1], vcat(t[sigma_hat[i][2]+1:end], map(fr, t[1:sigma_hat[i][2]])))
      @assert s == t
      return s
    end
  end

  function mul(t::Vector, s::Vector)
    return (t .* s)
  end

  #=

cmp(a, b) = (a == b || valuation(a-b) > 5)

Zx, x = ZZ["x"]
k = splitting_field(x^3-2)

l2 = prime_decomposition(maximal_order(k), 2)
k2 = Hecke.generic_completion(k, l2[1][1])  #S(3)(6)
zz = Hecke.local_fundamental_class_serre(k2[1], prime_field(k2[1]));
b, ac, gm, m, sh = zz;
for i=1:6 for j=1:6 a= m(b[j], ac(j, b[i])) .* map(inv, b[gm(i,j)]); push!(M, all([cmp(a[i], a[j]) for i=1:2 for j=i+1:2])); end; end

l3 = prime_decomposition(maximal_order(k), 3)
k3 = Hecke.generic_completion(k, l3[1][1])
zz = Hecke.local_fundamental_class_serre(k3[1], prime_field(k3[1]));
#fails in automorphisms
  =#


  return beta, action, G_mul, mul, sigma_hat
end
#############################################################################
#   The following "norm_equation_unramified" solves the norm equations only 
#   in unramified extensions
# Ali PhD, Algorithm 4
#############################################################################

function norm_equation_unramified(L::Hecke.LocalField, b::Hecke.LocalFieldElem)
   K = parent(b)
   @assert degree(L) == inertia_degree(L)
   prec_b = precision(b)
   piK = uniformizer(K)
   piL = uniformizer(L)
   f,mf = ResidueField(K)
   F,mF = ResidueField(L)
   ee = absolute_ramification_index(K)
   if mf(b) == f(1)
      f_nm = L(1)
   else
      f_nm = norm_equation(F,mf(b))
      f_nm = mF\(f_nm)
   end
   b = b//norm(f_nm)
   b = setprecision(b,prec_b)
   c = L(1)
   C = [L(1)]
   n = ee*valuation((b//norm(C[1]))-1)
   r = random_elem(L)
   while iszero(r) || valuation(trace(r)) != 0 || valuation(r//L(trace(r))) != 0
      r = random_elem(L)
   end
   z = ((b//norm(c))-1)//piK^ZZ(n)
   setprecision!(z, prec_b)
   push!(C, 1+ piL^ZZ(n)* (L(z)*r//L(trace(r))))
   c = prod(C)
   nc = norm(c)
   n = ee*valuation((b//nc)-1)
   while prec_b >= n+1 #  "solve till precision n-1"
      z = ((b//nc)-1)*piK^-ZZ(n)
      setprecision!(z, prec_b)
      push!(C, 1+ piL^ZZ(n)*(L(z)*r//L(trace(r))))
      c = prod(C)
      setprecision!(c, precision(L))
      nc = norm(c)
      chk = (nc*b^-1)-1
      if iszero(chk) == true
         n = prec_b
      else
         n = ee*valuation((b//nc)-1)
      end
   end
   return c*f_nm
end
