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
   while valuation(trace(r)) != 0 || valuation(r//L(trace(r))) != 0
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
