degree(L::Hecke.LocalField, K::Union{QadicField, Hecke.LocalField}) = divexact(absolute_degree(L), absolute_degree(K))

function degree(L::FinField, k::FinField)
  @assert characteristic(L) == characteristic(k)
  dL = absolute_degree(L)
  dk = absolute_degree(k)
  q, r = divrem(dL, dk)
  r == 0 && return q
  error("not a subfield")
end

##############################################
#random element with small coordinates
# BAD
##############################################

function random_elem(L::Union{QadicField, Hecke.LocalField})
   b = basis(L)
   n = degree(L)
   r = [rand(1:5*n) for i in 1:n]   # Choose small coordinates
   return sum( [r[i]*b[i] for i in 1:n])
end


########### any_root computes a single root in the finite field extensions####

import Nemo: any_root
function any_root(F::Union{fqPolyRepField, Hecke.RelFinField, FqField}, f::PolyRingElem)
   g = change_base_ring(F, f; cached = false)
   return any_root(g)
end

function roots(F::Union{fqPolyRepField, Hecke.RelFinField}, f::Union{fpPolyRingElem, fqPolyRepPolyRingElem})
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f) ] )
   return roots(g)
end

function any_root(F::Hecke.RelFinField, f::Hecke.AbstractAlgebra.Generic.Poly)
   g = polynomial(F, [coeff(f,i) for i = 0:degree(f)])
   fac = factor(g)
   if length(fac) == 1
      error("no roots")
   end
   r = first(fac)[1]
   @assert degree(r) == 1
   return -coeff(r,0)
end

function trace_equation(F::Union{QadicField, Hecke.LocalField}, a::Union{Hecke.LocalFieldElem, PadicFieldElem, QadicFieldElem})
  A = random_elem(F)
  K = parent(a)
  while iszero(trace(A, K)) || valuation(trace(A, K)) > 0
    A = random_elem(F)
  end
  A = divexact(A, F(trace(A, K)))
  return A*F(a) #F(a) here and above due to missing promote rule
end

function is_norm(F::Union{QadicField, Hecke.LocalField{PadicFieldElem, Hecke.UnramifiedLocalField}}, a::PadicFieldElem)
  return valuation(a) % degree(F) == 0
end

function norm_equation(F::Union{QadicField, Hecke.LocalField{PadicFieldElem, Hecke.UnramifiedLocalField}}, a::PadicFieldElem)
  v = valuation(a)
  if v % degree(F) != 0
    error("no solution, wrong valuation")
  end
  a = divexact(a, prime(parent(a), v))
  k, mk = residue_field(parent(a))
  K, mK = residue_field(F)
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

function Nemo.basis(K::FinField, k::FinField)
  b = basis(K)
  K = base_field(K)
  while absolute_degree(K) > absolute_degree(k)
    b = [x*y for x = basis(K) for y = b]
    K = base_field(K)
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
#   use exp/log for the height bit...
#alternatively just use the lin. alg
# 1+p^k/1+p^l, * = p^k/p^l, + for k<l<=2k ...

h2_is_iso(::QadicField) = true
h2_is_iso(::PadicField) = true
function h2_is_iso(K::Hecke.LocalField)
  p = prime(K)
  e = absolute_ramification_index(K)
  k, mk = residue_field(K)
  pi = uniformizer(K)
  pi = setprecision(pi, 2*e)
  eps = setprecision(K, precision(K)+e) do
    -inv(divexact(pi^e, p))
  end
  #assert valuation(eps) == 0
  kt, t = polynomial_ring(k, "t", cached = false)
  f = t^(p-1)-mk(eps)
  return length(roots(f)) == 0
end

function one_unit_group_gens(K::Union{QadicField, Hecke.LocalField})
  p = prime(K)
  e = absolute_ramification_index(K)
  f = absolute_inertia_degree(K)
  if e %(p-1) == 0 && !h2_is_iso(K)
    return _unit_group_gens_case2(K)
  else
    return _unit_group_gens_case1(K)
  end
end


function _unit_group_gens_case2(K::Union{QadicField, Hecke.LocalField})
  p = prime(K)
  e = absolute_ramification_index(K)
  f = absolute_inertia_degree(K)

  k, mk = residue_field(K)
  @assert absolute_degree(k) == f
  omega = absolute_basis(k)
  @assert isone(omega[1]) #this has to change...
  mu_0 = valuation(e, p)+1
  e_0 = divexact(e, (p-1)*p^(mu_0-1))

  kt, t = polynomial_ring(k, "t", cached = false)
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
  ps = findfirst(x->!iszero(coeff(r, x)), 0:degree(k))
  #omega still needs to be a basis after projection,
  #so put the weird element into a position of a non-vanishing coeff.
  #the Steiniz basis change theorem will make it work
  omega[ps] = r

  b = [preimage(mk, x) for x = omega]
  F_K = [ lambda for lambda = 1:ceil(Int, p*e//(p-1))-1 if lambda % p != 0]
  @assert length(F_K) == e

  one = K(1)
  gens = [ one+x*pi^l for x = b for l = F_K]
  push!(gens, one+preimage(mk, omega_s)*pi^(p^mu_0*e_0))
  return gens
end

function _unit_group_gens_case1(K::Union{QadicField, Hecke.LocalField})
  p = prime(K)
  e = absolute_ramification_index(K)
  f = absolute_inertia_degree(K)

  k, mk = residue_field(K)
  @assert absolute_degree(k) == f

  b = [preimage(mk, x) for x = absolute_basis(k)]
  F_K = [ lambda for lambda = 1:ceil(Int, p*e//(p-1))-1 if lambda % p != 0]
  @assert length(F_K) == e

  pi = uniformizer(K)
  one = K(1)

  return [ one+x*pi^l for x = b for l = F_K]
end

function coordinates(a::Union{QadicFieldElem, LocalFieldElem}, k)
  c = [coeff(a, i) for i=0:degree(parent(a))-1]
  while absolute_degree(parent(c[1])) > absolute_degree(k)
    c = reduce(vcat, [[coeff(x, i) for i=0:(degree(parent(c[1]))-1)] for x = c])
  end
  if parent(c[1]) != k
    if isa(parent(c[1]), QadicField) && degree(parent(c[1])) ==1
      return [coeff(x, 0) for x = c]
    end
    error("bad tower")
  end
  return c
end
coordinates(a::PadicFieldElem, ::PadicField) = [a]
lift(R::Ring, a::Hecke.LocalFieldValuationRingElem{PadicField, PadicFieldElem}) = lift(R, a.x)

function setprecision!(A::Generic.MatSpaceElem{Hecke.LocalFieldValuationRingElem{PadicField, PadicFieldElem}}, n::Int)
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
  if iszero(b-one)
    setprecision!(K, old)
    return ZZRingElem[0 for i=a], ZZRingElem(1)
  end
  @assert valuation(b-one) > 0
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
  Qp = absolute_base_field(K)
  Zp = ring_of_integers(Qp)
  expo_mult = identity_matrix(ZZ, length(cur_a))
  #transformation of cur_a to a
  expo = zero_matrix(ZZ, 1, length(cur_a))
  pk = ZZRingElem(p)

  val_offset = e .* map(valuation, absolute_basis(K))
  pow_b = ZZRingElem(1)

  while l <= k
#    @show 1, l, pow_b, k, expo
    last_val = e*valuation(cur_b-one)
#    @show expo_mult
    @assert e*valuation(cur_b-one) >= l
    @assert all(x->isone(x) || e*valuation(x-one) >= l, cur_a)

    A = abelian_group([p^max(0, ceil(Int, (l-v)//e)) for v = val_offset])
    h = hom(free_abelian_group(length(cur_a)), A, [A([lift(ZZ, x) for x =  absolute_coordinates(divexact(y-one, pi^l))]) for y = cur_a])
    lhs = A([lift(ZZ, x) for x = absolute_coordinates(divexact(cur_b -one, pi^l))])
    fl, s = has_preimage_with_preimage(h, lhs)
    _k, _mk = kernel(h)
    #if kernel has HNF, the next step is cheaper...
    _mk.map = hnf(_mk.map)
    #to find a nice preimage
    reduce_mod_hnf_ur!(s.coeff, _mk.map)
#    @show s
    # to verify that this is a "legal" operation... the hom constructor
    # will verify that this is legal
    # hom(domain(_mk), codomain(_mk), [_mk(x) for x = gens(domain(_mk))])

    if !fl
      pow_b *= p
      cur_b = cur_b^p
      expo = expo * p
      if iszero(cur_b-one)
        break
      end
      last_val = e*valuation(cur_b-one)
      continue
    end

    expo += s.coeff * expo_mult
    expo_mult = reduce(vcat, [_mk(x).coeff for x = gens(_k)])*expo_mult
    cur_a = [prod(cur_a[i]^_mk(x)[i] for i=1:length(cur_a)) for x = gens(_k)]
#    @show [e*valuation(x-1) for x = cur_a]

    cur_b = divexact(b^pow_b, prod(a[i]^expo[i] for i=1:length(a)))
    if iszero(cur_b-one) || e*valuation(cur_b-one) >= k
      break
    end
#    @show e*valuation(cur_b-one), 2l-1, last_val, k
    @assert e*valuation(cur_b-one) >= min(2*l-1, last_val)
    last_val = e*valuation(cur_b-one)

    if l == k
      break
    end
    l *= 2
    l = min(l, k)
  end
  setprecision!(K, old)
  return [expo[1, i] for i=1:length(cur_a)], pow_b
end

function is_norm(K::Hecke.LocalField, b::Union{QadicFieldElem,PadicFieldElem,Hecke.LocalFieldElem})
  return _norm_equation(K, b, test_only = true)::Bool
end

function norm_equation(K::Hecke.LocalField, b::Union{QadicFieldElem,PadicFieldElem,Hecke.LocalFieldElem})
  return _norm_equation(K, b, test_only = false)::elem_type(K)
end

function _norm_equation(K:: Hecke.LocalField, b::Union{QadicFieldElem,PadicFieldElem,Hecke.LocalFieldElem}; test_only::Bool)
  if iszero(b)
    test_only && return true
    return zero(K)
  end
  if ramification_index(K, parent(b)) == 1
    if test_only
      return Int(valuation(b)*absolute_ramification_index(K)) % degree(K, parent(b)) == 0
    end
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
  # Note: we don't need (or use) the Teichmueller lift as it is not
  # available in general. We need any element X s.th. N(X) = b mod p
  # then b/N(X) is a 1-unit
  @assert valuation(b) == 0
  k, mk = residue_field(K)
  fl, rt = is_power(mk(K(b)), e)
  test_only && !fl && return false
  @assert fl
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
  s, po = solve_1_units(ng, bb)
  test_only && return po == 1
  @assert po == 1
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
@doc raw"""
    norm_equation(F::Union{fqPolyRepField, Hecke.RelFinField}, b::Union{fpFieldElem, fqPolyRepFieldElem})

Find an element `x` in `F` such that the norm from `F` down to the parent of
`b` is exactly `b`.
"""
function norm_equation(F::Union{fqPolyRepField, Hecke.RelFinField, FqField}, b::Union{fpFieldElem, fqPolyRepFieldElem, FqFieldElem})
   if iszero(b)
      return zero(F)
   end
   k = parent(b)
   n = degree(F, k)
   kt, = polynomial_ring(k, "t", cached = false)
   f = kt(vcat([b],[rand(k) for i = 1:n-1],[one(k)]))
   while !is_irreducible(f)
     f = kt(vcat([b],[rand(k) for i = 1:n-1],[one(k)]))
   end
   return (-1)^(n)*any_root(F, f)
end

function basis(K::RelFinField)
  b = [gen(K)^0]
  while length(b) < degree(K)
    push!(b, b[end]*gen(K))
  end
  return b
end

absolute_frobenius_matrix(K::fqPolyRepField, d::Int = 1) = frobenius_matrix(K, d)
absolute_frobenius_matrix(K::Nemo.fpField, d::Int = 1) = matrix(K, 1, 1, [1])

function absolute_frobenius_matrix(K::RelFinField, d::Int=1)
  b = absolute_basis(K)
  q = characteristic(K)^d
  b = [x^q for x = b]
  return matrix([absolute_coordinates(x) for x = b])
end

absolute_representation_matrix(a::fqPolyRepField) = representation_matrix(a)
absolute_representation_matrix(a::fpFieldElem) = matrix(parent(a), 1, 1, [a])

function absolute_frobenius_matrix(a::FqField, d::Int = 1)
  b = absolute_basis(a)
  b = [absolute_frobenius(x, d) for x = b]
  return matrix([absolute_coordinates(x) for x = b])
end


function absolute_representation_matrix(a::Union{RelFinFieldElem, FqFieldElem})
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

struct ArtinSchreierSolveCtx{T, S}
  frob_mat::T
  basis::S

  function ArtinSchreierSolveCtx(K::FinField, d::Int)
    M = absolute_frobenius_matrix(K, d)
    B = absolute_basis(K)
    return new{typeof(M), typeof(B)}(M, B)
  end
end

@doc raw"""
    frobenius_equation(d::Int, c::Union{fpFieldElem, fqPolyRepFieldElem})

    Find an element `x` in `parent(c)` such that `frobenius(x, d) = x*c`.
    If the norm of `c` is one, this is supposed to work.

    (Hilbert 90)
"""
function frobenius_equation(d::Int, c::FinFieldElem)
   F = parent(c)
   if iszero(c)
      return zero(F)
   end
   p = characteristic(F)
   #F is a GF(p) vector space and x->x^(p^d)-cx is a linear map
   M = absolute_frobenius_matrix(F, d) - absolute_representation_matrix(c)
   k = kernel(M, side = :left)
   @assert nrows(k) > 0
   return dot(absolute_basis(F), k[1, :])
end

function frobenius_equation(X::ArtinSchreierSolveCtx, c::FinFieldElem)
   F = parent(c)
   if iszero(c)
      return zero(F)
   end
   p = characteristic(F)
   #F is a GF(p) vector space and x->x^(p^d)-cx is a linear map
   M = X.frob_mat - absolute_representation_matrix(c)
   k = kernel(M, side = :left)
   @assert nrows(k) > 0
   return dot(X.basis, k[1, :])
end


@doc raw"""
    artin_schreier_equation(d::Int, c::Union{fpFieldElem, fqPolyRepFieldElem})

    Find an element `x` in `parent(c)` such that `frobenius(x, d) -x = c`.
    Additive Hilbert 90.
"""
function artin_schreier_equation(d::Int, c::FinFieldElem)
   F = parent(c)
   p = characteristic(F)
   #F is a GF(p) vector space and x->x^(p^d)-x is a linear map
   M = absolute_frobenius_matrix(F, d)
   M = M-identity_matrix(base_ring(M), nrows(M))
   b = matrix(base_ring(M), 1, ncols(M), absolute_coordinates(c))
   s = solve(M, b; side = :left)
   return dot(absolute_basis(F), s)
end

function artin_schreier_equation(X::ArtinSchreierSolveCtx, c::FinFieldElem)
   F = parent(c)
   p = characteristic(F)
   #F is a GF(p) vector space and x->x^(p^d)-x is a linear map
   M = X.frob_mat
   M = M-identity_matrix(base_ring(M), nrows(M))
   b = matrix(base_ring(M), 1, ncols(M), absolute_coordinates(c))
   s = solve(M, b, side = :left)
   return dot(X.basis, s)
end

function frobenius(E::Hecke.LocalField, F::Union{Hecke.LocalField, PadicField, QadicField})
  #stupid approach... if E/F is unramified, then lifting of one root
  #should be enough,
  a = automorphism_list(E, F)
  K, mK = residue_field(E)
  k, mk = residue_field(F)
  b = gen(E)
  bb = [mK(x(b)) for x = a]
  f = findall(isequal(mK(b)), bb)
  @assert length(f) == 1
  f = findall(isequal(bb[f[1]]^order(k)), bb)
  @assert length(f) == 1
  return a[f[1]]
end

struct MapEvalCtx
  domain::Ring
  codomain::Ring

  map::Generic.MatSpaceElem{PadicFieldElem}

  function MapEvalCtx(M::LocalFieldMor)
    mat = matrix(absolute_base_field(domain(M)),
                 absolute_degree(domain(M)),
                 absolute_degree(codomain(M)),
                 reduce(vcat, [absolute_coordinates(M(x))
                      for x = absolute_basis(domain(M))]))

    return new(domain(M), codomain(M), mat)
  end
end

function Hecke.image(M::MapEvalCtx, a::LocalFieldElem)
  b = inv_absolute_coordinates(M.codomain, absolute_coordinates(a)*M.map)
  return b
end

function (M::MapEvalCtx)(a::LocalFieldElem)
  return image(M, a)
end

"""
solve, hopefully,
    x^phi//x = c
    for phi the Frobenius of parent(c) over F

Requires norm(c) == 1  for the norm relative to the Frobenius

(multiplicative Hilbert 90)
"""
function frobenius_equation(c::Hecke.LocalFieldElem, F::Union{PadicField, QadicField, Hecke.LocalField}; frobenius = false)
  E = parent(c)
  #solves using Lagrange resolvent
  #problem: we'd like to have a unit solution (no precision loss when
  #inverting), but the resolvent tends to have valuation (small primes)
  #possibilities:
  # - start with negative valuation to get a solution of val 0
  # - live with the valuation and use frobenius_equation2 to
  #   add precision at the end
  # - start with elem of val 0, then generically, the valuation of the
  #   resolvent should be the valuation of the abs. degree
  #   as long as the valuation comes from primes in ZZ, that are
  #   Galois-invariant, we can just scale by p and get a solution of
  #   val zero

  local fr::MapEvalCtx

  if frobenius == false
    fr = MapEvalCtx(Hecke.frobenius(E, F))
  else
    if isa(frobenius, MapEvalCtx)
      fr = frobenius
    else
      fr = MapEvalCtx(frobenius)# ::Map{LocalField, LocalField}
    end
  end

  v_deg = valuation(absolute_degree(E), prime(E))
  setprecision(E, precision(E) + v_deg) do
    cd = setprecision(c, precision(E))
    #careful: the function only works if norm(c) == 1
    #increasing the precision will break this
    cnt = 0
    while true
      local gamma
      while true
        gamma = random_elem(E)#*uniformizer(E, -absolute_ramification_index(E))
        if !iszero(gamma) && valuation(gamma) == 0
          break
        end
      end
      b = gamma
      a = zero(E)
      for i=1:divexact(absolute_degree(E), absolute_degree(F))
        a += b
        b = cd*fr(b)
      end
      iszero(a) && continue
      va = valuation(a)
      va == 0 && return inv(a)
      # @show va, v_deg
      if va <= v_deg
        denominator(va) == 1 && return inv(divexact(a, prime(E)^Int(va)))
        # @show :shit
      end

#      return frobenius_equation2(c, F, frobenius = fr, start = inv(a))
      cnt += 1
      if cnt > 5
        return frobenius_equation2(c, F, frobenius = fr)
      end
    end
  end #setprecision
end

#solve the same as above, but pi-adic digit by pi-adic digit, thus
#slow for large precision
function frobenius_equation2(c::Hecke.LocalFieldElem, F::Union{PadicField, QadicField, Hecke.LocalField}; frobenius = false, start::Union{Nothing, Hecke.LocalFieldElem} = nothing)
  E = parent(c)
  pr = precision(c)
  K, mK = residue_field(E)
  d = absolute_inertia_degree(base_field(E))
  X = ArtinSchreierSolveCtx(K, d)
  if start === nothing
    a0 = preimage(mK, frobenius_equation(X, mK(c)))
  else
    a0 = setprecision(start, precision(c))
  end

  local fr::MapEvalCtx
  if frobenius == false
    fr = MapEvalCtx(Hecke.frobenius(E, base_field(E)))
  else
    fr = frobenius# ::Map{LocalField, LocalField}
  end
  #so we have (should have) valuation(fr(a0)//a0 -c) > 0
  #since a0 better be a unit, this becomes valuation(fr(a0) - c*a0) > 0
  if fr(a0) == c*a0
    return a0
  end
  @assert valuation(fr(a0) - c*a0)>0
  s = a0
  is = inv(s)
  p = uniformizer(E)
  eF = absolute_ramification_index(F)
  eE = absolute_ramification_index(E)
  @assert valuation(p)*eE == 1
  bla = 1
  cc = c*s*fr(is)
  v = valuation(cc-1)
  while true
    if isone(cc)
      return s
    end
    @assert v > 0
    pvE = uniformizer(E, Int(v*eE); prec = pr)
    pvE_inv = uniformizer(E, -Int(v*eE); prec = pr)
    x = mK((cc-1)* pvE_inv)
    a = preimage(mK, artin_schreier_equation(X, x))
    t = (1+pvE*a)
    s *= t
    is *= inv(t)
    cc = c*s*fr(is)
    if isone(cc)
      return s
    end
    vv = valuation(cc - 1)
    if vv*eE >= pr
      return setprecision(s, pr)
    end
    @assert vv > v "does not converge"
    v = vv

    bla += 1
    if bla > eE*precision(c)
      error("does not converge")
    end
  end
end


"""
    gens(L::FinField, l::FinField)

Return l-algebra generators for L, l must be a direct subfield of L
"""
function gens(L::FinField, l::FinField)
  L == l && return [one(L)]
  g = [gen(L)]
  K = base_field(L)
  while absolute_degree(K) >= absolute_degree(l) && !isa(K, Nemo.fpField)
    K == l && return g
    push!(g, L(gen(K)))
    K = base_field(K)
    K == l && return g
  end
  @assert K == l
  return g
end

#big TODO: figure out how to do this relative...
#  want local class for (K/k)_p, but the completions of k and K do not
#  know of each other. In current example C:Q_p = 20, but C:c = 5, so
#  4x faster if restricted automorphisms are used.
function local_fundamental_class_serre(L::Hecke.LocalField, K::PadicField)
  return local_fundamental_class_serre(hom(K, L))
end

function local_fundamental_class_serre(L::Hecke.LocalField, K::Union{Hecke.LocalField, QadicField})
  return local_fundamental_class_serre(hom(K, L, L(gen(K))))
end



function local_fundamental_class_serre(mKL::LocalFieldMor)
  K = domain(mKL)
  L = codomain(mKL)

  e = divexact(absolute_ramification_index(L), absolute_ramification_index(K))
  d = divexact(absolute_inertia_degree(L), absolute_inertia_degree(K))
  E = unramified_extension(L, e)[1]
  G = automorphism_list(L, absolute_base_field(L))
  gK = map(mKL, gens(K, absolute_base_field(K)))
  G = [g for g = G if map(g, gK) == gK]
  @assert Base.length(G) == absolute_degree(L)/absolute_degree(K)

  u = mKL(uniformizer(K))//uniformizer(L)^e
  @assert valuation(u) == 0
  v = norm_equation(E, u)
  @assert valuation(v) == 0
  @assert norm(v) == u
  pi = v*uniformizer(L)
  pi_inv = inv(pi)

  #if (like here) L is Eisenstein over unram, then the automorphisms are easier
  
  if ramification_index(L) == degree(L) && e > 1#so we're ramified
    #thus Gal(E/base_field(L)) = Gal(L/base_field(L)) x unram of base_field
    bL = base_field(L)
    E2, _ = unramified_extension(map_coefficients(x->bL(coeff(x, 0)), defining_polynomial(E), cached = false))
    G2 = automorphism_list(E2, absolute_base_field(E2))
    GG = morphism_type(E)[]
    for e = G2
      ime = e(gen(E2))
      imeE = E(map_coefficients(L, ime.data, cached = false))
      res_e = coeff(e(E2(gen(bL))), 0)
      for g = G
        res_g = coeff(g(L(gen(bL))), 0)
        if res_e == res_g
          push!(GG, hom(E, E, g, imeE, check = !false))
        end
      end
    end
    @assert length(GG) == divexact(absolute_degree(E), absolute_degree(K))
#    @assert all(x->x in GG, automorphism_list(E, K))
  else
    GG = automorphism_list(E, absolute_base_field(E))
    gK = map(E, gK)
    GG = [g for g = GG if map(g, gK) == gK]
  end

  rE, mE = residue_field(E)
  rL, mL = residue_field(L)
  rK, mK = residue_field(K)
  # how is this supposed to work?
  mrKL = hom(rK, rL, mL(mKL(preimage(mK, gen(rK)))))
  q = order(rK)

  #the gens are necessary as sometimes the defining eq. for rE is over
  #F_p rather than rL - then just testing the gen(rE) amounts to restricting
  #to a much smaller subfield
  power_frob_L = [gens(rL, prime_field(rL))]
  while length(power_frob_L) < absolute_degree(rL)/absolute_degree(rK)
    push!(power_frob_L, power_frob_L[end] .^q)
  end

  power_frob_E = [gens(rE, prime_field(rL))]
  while length(power_frob_E) < absolute_degree(rE)/absolute_degree(rK)
    push!(power_frob_E, power_frob_E[end] .^q)
  end

  fr = MapEvalCtx(frobenius(E, L))

  z = findall(isequal([mE(fr(preimage(mE, x))) for x = gens(rE, prime_field(rE))]), power_frob_E)
  @assert length(z) == 1
#  @assert z[1] == d+1  #for d == 1 wrong

  beta = []
  sigma_hat = []
  #need to map and compare all generators
  gL = gens(L, absolute_base_field(L))
  imGG = map(x->map(x, map(E, gL)), GG)
  imG = map(x->map(x, gL), G)

  function G_mul(i::Int, j::Int)
    gij = map(G[i], imG[j])
    f = findall(isequal(gij), imG)
    if f === nothing || length(f) == 0
      f = argmax([valuation(x-gij) for x = imG], dims = 1)
    end
    @assert length(f) == 1
    return f[1]
  end

  for sigma = G
    #sigma induces on the residue field a power of frobenius - we want the
    #power...
    fa = findall(isequal(map(E, map(sigma, gL))), imGG)
    #fa are all extensions of sigma to L...
    #but now we want a specific one:
    #sigma, restricted to the residue field is some power of frobenius
    #we want sigma^-1 restricted to be frob^j for small j
    power_L = 1
    if !isa(rL, Nemo.fpField)
      power_L = findall(isequal([mL(sigma(preimage(mL, x))) for x = gens(rL, prime_field(rL))]), power_frob_L)
      @assert length(power_L) == 1
      power_L = power_L[1]
    end
    power_E = [findfirst(isequal([mE(GG[i](preimage(mE, x))) for x = gens(rE, prime_field(rE))]), power_frob_E) for i = fa]

#    @show fb = findall(isequal(power_L), power_E)
#    @assert length(fb) == 1
#    @assert fb[1] == argmin(power_E)

    i = power_L = power_L == 1 ? d : power_L-1
    #now i in Debeerst (2.2) is power_L
    fb_inv = [x == 1 ? x : (length(G) - (x-1) + 1) for x = power_E]
    fb = argmin(fb_inv, dims = 1) #the unique elem <= d
    @assert length(fb) == 1

    c = GG[fa[fb[1]]](pi) * pi_inv

#    @assert isone(norm(c))

    us = frobenius_equation(c, K, frobenius = fr)
    #think...
    @assert fr(us) == c*us || valuation(fr(us) - c*us) >= precision(c)//absolute_ramification_index(E)
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

  return function(h, g)
    i = findall(isequal(g), G)
    @assert length(i) == 1
    i = i[1]
    if i === nothing
      i = argmax(valuation(g(gen(L))-x) for x = imG)
    end
    j = findall(isequal(h), G)
    @assert length(j) == 1
    j = j[1]
    if j === nothing
      j = argmax(valuation(h(gen(L))-x) for x = imG)
    end
    a = mul(beta[i], action(i, beta[j])) .* map(inv, beta[G_mul(i,j)])
    cmp(a, b) = (a == b || valuation(a-b) > 5)
    @assert all(cmp(a[1], a[j]) for j=2:length(a))
    return inv(coeff(a[1], 0))
  end

  #=

cmp(a, b) = (a == b || valuation(a-b) > 5)

Zx, x = ZZ["x"]
k = splitting_field(x^3-2)

l2 = prime_decomposition(maximal_order(k), 2)
k2 = Hecke.generic_completion(k, l2[1][1])  #S(3)(6)
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
   f,mf = residue_field(K)
   F,mF = residue_field(L)
   ee = absolute_ramification_index(K)
   if mf(b) == f(1)
      f_nm = L(1)
   else
      f_nm = norm_equation(F,mf(b))
      f_nm = mF\(f_nm)
   end
   b = b//norm(f_nm)
   if isone(b) || iszero(b-1)
     return f_nm
   end
   b = setprecision(b,prec_b)
   c = L(1)
   C = [L(1)]
   _b = b//norm(C[1])-1
   @assert !iszero(_b)
   n = ee*valuation(_b)
   r = random_elem(L)
   tr = trace(r)
   while iszero(r) || iszero(tr) || valuation(tr) != 0 || valuation(r//L(tr)) != 0
      r = random_elem(L)
      tr = trace(r)
   end
   z = ((b//norm(c))-1)//piK^ZZ(n)
   setprecision!(z, prec_b)
   push!(C, 1+ piL^ZZ(n)* (L(z)*r//L(trace(r))))
   c = prod(C)
   nc = norm(c)
   if iszero(b//nc-1)
     return c*f_nm
   end

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


function _order_1_unit(a::LocalFieldElem)
  if isone(a)
    return ZZRingElem(1)
  end
  pr = precision(a)
  one = Base.one(parent(a))
  v = valuation(a-one)
  @assert v > 0
  p = prime(parent(a))
  b = a^p
  k = 1
  e = absolute_ramification_index(parent(a))
  while !isone(b) && !iszero(b-one) && e*valuation(b-one) <= pr
    k += 1
    b = b^p
  end
  return p^k
end

function one_unit_group(K::LocalField)
  gens = one_unit_group_gens(K)

  if length(gens) == absolute_degree(K)
    o = map(_order_1_unit, gens)
    G = abelian_group([minimum(o) for x = gens])
    from_G = function (g::FinGenAbGroupElem)
      return prod(gens[i]^g[i] for i=1:length(gens))
    end
    to_G = function (a::LocalFieldElem)
      @assert parent(a) == K
      s, e = solve_1_units(gens, a)
      @assert e == 1
      return G(s)
    end
  else
    @assert length(gens) == absolute_degree(K)+1
    rel, po = solve_1_units(gens[1:end-1], gens[end])
    push!(rel, -po)
    h, t = hnf_with_transform(matrix(ZZ, length(gens), 1, rel))
    while h[1,1] > 20
      #=
      Eisenstein extension with defining polynomial x^2 + (2^1 + 2^2 + 2^3 + 2^4 + 2^5 + 2^6 + 2^7 + 2^8 + 2^9 + 2^10 + 2^11 + 2^12 + 2^13 + 2^14 + 2^15 + 2^16 + 2^17 + 2^18 + 2^19 + 2^20 + 2^21 + 2^22 + 2^23 + 2^24 + 2^25 + 2^26 + 2^27 + 2^28 + 2^29 + 2^30 + 2^31 + O(2^32))*x + 2^1 + O(2^32) over Unramified extension of 2-adic numbers of degree 1

      gens[1]^4 == gens[2]^4, hence gens[3] is independent.
      solve_1_units -> rework as rels_1_units
      completion of x^2+1 at 2
      =#
      # @show :permuting, h[1,1]
      i = rand(1:length(gens)-1)
      gens[end], gens[i] = gens[i], gens[end]
      rel, po = solve_1_units(gens[1:end-1], gens[end])
      push!(rel, -po)
      h, t = hnf_with_transform(matrix(ZZ, length(gens), 1, rel))
    end


    #h[1,1] is the torsion part - it should be a power of p
    #t (and/or the inverse) should give the basis of the free bit
    ti = inv(t)
    #1st col should be the torsion generator, the others the free bit
    bas = [prod(gens[i]^ti[i,j] for i=1:length(gens)) for j=1:length(gens)]
    #bas[1] is torsion
    #torsion kan only happen in small precision k*e < e/(p-1) I think
    e = absolute_ramification_index(K)
    pr = e*ceil(Int, ZZRingElem(e)//(prime(K)-1))
    if pr < 2 && prime(K) == 2
      pr = 2 #to see different signs
    end

    tor = [setprecision(one(K), pr), setprecision(bas[1], pr)]
    while length(tor) < h[1,1]
      push!(tor, setprecision(tor[end]*tor[2], pr))
    end

    ord = map(_order_1_unit, gens[2:end])
    ord = vcat(h[1,1], [minimum(ord) for x = bas[2:end]])
    G = abelian_group(ord)
    from_G = function (g::FinGenAbGroupElem)
      return prod(bas[i]^g[i] for i=1:length(gens))
    end
    to_G = function (a::LocalFieldElem) #still uncertain
      s, p = solve_1_units(bas[2:end], a)
      s = [divexact(x, p) for x = s]
      y = prod(bas[i+1]^s[i] for i=1:length(s)) * inv(a)
      y = setprecision(y, pr)
      z = findfirst(isequal(y), tor)
      @assert z !== nothing
      if p != 1
        b = a*bas[1]^(z-1)
        s, p = solve_1_units(bas[2:end], b)
        @assert p == 1
      end
      ex = vcat([-z+1], s)
      x = (prod(bas[i]^ex[i] for i=1:length(bas))*inv(a))
        @assert isone(x) || iszero(x-1) || (#=@show valuation(x-1);=# e*valuation(x-1) >= precision(a))
      return G(ex)
    end
  end
  return G, MapFromFunc(G, K, from_G, to_G)
end

function teichmuller(a::LocalFieldElem)
  k, mk = residue_field(parent(a))
  ka = mk(a)
  if iszero(ka)
    return zero(a)
  end
  q = order(k)
  if q == 2
    return one(a)
  end

  fs = preimage(mk, inv((q-1)*ka^(q-2)))
  while true
    fa = a^(q-1)-1
    if iszero(fa)
      return a
    end
    a = a-fa*fs
    fs = fs*(2-fs*(q-1)*a^(q-2))
  end
end

function unit_group(K::LocalField)
  U, mU = one_unit_group(K)
  k, mk = residue_field(K)
  u, mu = unit_group(k)

  #group is Z x u x U ...

  Z = abelian_group([0])
  G, pro, inj = direct_product(Z, u, U, task = :both)

  gk = preimage(mk, mu(u[1]))
  gk = teichmuller(gk)
  @assert order(u[1]) == order(u)

  from_G = function(g::FinGenAbGroupElem)
    return uniformizer(K)^g[1] * gk^pro[2](g)[1] * mU(pro[3](g))
  end

  to_G = function(x::LocalFieldElem)
    v = Int(absolute_ramification_index(K)*valuation(x))
    x *= uniformizer(K)^-v
    @assert valuation(x) == 0
    r = mk(x)
    x *= inv(gk^preimage(mu, r)[1])
    @assert iszero(x-1) || valuation(x-1)>0
    return inj[1](v*Z[1]) + inj[2](preimage(mu, r)) + inj[3](preimage(mU, x))
  end

  return G, MapFromFunc(G, K, from_G, to_G)
end

#=
function unit_group(R::LocalFieldValuationRing)
  K = R.Q
  U, mU = one_unit_group(K)
  k, mk = residue_field(K)
  u, mu = unit_group(k)

  #group is u * U ...

  G, pro, inj = direct_product(u, U, task = :both)

  from_G = function(g::FinGenAbGroupElem)
    return preimage(mk, mu(pro[1](g))) * mU(pro[2](g))
  end

  to_G = function(x::LocalFieldElem)
    r = mk(x)
    x *= inv(preimage(mk, r))
    return inj[1](preimage(mu, r)) + inj[2](preimage(mU, x))
  end

  return G, MapFromFunc(G, K, from_G, to_G)
end

=#

@doc raw"""
    is_local_norm(mkK::Map, a::AbsSimpleNumFieldElem) -> Bool

Let    
    ```mkK : k \to K```
be a map (embedding) of number fields.    

Tests if ``a`` is a local norm for the relative extension implicit in the map.
That is for a prime ideal ``p`` in ``k`` let ``Q_i`` the primes above.
``a`` is a local norm if there are ``b_i`` in the completions at ``Q_i`` s.th. the 
    ```\prod N(b_i) = q```
where the norm ``N`` is form the completion at ``Q_i`` down to the completion
at ``p``.  
"""
function is_local_norm(mkK::Map{AbsSimpleNumField, AbsSimpleNumField}, a::AbsSimpleNumFieldElem)

  k = domain(mkK)
  K = codomain(mkK)
  @assert parent(a) == k

  ZK = maximal_order(K)
  zk = maximal_order(k)

  #need al (relative) ramified primes, so the relative
  #disc. but it should hold that
  #d_K/k = norm (D_K/k)
  #D_K/q = D_K/k * D_k/q, so
  #norm(D_K/k) = norm(D_K/q / D_k/q) = norm(D_K/q) / D_k/q^degree(K/k)
  #
  # D : different, d : discriminant

  D = divexact(norm(mkK, different(ZK); order = zk), different(zk)^divexact(degree(K), degree(k)))

  #need to test local norm at all primes dividing RHS + primes in D
  #well, at the prime in K above...

  #for unram. primes, only the valuation counts: the local norm is surjective
  #on units
  #inf. places
  if signature(k)[1] > 0 
    for i = complex_places(K)
      ki = restrict(embeddings(i)[1], mkK)
      if isreal(ki) && real(evaluate(a, ki)) < 0
        return false
      end
    end
  end

  S = collect(keys(factor(D)))
  for p = keys(factor(a*zk))
    p in S && continue
    push!(S, p)
  end

  for p = S
    allQ = collect(keys(factor(Hecke.induce_image(mkK, p; target = ZK))))
    v = valuation(D, p)
    if v == 0
      d = mapreduce(inertia_degree, gcd, allQ; init = 0)
      d = divexact(d, inertia_degree(p))
      if valuation(a, p) % d != 0
        return false
      end
      continue
    end
    #the norm_cts needs to invert a matrix and this seems to loose
    #precision proportional to the valuation 
    #times ram_index: due to the different ways to measure precision
    c, mc = completion(k, p, (20+v)*ramification_index(p))

    b = mc(a)
    gens = []
    imgs = FinGenAbGroupElem[]
    U, mU = unit_group(c)#, n_quo = divexact(degree(K), degree(k)))
    for Q = allQ
      C, mC = completion(K, Q, (20+v)*ramification_index(Q))
      t = norm_ctx(mc, mC, mkK)

      R, mR = residue_field(C)
      u, mu = unit_group(R)#, n_quo = divexact(degree(K), degree(k)))
      g = preimage(mR, mu(u[1]))
      pr = precision(g)
      gkk = setprecision(g^order(R), pr)
      while !iszero(gkk - g)
        g = gkk
        gkk = setprecision(g^order(R), pr)
      end
      gs = Hecke.one_unit_group_gens(C)
      push!(gs, g)
      push!(gs, uniformizer(C))
      no = FinGenAbGroupElem[]
      for g = gs
        n = t(g)
        push!(no, preimage(mU, n))
      end
      append!(imgs, no)
    end
    F = free_abelian_group(length(imgs))
    h = hom(F, U, imgs)
    if ! has_preimage_with_preimage(h, preimage(mU, mc(a)))[1]
      return false
    end
  end
  return true
end
#= TODO
 - implement n_quo properly
 - re-organize: write a function for norm_group and use it
 - think: in many cases this should be trivial due to degrees
=#

@doc raw"""
    function is_local_norm(K::Hecke.RelSimpleNumField{AbsSimpleNumFieldElem}, a::AbsSimpleNumFieldElem) -> Bool

Tests if `a`, an element in the coefficient field of `K` is a local norm in
the idel sense, i.e. a product of norms of the completions extending
a completions of the base field.
"""
function is_local_norm(K::Hecke.RelSimpleNumField{AbsSimpleNumFieldElem}, a::AbsSimpleNumFieldElem)
  k = base_field(K)
  @req parent(a) == k "element must be in the base field of the 1st argument"

  Ka, mkK = absolute_simple_field(K)
  return is_local_norm(hom(k, Ka, preimage(mkK, K(gen(k)))), a)
end

#TODO: qadic is also missing
#TODO: extend the n_quo to actually compute K^*/()^n_quo

@doc raw"""
    unit_group(K::PadicField; n_quo::Int = -1) -> FinGenAbGroup, Map

Returns a group ``U`` and a map ``f: U \to\K^*``. ``U`` is an approximation
to the unit group up to the precision of ``K``. More precisely, if
```K^* = \langle p\rangle  \times \mathbbb F_p^* \times 1+p\mathbbb Z_p```
Then ``U`` will be isomorphic to ``\mathbbb Z \times \mathbbb Z/(p-1) \times \mathbbb Z/p^(k-1)``.

If `n_quo` is given and positive, then ``\mathbbb F_p^*`` will be replaced
by the quotient modulo `n_quo`-th powers. (To avoid the costly discrete
logarithm in the finite field)
"""
function Hecke.unit_group(K::PadicField; n_quo::Int = -1)
  p = prime(K)
  r, mr = residue_field(K)
  u, mu = unit_group(r; n_quo)
  g = teichmuller(preimage(mr, mu(u[1])))
  A = abelian_group([0, order(u), p^(precision(K)-2)])
  function fl(y::PadicFieldElem)
    v = valuation(y)
    y *= K(p)^-v
    @assert valuation(y) == 0
    @assert mr(y) != 0
    f = preimage(mu, mr(y))
    if n_quo > -1
      y *= inv(teichmuller(y))
    else
      y *= g^-f[1]
    end
    return A(ZZRingElem[v, f[1], lift(ZZ, divexact(y-1, p))])
  end  
  return A, MapFromFunc(A, K, x-> p^x[1]*g^x[2]*(1+p*x[3]), fl)
end

@doc raw"""
    is_local_norm(k::Hecke.AbsSimpleNumField, a::ZZRingElem) -> Bool

Tests if `a` is a local norm in `k`.    
"""
function is_local_norm(k::Hecke.AbsSimpleNumField, a::ZZRingElem)
  #need to test local norm at all primes dividing RHS + primes in D
  #well, at the prime in K above...
  if signature(k)[1] == 0  && #totally complex 
     a < 0
    return false
  end
  #for unram. primes, only the valuation counts: the local norm is surjective
  #on units

  zk = maximal_order(k)
  S = ramified_primes(zk)
  for p = keys(factor(a).fac)
    p in S && continue
    push!(S, p)
  end

  prec = 20
  for p = S
    P = prime_ideals_over(zk, p)
    if valuation(discriminant(zk), p) == 0
      d = mapreduce(inertia_degree, gcd, P; init = 0)
      if valuation(a, p) % d != 0
        return false
      end
      continue
    end
    Qp = padic_field(p, precision = prec)
    #for each P we need
    # - a gen (pi) for the valuation
    # - a gen for the residue field
    # - the one-unit gens
    gens = []
    imgs = FinGenAbGroupElem[]
    U, mU = unit_group(Qp; n_quo = degree(k))
    for Q = P
      c, mc = completion(k, Q, prec)
      r, mr = residue_field(c)
      u, mu = unit_group(r)
      @assert ngens(u) == 1
      g = preimage(mr, mu(u[1]))
      pr = precision(g)
      gkk = setprecision(g^order(r), pr)
      while !iszero(gkk - g)
        g = gkk
        gkk = setprecision(g^order(r), pr)
      end
      gs = [uniformizer(c), g]
      append!(gs, Hecke.one_unit_group_gens(c))
#      push!(gens, gs)
      no = FinGenAbGroupElem[]
      for g = gs
        n = absolute_norm(g)
        v = n.v
        n.v = 0
        n = Qp(lift(ZZ, n))
        n.v = v
        push!(no, preimage(mU, n))
      end
      append!(imgs, no)
    end
    F = free_abelian_group(length(imgs))
    h = hom(F, U, imgs)
    if ! has_preimage_with_preimage(h, preimage(mU, Qp(a)))[1]
      return false
    end
  end
  return true
end

function is_local_norm(k::Hecke.AbsSimpleNumField, a::Integer)
  return is_local_norm(k, ZZ(a))
end

function is_local_norm(k::Hecke.AbsSimpleNumField, a::QQFieldElem)
  return is_local_norm(k, numerator(a)*denominator(a)^degree(k))
end

function is_local_norm(k::Hecke.AbsSimpleNumField, a::Rational)
  return is_local_norm(k, QQ(a))
end

@doc raw"""
Given number fields ``k`` and ``K`` as well as a prime ``p`` in ``k`` and
``Q`` above ``p`` in ``K`` via maps:
```mkK: k \to K```
```mc: k \to k_p```
```mC: K \to K_Q```
this function returns a function 
    ```N: K_Q \to k_p```
implementing the norm of this extension.
(In particular the extension ``K_Q/k_p`` is not explicit here)
"""
function norm_ctx(mc::Map{AbsSimpleNumField, <:Hecke.LocalField}, mC::Map{AbsSimpleNumField, <: Hecke.LocalField}, mkK::Map{AbsSimpleNumField, AbsSimpleNumField})
  #we have k -> K two number fields
  #        k -> c a completion
  #        K -> C a completion
  #this produces data to compute a norm from C to c
  #
  #c (and C) are completions, hence Eisenstein oder Unramifield
  #with basis the product basis pi^i and rho^j, pi for the ramified and rho
  #for the unram.
  #Thus a basis for C/c is given by the pi and rho from C but the
  #exponents for rho up to f(C)/f(c) and for pi: e(C)/e(c)
  #Thus we get a different basis for C via the image the basis of
  #c, transported to k, then to K then to C and the powers.
  #writing elements in this basis we can compute norms via rep. mat.
  #possible in 2 steps: C down to U*c, then U*c -> c

  c = codomain(mc)
  C = codomain(mC)
  k = domain(mc)
  @assert k == domain(mkK)
  K = domain(mC)
  @assert K == codomain(mkK)
  fc = absolute_inertia_degree(c)
  fC = absolute_inertia_degree(C)
  ec = absolute_ramification_index(c)
  eC = absolute_ramification_index(C)

  pi_C = uniformizer(C)
  rho_C = gen(base_field(C))

  pow_pi = [one(C)]
  while length(pow_pi) < eC/ec
    push!(pow_pi, pow_pi[end]*pi_C)
  end

  pow_rho = [one(base_field(C))]
  while length(pow_rho) < fC/fc
    push!(pow_rho, pow_rho[end]*rho_C)
  end
  pow_rho = map(C, pow_rho)

  b_k = absolute_basis(c)
  b_kK = [mC(mkK(preimage(mc, x))) for x = b_k]
 
  #now the product basis of b_kK, pow_rho and pow_pi
  b_K = [x*y*z for x = pow_pi for y = pow_rho for z = b_kK]
  T = matrix(hcat([absolute_coordinates(x) for x = b_K]...))

  S = inv(T)
  
  function norm(x)
    e = divexact(eC, ec)
    f = divexact(fC, fc)
    n = length(b_k)
    img = S*matrix(hcat([absolute_coordinates(x*t) for t = pow_pi]...))
    m = matrix(C, length(pow_pi), length(pow_pi), [sum(img[(i-1)*f*n+j, k]*b_K[j] for j=1:f*n) for i=1:e for k=1:e])
    d = det(m)
    img = S*matrix(hcat([absolute_coordinates(d*t) for t = pow_rho]...))
    m = matrix(c, length(pow_rho), length(pow_rho), [sum(img[j+(i-1)*n, k]*b_k[j] for j=1:n) for i=1:f for k=1:f])
    return det(m)
  end
  return norm
end

