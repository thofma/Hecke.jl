@doc Markdown.doc"""
    norm(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField} -> NfOrdIdl

Given an embedding $m:k\to K$ of number fields and an integral ideal in $K$, find the norm
$N_{K/k}(I)$.
"""
function norm(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField}
  K = codomain(m)
  @assert K == nf(order(I))
  k = domain(m)
  zk = maximal_order(k)
  if degree(k) == 1
    return ideal(zk, norm(I))
  end
  if I.is_principal == 1
    if isdefined(I, :princ_gen)
      return ideal(zk, zk(norm(m, (I.princ_gen).elem_in_nf)))
    elseif isdefined(J,:princ_gen_special)
      el = J.princ_gen_special[2] + J.princ_gen_special[3]
      return ideal(zk, zk(norm(m, el)))
    end
  end
  assure_2_normal(I)
  J = ideal(zk, I.gen_one^div(degree(K), degree(k)), zk(norm(m, I.gen_two.elem_in_nf)))
  J.gens_normal = I.gens_normal
  return J
end

function norm(m::T, I::NfOrdFracIdl) where T <: Map{AnticNumberField, AnticNumberField}
  return norm(m, numerator(I))//denominator(I)^div(degree(codomain(m)), degree(domain(m)))
end


#TODO: intersect_nonindex uses a worse algo in a more special case. Combine.
#  for prime ideals, the gcd's can be done in F_p/ F_q hence might be faster
@doc Markdown.doc"""
    minimum(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField} -> NfOrdIdl

Given an embedding $m:k\to K$ of number fields and an integral ideal in $K$, find the
intersect $I \cap \mathbf{Z}_k$.
"""
function minimum(m::T, I::NfOrdIdl) where T <: Map{AnticNumberField, AnticNumberField}
  K = codomain(m)
  @assert K == nf(order(I))
  k = domain(m)
  zk = maximal_order(k)
  if degree(k) == 1
    return ideal(zk, minimum(I))
  end
  assure_2_normal(I) # basically implies order(I) is maximal

  if !isone(gcd(minimum(I), index(order(I))))
    bk = map(m, basis(maximal_order(k), k))
    bK = map(K, basis(I))
    d = lcm(lcm(map(denominator, bk)), lcm(map(denominator, bK)))
    F = FreeModule(FlintZZ, degree(K))

    hsk = ModuleHomomorphism(FreeModule(FlintZZ, degree(k)), F, elem_type(F)[F(matrix(FlintZZ, 1, degree(K), coefficients(d*x))) for x = bk])
    hsK = ModuleHomomorphism(F, F, elem_type(F)[F(matrix(FlintZZ, 1, degree(K), coefficients(d*x))) for x = bK])
    sk = image(hsk)
    imhsK = image(hsK)
    mm = intersect(sk[1], imhsK[1])
    return ideal(zk, elem_type(zk)[zk(x.v) for x = map(x->preimage(hsk, sk[2](mm[2](x))), gens(mm[1]))])
  end

  # Here is a version with abelian groups
  #if !isone(gcd(minimum(I), index(order(I))))
  #  bk = map(m, basis(maximal_order(k), k))
  #  bK = map(K, basis(I))
  #  d = lcm(lcm(map(denominator, bk)), lcm(map(denominator, bK)))
  #  F = abelian_group([0 for i in 1:degree(K)])
  #  hsk = hom(abelian_group[0 for i in 1:degree(k)], F, elem_type(F)[F(matrix(FlintZZ, 1, degree(K), coefficients(d*x))) for x = bk])
  #  hsK = hom(F, F, elem_type(F)[F(matrix(FlintZZ, 1, degree(K), coefficients(d*x))) for x = bK])
  #  sk = image(hsk)
  #  imhsK = image(hsK)
  #  mm = intersect(sk[1], imhsK[1], false)
  #  return ideal(zk, elem_type(zk)[zk(collect(x.coeff)) for x = map(x->preimage(hsk, sk[2](mm[2](x))), gens(mm[1]))])
  #end

  @assert K == nf(order(I))
  k = domain(m)
  kt, t = PolynomialRing(k, cached = false)
  Qt = parent(K.pol)
  h = gcd(gen(k) - evaluate(Qt(m(gen(k))), t), evaluate(K.pol, t))
  g, ai, _ = gcdx(evaluate(Qt(I.gen_two.elem_in_nf), t) % h, h)
  @assert g == 1
  #so ai * a = 1 in K/k
  c = content_ideal(ai, zk)
  n,dd = integral_split(c)
  J = ideal(zk, I.gen_one) + dd
  J.gens_normal = I.gens_normal
  return J
end

function minimum(m::T, I::NfOrdFracIdl) where T <: Map{AnticNumberField, AnticNumberField}
  return minimum(m, numerator(I))//denominator(I)
end


################################################################################
#
#  Prime decomposition
#
################################################################################

@doc Markdown.doc"""
    intersect_prime(f::Map, P::NfOrdIdl, O_k::NfOrd) -> NfOrdIdl

Given a prime ideal $P$ in $K$ and the inclusion map $f:k \to K$
of number fields, find the unique prime $p$ in $k$ below.
$p$ will be in the order $O_k$ which defaults to "the" maximal order of $k$.
"""
function intersect_prime(f::Map, P::NfOrdIdl, Ok::NfOrd = maximal_order(domain(f)))
  @assert isprime(P)
  p = minimum(P)
  if isone(degree(Ok))
    res = ideal(Ok, p)
    res.is_prime = 1
    res.splitting_type = (1, 1)
    return res
  end
  k = domain(f)
  K = codomain(f)
  OK = maximal_order(K)
  if !isindex_divisor(Ok, p) && !isindex_divisor(OK, p)
    return intersect_nonindex(f, P, Ok)
  end
  d = degree(P)
  lp = prime_decomposition(Ok, p, d, 1)
  for (Q, v) in lp
    el = Q.gen_two
    if f(K(el)) in P
      return Q
    end
  end
  error("Restriction not found!")

end

function intersect_nonindex(f::Map, P::NfOrdIdl, Zk::NfOrd = maximal_order(domain(f)))
  @assert isprime(P)
  #let g be minpoly of k, G minpoly of K and h in Qt the primitive
  #element of k in K (image of gen(k))
  #then
  #  g(h) = 0 mod G
  k = domain(f)
  K = codomain(f)
  G = K.pol
  Qx = parent(G)
  g = change_base_ring(base_ring(Qx), k.pol, parent = Qx)
  h = Qx(f(gen(k)))

  Fp, xp = PolynomialRing(GF(Int(minimum(P)), cached=false), cached=false)
  gp = factor(Fp(g))
  hp = Fp(h)
  Gp = gcd(Fp(K(P.gen_two)), Fp(G))
  for (s, e) in gp
    if iszero(s(hp) % Gp)
      p = ideal_from_poly(Zk, Int(minimum(P)), s, e)
      return p
    end
  end
end


@doc Markdown.doc"""
    prime_decomposition_nonindex(f::Map, p::NfOrdIdl, Z_K::NfOrd) -> Vector{Tuple{NfOrdIdl, Int}}

Given a map $f: k\to K$ of number fields defined over $\mathbb Q$ and
a prime ideal in the maximal order of $k$, find all prime ideals in
the maximal order of $K$ above.
The ideals will belong to $Z_K$ which defaults to "the" maximal order of $K$.
"""
function prime_decomposition(f::Map, p::NfOrdIdl, ZK::NfOrd = maximal_order(codomain(f)))
  @assert p.is_prime == 1
  k = domain(f)
  K = codomain(f)
  if degree(k) == 1
    return prime_decomposition(ZK, minimum(p))
  end
  if !divisible(index(ZK), minimum(p))
    return prime_decomposition_nonindex(f, p, ZK)
  end
  # TODO: Implement for nonindex divisors seriously,
  # splitting the algebra.
  lp = prime_decomposition(ZK, minimum(p))
  res = Tuple{NfOrdIdl, Int}[]
  el = f(p.gen_two.elem_in_nf)
  for (P,_) in lp
    v = valuation(el, P)
    # p has a two-normal presentation, so to test the ramification
    # I only need to test the second element.
    if v > 0
      push!(res, (P, v))
    end
  end
  return res

end

function prime_decomposition_nonindex(f::Map, p::NfOrdIdl, ZK = maximal_order(codomain(f)))

  k = domain(f)
  K = codomain(f)
  G = K.pol
  Qx = parent(G)
  res = Tuple{NfOrdIdl, Int}[]
  if fits(Int, minimum(p))
    Fp = PolynomialRing(GF(Int(minimum(p)), cached = false), cached = false)[1]
    Gp = factor(ppio(Fp(G), Fp(f(p.gen_two.elem_in_nf)))[1])
    for (ke, e) in Gp
      P = ideal_from_poly(ZK, Int(minimum(p)), ke, e)
      push!(res, (P, divexact(e, ramification_index(p))))
    end
  else
    Fp1 = PolynomialRing(GF(minimum(p), cached = false), cached = false)[1]
    Gp1 = factor(ppio(Fp1(G), Fp1(Qx(f(K(p.gen_two)))))[1])
    for (ke, e) in Gp1
      P = ideal_from_poly(ZK, minimum(p), ke, e)
      push!(res, (P, divexact(e, ramification_index(p))))
    end
  end
  return res
end

function prime_decomposition_type(f::Map, p::NfOrdIdl, ZK = maximal_order(codomain(f)))

  if !isindex_divisor(ZK, minimum(p)) && !isramified(ZK, minimum(p))
    return prime_decomposition_type_nonindex(f, p, ZK)
  end
  lp = prime_decomposition(f, p, ZK)
  res = Vector{Tuple{Int, Int}}(undef, length(lp))
  for i = 1:length(lp)
    res[i] = (divexact(degree(lp[i][1]), degree(p)), lp[i][2])
  end
  return res

end

function prime_decomposition_type_nonindex(f::Map, p::NfOrdIdl, ZK = maximal_order(codomain(f)))
  k = domain(f)
  K = codomain(f)
  G = K.pol
  Qx = parent(G)

  if fits(Int, minimum(p, copy = false))
    Fp = PolynomialRing(GF(Int(minimum(p)), cached = false), cached = false)[1]
    Gp = factor_shape(gcd(Fp(f(K(p.gen_two))), Fp(G)))
  else
    Fpp = PolynomialRing(GF(minimum(p), cached = false), cached = false)[1]
    Gp = factor_shape(gcd(Fpp(f(K(p.gen_two))), Fpp(G)))
  end
  res = Vector{Tuple{Int, Int}}(undef, sum(values(Gp)))
  ind = 1
  for (d, e) in Gp
    for i = 1:e
      res[ind] = (d, 1)
      ind += 1
    end
  end
  return res
end
