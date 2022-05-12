export absolute_primitive_element, absolute_simple_field

################################################################################
#
#  Absolute primitive element
#
################################################################################

@doc Markdown.doc"""
    absolute_primitive_element(K::NumField) -> NumFieldElem
Given a number field $K$, this function returns an element $\gamma \in K$
such that $K = \mathbf{Q}(\gamma)$.
"""
absolute_primitive_element(::NumField)

function absolute_primitive_element(K::NfRelNS)
  k = base_field(K)
  a = primitive_element(K)
  if is_absolutely_primitive(a)
    return a
  end
  gk = absolute_primitive_element(k)
  a += gk
  while !is_absolutely_primitive(a)
    a += gk
  end
  return a
end

function absolute_primitive_element(K::NfRel)
  k = base_field(K)
  gk = absolute_primitive_element(k)
  a = gen(K)
  while !is_absolutely_primitive(a)
    a += gk
  end
  return a
end

function absolute_primitive_element(K::NfAbsNS)
  return primitive_element(K)
end

function absolute_primitive_element(K::AnticNumberField)
  return gen(K)
end

################################################################################
#
#  Is absolutely primitive test
#
################################################################################

#TODO: Put some more thought in it.
#In practice, we should check this modularly
function is_absolutely_primitive(a::NumFieldElem)
  c = conjugates_arb(a, 16)
  is_primitive = true
  for i = 2:length(c)
    for j = i+1:length(c)
      if overlaps(c[i], c[i])
        is_primitive = false
        break
      end
    end
    if !is_primitive
      break
    end
  end
  if is_primitive
    return true
  end
  return degree(absolute_minpoly(a)) == absolute_degree(parent(a))
end

function is_absolutely_primitive(a::T) where T <: Union{NfRelNSElem{nf_elem}, NfRelElem{nf_elem}}
  L = parent(a)
  rt, PR, tmp = _setup_block_system(L)
  if _is_primitive_via_block(a, rt, PR, tmp)
    return true
  end
  return degree(absolute_minpoly(a)) == absolute_degree(parent(a))
end

################################################################################
#
#  Absolute field
#
################################################################################

@doc Markdown.doc"""
    absolute_simple_field(K::NumField) -> NumField, Map

Given a number field $K$, this function returns an absolute simple number field
$M/\mathbf{Q}$ together with a $\mathbf{Q}$-linear isomorphism $M \to K$.
"""
absolute_simple_field(::NumField)

function absolute_simple_field(K::AnticNumberField)
  return K, id_hom(K)
end

function absolute_simple_field(K::NfAbsNS; cached::Bool = true, simplify::Bool = false)
  return simple_extension(K, cached = cached, simplified = simplify)
end

function absolute_simple_field(K::NumField; cached::Bool = false, simplify::Bool = false)
  if simplify
    return simplified_absolute_field(K, cached = cached)
  end
  el = absolute_primitive_element(K)
  f = absolute_minpoly(el)
  Kabs, gKabs = number_field(f, cached = cached, check = false)
  mp = hom(Kabs, K, el)
  embed(mp)
  return Kabs, mp
end

#Special function for NfRel{nf_elem}. In this case, we can easily construct the
#inverse of the isomorphism, so we do it separately
function absolute_simple_field(K::NfRel{nf_elem}; cached::Bool = false, simplify::Bool = false)
  if simplify
    return simplified_absolute_field(K, cached = cached)
  end
  Ka, a, b, c = _absolute_field(K, cached = cached)
  h1 = hom(Ka, K, c, inverse = (a, b))
  embed(h1)
  embed(MapFromFunc(x->preimage(h1, x), K, Ka))
  return Ka, h1
end


#Trager: p4, Algebraic Factoring and Rational Function Integration
function _absolute_field(K::NfRel; cached::Bool = false)
  f = K.pol
  kx = parent(f)
  k = base_ring(kx)
  Qx = parent(k.pol)

  l = 0
  #TODO: Until we don't find a primitive element, we should check
  #primitiveness instead of computing the full norm.
  g = f
  N = norm(g)

  while true
    @assert degree(N) == degree(g) * degree(k)
    if !is_constant(N) && is_squarefree(N)
      break
    end
    l += 1
    g = compose(f, gen(kx) - l*gen(k))
    N = norm(g)
  end

  Ka, gKa = NumberField(N, "x", cached = cached, check = false)
  KaT, T = PolynomialRing(Ka, "T", cached = false)

  # map Ka -> K: gen(Ka) -> gen(K)+ k gen(k)

  # gen(k) -> Root(gcd(g, poly(k)))  #gcd should be linear:
  # g in kx = (Q[a])[x]. Want to map x -> gen(Ka), a -> T

  gg = zero(KaT)
  for i=degree(g):-1:0
    auxp = change_base_ring(Ka, Qx(coeff(g, i)), parent = KaT)
    gg = gg*gKa
    add!(gg, gg, auxp)
    #gg = gg*gKa + auxp
  end

  q = gcd(gg, change_base_ring(Ka, k.pol, parent = KaT))
  @assert degree(q) == 1
  al = -constant_coefficient(q)//leading_coefficient(q)
  be = gKa - l*al
  ga = gen(K) + l*gen(k)

  #al -> gen(k) in Ka
  #be -> gen(K) in Ka
  #ga -> gen(Ka) in K
  return Ka, al, be, ga
end

################################################################################
#
#  Collapse_top_layer function
#
################################################################################

function collapse_top_layer(K::NfRel{T}; cached::Bool = false) where T <: SimpleNumFieldElem
  Ka, a, b, c = _absolute_field(K)
  h1 = hom(Ka, K, c, inverse = (a, b))
  h2 = hom(base_field(K), Ka, a, check = false)
  embed(h1)
  embed(MapFromFunc(x->preimage(h1, x), K, Ka))
  embed(h2)
  return Ka, h1, h2
end
