################################################################################
#
#  Absolute primitive element
#
################################################################################

@doc raw"""
    absolute_primitive_element(K::NumField) -> NumFieldElem
Given a number field $K$, this function returns an element $\gamma \in K$
such that $K = \mathbf{Q}(\gamma)$.
"""
absolute_primitive_element(::NumField)

function absolute_primitive_element(K::RelNonSimpleNumField)
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

function absolute_primitive_element(K::RelSimpleNumField)
  k = base_field(K)
  gk = absolute_primitive_element(k)
  a = gen(K)
  while !is_absolutely_primitive(a)
    a += gk
  end
  return a
end

function absolute_primitive_element(K::AbsNonSimpleNumField)
  return primitive_element(K)
end

function absolute_primitive_element(K::AbsSimpleNumField)
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

function is_absolutely_primitive(a::T) where T <: Union{RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}, RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}
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

@doc raw"""
    absolute_simple_field(K::NumField) -> NumField, Map

Given a number field $K$, this function returns an absolute simple number field
$M/\mathbf{Q}$ together with a $\mathbf{Q}$-linear isomorphism $M \to K$.
"""
absolute_simple_field(::NumField)

function absolute_simple_field(K::AbsSimpleNumField)
  return K, id_hom(K)
end

function absolute_simple_field(K::AbsNonSimpleNumField; cached::Bool = true, simplify::Bool = false)
  abs = get_attribute(K, :abs_simple_field)
  MT = morphism_type(AbsSimpleNumField, AbsNonSimpleNumField)
  if abs !== nothing
    if haskey(abs::Dict{Bool, Tuple{AbsSimpleNumField, MT}}, simplify)
      return abs[simplify]::Tuple{AbsSimpleNumField, MT}
    end
  else
    abs = Dict{Bool, Tuple{AbsSimpleNumField, MT}}()
    set_attribute!(K, :abs_simple_field => abs)
  end
  L, mL = simple_extension(K, cached = cached, simplified = simplify)
  abs[simplify] = (L, mL)
  return L, mL
end

function absolute_simple_field(K::NumField; cached::Bool = false, simplify::Bool = false)
  local Kabs::AbsSimpleNumField
  MT = morphism_type(AbsSimpleNumField, typeof(K))

  abs = get_attribute(K, :abs_simple_field)
  if abs !== nothing
    if haskey(abs, simplify)
      return abs[simplify]::Tuple{AbsSimpleNumField, MT}
    end
  else
    abs = Dict{Bool, Tuple{AbsSimpleNumField, MT}}()
    set_attribute!(K, :abs_simple_field => abs)
  end

  if simplify
    Kabs, mp = simplified_absolute_field(K, cached = cached)
    abs[simplify] = (Kabs, mp)
    return Kabs, mp
  end
  el = absolute_primitive_element(K)
  f = absolute_minpoly(el)
  Kabs, gKabs = number_field(f, cached = cached, check = false)
  mp = hom(Kabs, K, el)
  embed(mp)
  abs[simplify] = (Kabs, mp)
  return Kabs, mp
end

#Special function for RelSimpleNumField{AbsSimpleNumFieldElem}. In this case, we can easily construct the
#inverse of the isomorphism, so we do it separately
function absolute_simple_field(K::RelSimpleNumField{AbsSimpleNumFieldElem}; cached::Bool = false, simplify::Bool = false)
  MT = morphism_type(AbsSimpleNumField, typeof(K))

  abs = get_attribute(K, :abs_simple_field)
  if abs !== nothing
    if haskey(abs, simplify)
      return abs[simplify]::Tuple{AbsSimpleNumField, MT}
    end
  else
    abs = Dict{Bool, Tuple{AbsSimpleNumField, MT}}()
    set_attribute!(K, :abs_simple_field => abs)
  end

  local Ka::AbsSimpleNumField
  if simplify
    Ka, mp = simplified_absolute_field(K, cached = cached)
    abs[simplify] = (Kabs, mp)
    return Ka, mp
  end
  Ka, a, b, c = _absolute_field(K, cached = cached)
  h1 = hom(Ka, K, c, inverse = (a, b))
  embed(h1)
  embed(MapFromFunc(K, Ka, x->preimage(h1, x)))
  abs[simplify] = (Ka, h1)
  return Ka, h1
end

#Trager: p4, Algebraic Factoring and Rational Function Integration
function _absolute_field(K::RelSimpleNumField; cached::Bool = false, do_embedding::Bool = true)
  f = K.pol
  kx = parent(f)
  k = base_ring(kx)
  Qx = parent(k.pol)

  l = 0
  #TODO: Until we don't find a primitive element, we should check
  #primitiveness instead of computing the full norm.
  g = f
  N = norm(g)

  i = 0
  l = 0

  while true
    @assert degree(N) == degree(g) * degree(k)
    if !is_constant(N) && is_squarefree(N)
      break
    end
    i += 1
    if isodd(i)
      l = -div(i+1, 2)
    else
      l = div(i, 2)
    end
    g = compose(f, gen(kx) - l*gen(k), inner = :second)
    N = norm(g)
  end

  Ka, gKa = number_field(N, "x", cached = cached, check = false)
  KaT, T = polynomial_ring(Ka, "T", cached = false)

  if !do_embedding
    return Ka, gen(Ka), gen(Ka), gen(K)
  end

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

function collapse_top_layer(K::RelSimpleNumField{T}; cached::Bool = false, do_embedding::Bool = true) where T <: SimpleNumFieldElem
  Ka, a, b, c = _absolute_field(K, do_embedding = do_embedding)
  if !do_embedding
    h = hom(Ka, Ka, gen(Ka), check = false)
    return Ka, h, h
  end
  h1 = hom(Ka, K, c, inverse = (a, b), check = false)
  h2 = hom(base_field(K), Ka, a, check = false)
  embed(h1)
  embed(MapFromFunc(K, Ka, x->preimage(h1, x)))
  embed(h2)
  return Ka, h1, h2
end
