################################################################################
#
#  Relative extension
#
################################################################################

@doc raw"""
    relative_simple_extension(K::NumField, k::NumField) -> RelSimpleNumField

Given two fields $K\supset k$, it returns $K$ as a simple relative
extension $L$ of $k$ and an isomorphism $L \to K$.
"""
function relative_simple_extension(K::NumField, k::NumField)
  if _issubfield_in_tower(k, K)
    return relative_ext_in_tower(K, k)
  end
  error("Not yet implemented")
end


function relative_ext_in_tower(K::NumField, k::NumField)
  el = primitive_element(K, k)
  f = minpoly(el, k)
  L = number_field(f, cached = false, check = false)[1]
  mL = hom(L, K, el)
  return L, mL
end

function relative_simple_extension(K::AbsSimpleNumField, k::AbsSimpleNumField)
  fl, mp = is_subfield(k, K)
  @assert fl
  return relative_simple_extension(mp)
end

function relative_simple_extension(m::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
  k = domain(m)
  K = codomain(m)
  lf = factor(k, K.pol)
  rel_deg = divexact(degree(K), degree(k))
  pols = [f for (f, v) in lf if degree(f) == rel_deg]
  p = pols[1]
  if length(pols) > 1
    i = 2
    while !iszero(map_coefficients(m, p, cached = false)(gen(K)))
      p = pols[i]
      i += 1
    end
  end
  L, b = number_field(p, cached = false, check = false)
  mp = hom(K, L, b, inverse = (image_primitive_element(m), gen(K)))
  return L, inv(mp)
end



################################################################################
#
#  Relative minpoly
#
################################################################################

function minpoly(a::NumFieldElem, K::NumField)
  if !_issubfield_in_tower(K, parent(a))
    error("Not yet implemented!")
  end
  f = minpoly(a)
  g = norm(f, K)
  if is_squarefree(g)
    return g
  else
    h = gcd(g, derivative(g))
    return divexact(g, h)
  end
end

function minpoly(a::NumFieldElem, ::QQField)
  return absolute_minpoly(a)
end

################################################################################
#
#  IsSubfieldTower
#
################################################################################

function _issubfield_in_tower(k::NumField, K::NumField)
  if absolute_degree(k) == 1
    return true
  end
  found = true
  while k != base_field(K)
    K = base_field(K)
    if absolute_degree(k) > absolute_degree(K)
      found = false
      break
    end
  end
  return found
end

################################################################################
#
#  Relative primitive element
#
################################################################################

function primitive_element(K::NumField, k::NumField; check::Bool = true)
  if _issubfield_in_tower(k, K)
    return primitive_element_tower(K, k)
  else
    if check
      @assert is_subfield(k, K)[1]
    end
    return primitive_element_generic(K, k)
  end
end

function primitive_element_generic(K::NumField, k::NumField)
  return absolute_primitive_element(K)
end

function primitive_element_tower(K::NumField, k::NumField)
  pK = primitive_element(K)
  if base_field(K) == k
    return pK
  end
  if is_primitive_over(pK, k)
    return pK
  end
  L = base_field(K)
  gL = primitive_element(L, k)
  pK += gL
  while !is_primitive_over(pK, k)
    pK += gL
  end
  return pK
end

function is_primitive_over(a::NumFieldElem, k::NumField)
  return divexact(absolute_degree(parent(a)), absolute_degree(k)) == degree(minpoly(a, k))
end
