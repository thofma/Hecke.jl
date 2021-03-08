export relative_simple_extension

################################################################################
#
#  Relative extension
#
################################################################################

@doc Markdown.doc"""
    relative_simple_extension(K::NumField, k::NumField) -> NfRel

Given two fields $K\supset k$, it returns $K$ as a simple relative 
extension $L$ of $k$ and an isomorphism $L \to K$.
"""
relative_simple_extension(K::NumField, k::NumField)



function relative_simple_extension(K::AnticNumberField, k::AnticNumberField)
  fl, mp = issubfield(k, K)

  return relative_extension(mp)
end


function relative_simple_extension(K::NumField, k::NumField)
  Kabs, mKabs = absolute_simple_field(K)
  kabs, mkabs = absolute_simple_field(k)
  fl, mp = issubfield(kabs, Kabs)
  if !fl
    error("k is not a subfield of K")
  end
  L, mL = relative_extension(mp)
  ktoL = inv(mkabs)*mp*inv(mL)
  p = map_coeffs(pseudo_inv(ktoL), L.pol)
  Lres, gLres = number_field(p, cached = false, check = false)
  mp1 = hom(Lres, K, inv(mkabs)*mp*mKabs, )
end


function relative_simple_extension(m::NfToNfMor)
  k = domain(m)
  K = codomain(m)
  lf = factor(K.pol, k)
  rel_deg = divexact(degree(K), degree(k))
  pols = [f for (f, v) in lf if degree(f) == rel_deg]
  p = pols[1]
  if length(pols) > 1
    i = 2
    while !iszero(map_coeffs(m, p)(gen(K)))
      p = pols[i]
      i += 1
    end
  end
  L, b = number_field(p, cached = false, check = false)
  mp = hom(K, L, b, inverse = (image_primitive_element(m), gen(K)))
  return L, inv(mp)
end


function _issubfield_easy(k::NumField, K::NumField)
  found = true
  while k != base_field(K)
    K = base_field(K)
    if absolute_degree(k) > absolute_degree(K)
      found = false
      break
    end
  end
  if !found
    return false, morphism_type(k, K)()
  end
  return true, hom(k, K, )
end

################################################################################
#
#
#
################################################################################