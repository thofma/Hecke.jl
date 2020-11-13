################################################################################
#
#  Morphisms
#
################################################################################

#mutable struct NfAbsToNfAbsNS <: Map{AnticNumberField, NfAbsNS, HeckeMap, NfAbsToNfAbsNS}
#  header::MapHeader{AnticNumberField, NfAbsNS}
#  prim_img::NfAbsNSElem
#  emb::Array{nf_elem, 1}
#
#  function NfAbsToNfAbsNS(K::AnticNumberField, L::NfAbsNS, a::NfAbsNSElem, emb::Array{nf_elem, 1})
#    function image(x::nf_elem)
#      # x is an element of K
#      f = x.parent.pol.parent(x)
#      return f(a)
#    end
#
#    function preimage(x::NfAbsNSElem)
#      return msubst(data(x), emb)
#    end
#
#    z = new()
#    z.prim_img = a
#    z.emb = emb
#    z.header = MapHeader(K, L, image, preimage)
#    return z
#  end
#
#  function NfAbsToNfAbsNS(K::AnticNumberField, L::NfAbsNS, a::NfAbsNSElem)
#    function image(x::nf_elem)
#      # x is an element of K
#      f = x.parent.pol.parent(x)
#      return f(a)
#    end
#
#    z = new()
#    z.prim_img = a
#    z.header = MapHeader(K, L, image)
#    return z
#  end
#end

#hom(K::AnticNumberField, L::NfAbsNS, a::NfAbsNSElem; check::Bool = false) = NfAbsToNfAbsNS(K, L, a)
#
#hom(K::AnticNumberField, L::NfAbsNS, a::NfAbsNSElem, b::Vector{nf_elem}; check::Bool = false) = NfAbsToNfAbsNS(K, L, a, b)

#mutable struct NfAbsNSToNfAbsNS <: Map{NfAbsNS, NfAbsNS, HeckeMap, NfAbsNSToNfAbsNS}
#  header::MapHeader{NfAbsNS, NfAbsNS}
#  emb::Array{NfAbsNSElem, 1}
#
#  function NfAbsNSToNfAbsNS(K::NfAbsNS, L::NfAbsNS, emb::Array{NfAbsNSElem, 1})
#    function image(x::NfAbsNSElem)
#      # x is an element of K
#      return msubst(data(x), emb)
#    end
#
#    z = new()
#    z.emb = emb
#    z.header = MapHeader(K, L, image)
#    return z
#  end
#end
#
#function id_hom(K::NfAbsNS)
#  return NfAbsNSToNfAbsNS(K, K, gens(K))
#end
#
#function hom(K::NfAbsNS, L::NfAbsNS, emb::Array{NfAbsNSElem, 1}; check::Bool = false)
#  return NfAbsNSToNfAbsNS(K, L, emb)
#end 

function Base.:(*)(f::NfAbsNSToNfAbsNS, g::NfAbsNSToNfAbsNS)
  codomain(f) == domain(g) || throw("Maps not compatible")
  a = gens(domain(f))
  return NfAbsNSToNfAbsNS(domain(f), codomain(g), NfAbsNSElem[ g(f(x)) for x in a])
end

function Base.:(==)(f::NfAbsNSToNfAbsNS, g::NfAbsNSToNfAbsNS)
  if domain(f) != domain(g) || codomain(f) != codomain(g)
    return false
  end

  L = domain(f)

  for a in gens(L)
    if f(a) != g(a)
      return false
    end
  end

  return true
end
