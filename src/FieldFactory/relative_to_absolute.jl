###############################################################################
#
#  From relative to absolute
#
###############################################################################

function _relative_to_absoluteQQ(L::RelNonSimpleNumField{AbsSimpleNumFieldElem}, auts::Vector{<:NumFieldHom{RelNonSimpleNumField{AbsSimpleNumFieldElem}, RelNonSimpleNumField{AbsSimpleNumFieldElem}}})
  K, gK = number_field(AbsNonSimpleNumField, L)
  Ks, mKs = simplified_simple_extension(K, is_abelian = true, cached = false)
  #Now, I have to translate the automorphisms.
  #First, to automorphisms of K.
  autsK = Vector{morphism_type(AbsNonSimpleNumField)}(undef, length(auts))
  Qxy = parent(K.pol[1])
  for i = 1:length(auts)
    embs = Vector{AbsNonSimpleNumFieldElem}(undef, ngens(K))
    imgs = image_generators(auts[i])
    for j = 1:length(imgs)
      embs[j] = K(map_coefficients(FlintQQ, imgs[j].data, parent = Qxy))
    end
    autsK[i] = hom(K, K, embs, check = false)
  end
  #Final step: translate the automorphisms to Ks
  Hecke._assure_has_inverse_data(mKs)
  autsKs = Vector{morphism_type(AbsSimpleNumField, AbsSimpleNumField)}(undef, length(autsK))
  for i = 1:length(autsK)
    autsKs[i] = hom(Ks, Ks, mKs\(image_primitive_element(mKs*autsK[i])), check = false)
  end
  return Ks, autsKs
end

function _relative_to_absolute(L::RelNonSimpleNumField{AbsSimpleNumFieldElem}, auts::Vector{<:NumFieldHom{RelNonSimpleNumField{AbsSimpleNumFieldElem}, RelNonSimpleNumField{AbsSimpleNumFieldElem}}})
  Ks, mKs = simplified_absolute_field(L)
  Hecke._assure_has_inverse_data(mKs)
  #Now, I have to translate the automorphisms.
  #First, to automorphisms of K.
  autsKs = Vector{automorphism_type(Ks)}(undef, length(auts))
  imggen = mKs(gen(Ks))
  for i = 1:length(auts)
    autsKs[i] = hom(Ks, Ks, mKs\(auts[i](imggen)))
  end
  #finally, the embedding of the base field of L into Ks
  k = base_field(L)
  img = mKs\(L(gen(k)))
  embed = hom(k, Ks, img, check = false)
  return Ks, autsKs, embed
end
