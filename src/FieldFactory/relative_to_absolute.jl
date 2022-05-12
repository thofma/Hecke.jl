###############################################################################
#
#  From relative to absolute
#
###############################################################################

function _relative_to_absoluteQQ(L::NfRelNS{nf_elem}, auts::Vector{NfRelNSToNfRelNSMor_nf_elem})
  K, gK = number_field(NfAbsNS, L)
  Ks, mKs = simplified_simple_extension(K, is_abelian = true, cached = false)
  #Now, I have to translate the automorphisms.
  #First, to automorphisms of K.
  autsK = Vector{NfAbsNSToNfAbsNS}(undef, length(auts))
  Qxy = parent(K.pol[1])
  for i = 1:length(auts)
    embs = Vector{NfAbsNSElem}(undef, ngens(K))
    imgs = image_generators(auts[i])
    for j = 1:length(imgs)
      embs[j] = K(map_coefficients(FlintQQ, imgs[j].data, parent = Qxy))
    end
    autsK[i] = hom(K, K, embs, check = false)
  end
  #Final step: translate the automorphisms to Ks
  Hecke._assure_has_inverse_data(mKs)
  autsKs = Vector{NfToNfMor}(undef, length(autsK))
  for i = 1:length(autsK)
    autsKs[i] = hom(Ks, Ks, mKs\(image_primitive_element(mKs*autsK[i])), check = false)
  end
  return Ks, autsKs
end

function _relative_to_absolute(L::NfRelNS{nf_elem}, auts::Vector{NfRelNSToNfRelNSMor_nf_elem})
  Ks, mKs = simplified_absolute_field(L)
  Hecke._assure_has_inverse_data(mKs)
  #Now, I have to translate the automorphisms.
  #First, to automorphisms of K.
  autsKs = Vector{NfToNfMor}(undef, length(auts))
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
