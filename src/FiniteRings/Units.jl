function unit_group(::Type{Oscar.DirectProductGroup}, R::Union{FiniteRing, Oscar.Hecke.AbstractAssociativeAlgebra})
  rngs, rprojs = decompose_into_indecomposable_rings(R)
  grps = [unit_group_nonrecursive(S) for S in rngs]
  D = direct_product([codomain(U) for U in grps])
  injs = Oscar.canonical_injections(D)
  projs = Oscar.canonical_projections(D)

  _preim = (_f, _x) -> begin
    if R isa FiniteRing
      preimage(_f, _x)
    else
      fl, _y = has_preimage_with_preimage(_f, _x)
      @assert fl
      return _y
    end
  end

  return D, RingMultMap(R, D, 
                     x -> prod(injs[i](grps[i](rprojs[i](x))) for i in 1:length(rngs)),
                     y -> sum(_preim(rprojs[i], preimage(grps[i], (projs[i](y)))) for i in 1:length(rngs)))
end

@attr Tuple function unit_group(R::Union{FiniteRing, Oscar.Hecke.AbstractAssociativeAlgebra})
  rngs, rprojs = decompose_into_indecomposable_rings(R)
  grps = [unit_group_nonrecursive(S) for S in rngs]
  D = direct_product([codomain(U) for U in grps])
  Dtofp = isomorphism(FPGroup, D)
  injs = Oscar.canonical_injections(D)
  projs = Oscar.canonical_projections(D)

  _preim = (_f, _x) -> begin
    if R isa FiniteRing
      preimage(_f, _x)
    else
      fl, _y = has_preimage_with_preimage(_f, _x)
      @assert fl
      return _y
    end
  end

  codomain(Dtofp), RingMultMap(R, codomain(Dtofp), 
                        x -> Dtofp(prod(injs[i](grps[i](rprojs[i](x))) for i in 1:length(rngs))),
                        y -> sum(_preim(rprojs[i], preimage(grps[i], (projs[i](preimage(Dtofp, y))))) for i in 1:length(rngs)))
end

function unit_group_nonrecursive(R::Union{FiniteRing, Oscar.Hecke.AbstractAssociativeAlgebra})
  if R isa FiniteRing && is_prime(characteristic(R))
    #@assert fits(Int, p)
    @vprintln :FiniteRings "Ring has prime characterstic. Constructing an algebra ..."
    S, StoR = isomorphism(StructureConstantAlgebra, R)
    @vprintln :FiniteRings "Algebra of type $(typeof(S))"
    U = unit_group_nonrecursive(S)
    return RingMultMap(R, codomain(U), x -> U(preimage(StoR, x)), x -> StoR(preimage(U, x)))
  end
  @vprintln :FiniteRings "Not going via algebra"
  J = get_attribute!(R, :radical) do
    @vprintln :FiniteRings "Computing radical (not cached)"
    radical(R)
  end

  J = radical(R)
  OJ = OnePlusIdeal(J)
  @vprintln :FiniteRings "Constructing presentation unipotent units"
  OJabs = EffectivePresentation(OJ; chain = (Oscar.get_attribute(R, :radical_chain, nothing), 2))
  Rs, RtoRs = quo(R, J)
  if R isa Oscar.Hecke.AbstractAssociativeAlgebra
    A, AtoRs = Rs, Oscar.hom(Rs, Rs, identity_matrix(base_ring(Rs), dim(Rs)), identity_matrix(base_ring(Rs), dim(Rs)); check = false)
  else
    A, AtoRs = isomorphism(Oscar.MatAlgebra, Rs)
  end
  @assert domain(AtoRs) === A
  @vprintln :FiniteRings "Constructing presentation of semisimple quotient"
  Aunitabs = _unit_group_semisimple(A)
  # f : 1 + J -> R^*
  f = x -> x.elem
  fpreim = x -> OJ(x) # R^* -> 1 + R
  # g : R^* -> A^*
  g = x -> preimage(AtoRs, RtoRs(x))
  gpreim = x -> preimage(RtoRs, AtoRs(x))
  @vprintln :FiniteRings "Final extension"
  E = extension(OJabs, Aunitabs, R, f, fpreim, g, gpreim)
  return RingMultMap(R, E.G, E.forward, E.backward)
end

function _unit_group_semisimple(A)
  Adec = decompose(A)
  k1 = Vector{elem_type(A)}()
  idems = [ BtoA(one(B)) for (B, BtoA) in Adec ]
  sum_idems = sum(idems)
  minus_idems = map(x -> -one(A)*x, idems)
  grps = []
  for i = 1:length(Adec)
    B, BtoA = Adec[i]
    C, CtoB = Oscar.Hecke._as_algebra_over_center(B)
    F = base_ring(C)
    M, CtoM = Oscar.Hecke._as_matrix_algebra(C)
    #@show F
    @vprintln :FiniteRings "  Component isomorphic to M_$(Oscar.Hecke._matdeg(M))(F_$(order(F)))"
    G = GL(Oscar.Hecke._matdeg(M), F)
    @vprint :FiniteRings "  Computing presentation of $G ... "
    #GtoH = isomorphism(FPGroup, G)
    #H = codomain(GtoH)
    _P = _effective_presentation_of_glnq(G)
    Oscar.set_order(_P.G, order(G))
    @vprintln :FiniteRings "done"
    H = _P.G
    #@show relators(H)
    P = EffectivePresentation(B, H,
                         x -> begin
                           @assert parent(x) === B
                           _P.forward(G(matrix(CtoM(Oscar.Hecke.preimage(CtoB, x)))))
                         end,
                         y -> begin
                           CtoB(Oscar.Hecke.preimage(CtoM, M(matrix(_P.backward(y)))))
                         end)
    push!(grps, (B, BtoA, P))
    #_gens = Hecke._unit_group_generators(M)
    #gens = [CtoM\g for g in _gens]
    #for aC in gens
    #  aA = BtoA(CtoB(aC))
    #  # In the other components aA should be 1 (this is not mentioned in the Bley/Boltje-Paper)
    #  aA = add!(aA, aA, sum_idems)
    #  aA = add!(aA, aA, minus_idems[i])
    #  push!(k1, aA)
    #end
  end
  GG, emb, proj = direct_product([g[3].G for g in grps], morphisms = true)
  GGtoPP = isomorphism(FPGroup, GG)
  PP = codomain(GGtoPP)

  # now construct the new map
  f = x -> begin
    GGtoPP(prod([ emb[i](grps[i][3].forward(grps[i][2]\(idems[i]*x))) for i in 1:length(grps)]))
  end
  g = y -> begin
    sum([ idems[i] * grps[i][2]((grps[i][3].backward(proj[i](Oscar.Hecke.preimage(GGtoPP, y))))) for i in 1:length(grps)])
  end
  return EffectivePresentation(A, PP, f, g)
end
