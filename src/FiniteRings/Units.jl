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

################################################################################
#
#  1 + J
#
################################################################################


function EffectivePresentation(Q::OnePlusIdealModuloOnePlusIdeal)
 A, AtoQQ, QQtoA = isomorphism(FinGenAbGroup, Q.Q)
 AbsA = EffectivePresentation(A)
 AbsQ = EffectivePresentation(Q, AbsA.G,
                      x -> begin
                        @assert parent(x) === Q
                        y = QQtoA(x.elem)
                        @assert parent(y) === A
                        z = AbsA.forward(y)
                        @assert parent(z) === AbsA.G
                        return z
                      end,
                      y -> begin
                        @assert parent(y) === AbsA.G
                        zz = AtoQQ(AbsA.backward(y))
                        @assert parent(zz) === Q.Q
                        return OnePlusIdealModuloOnePlusIdealElem(Q, zz)
                      end)
 for i in 1:10
   y = rand(AbsQ.G)
   z = rand(AbsQ.G)
   @assert AbsQ.forward(AbsQ.backward(y)) == y
   @assert AbsQ.backward(y * z) == AbsQ.backward(y) * AbsQ.backward(z)
 end
 return AbsQ
end

function EffectivePresentation(OI::OnePlusIdeal, originalI = ideal(OI); chain = nothing)
  if is_zero(ideal(OI))
    G = free_group(0)
    return EffectivePresentation(OI, G,
                                x -> one(G),
                                y -> one(OI))
  end
  #A = algebra(OI)
  I = ideal(OI)
  # let's do 1 + I^2 -> 1 + I -> (1 + I)/(1 + I^2) -> 1
  if chain === nothing || chain[1] === nothing
    I2 = I * I
  else
    I2 = chain[1][chain[2]]
    #@assert I2 == I * I
  end
  #I2 = I * originalI
  #OI2 = OnePlusIdeal(I2)
  OI2 = OnePlusIdeal(I2) #originalI)
  Q, f = quo(OI, OI2)
  #@info "Structure of (1 + J)/(1 + J^2): $(elementary_divisors(Q.Q.A))"
  AbsQ = EffectivePresentation(Q)
  if is_zero(I2)
    # need to break the cursion
    # f is an isomorphism
    AbsOI = EffectivePresentation(AbsQ, OI, x -> begin @assert parent(x) === OI; z = f(x); @assert parent(z) === Q; return z end,
                                 y -> preimage(f, y))
    return AbsOI
  else
    AbsOI2 = EffectivePresentation(OI2, originalI; chain = (chain[1], chain[2] + 1))
    #@show AbsOI2.G
    #@info "extending"
    # now construct the extension
    res = extension(AbsOI2, AbsQ, OI,
                       # need to supply all the maps
                       # 1 + J^2 -> 1 + J
                       xx -> begin
                         @assert parent(xx) === OI2
                         return OI(xx.elem)
                       end,
                       # preimage under 1 + J^2 -> 1 + J,
                       x -> begin
                         @assert parent(x) === OI
                         return OI2(x.elem)
                       end,
                       # 1 + J -> (1 + J)/(1 + J^2),
                       x -> begin
                         @assert parent(x) === OI
                         return f(x)
                       end,
                       # preimage under 1 + J -> (1 + J)/(1 + J^2)
                       x -> begin
                         @assert parent(x) === Q
                         return preimage(f, x)
                       end)
    return res
  end
end
