domain(f::RingMultMap) = f.R

codomain(f::RingMultMap) = f.A

(f::RingMultMap)(x) = image(f, x)

function image(f::RingMultMap, x)
  @req parent(x) === domain(f) "Element must be contained in domain"
  @req Oscar.is_invertible(x)[1] "Element must be a unit"
  return f.f(x)::elem_type(f.A)
end

function preimage(f::RingMultMap, y)
  @req parent(y) === codomain(f) "Element must be contained in codomain"
  x = f.g(y)
  @assert parent(x) === domain(f)
  return x
end

function Base.show(io::IO, M::RingMultMap)
   if Oscar.is_terse(io)
      # no nested printing
      print(io, "Map from multiplicative group of ring")
   else
      io = Oscar.pretty(io)
      io = Oscar.terse(io)
      print(io, "Map: ", Oscar.AbstractAlgebra.Lowercase(), domain(M))
      print(io, " -> ", Oscar.AbstractAlgebra.Lowercase(), codomain(M))
   end
end

function Oscar.AbstractAlgebra.show_map_data(io::IO, M::RingMultMap)
  #println(io)
  #println(io, "with", Oscar.AbstractAlgebra.Indent())
  #D = codomain(M)
  #for d in gens(D)
  #  println(io, preimage(M, d), " => ", d)
  #end
end

function direct_product(R, projs::Vector, maps::Vector{<:RingMultMap}; simplify = true)
  _D, _fromD, _intoD = Oscar.biproduct(codomain.(maps)...)
  if simplify
    D, StoD = snf(_D)
    Oscar.set_attribute!(D, :direct_product => nothing, :show => nothing)
    DtoS = inv(StoD)
    fromD = [StoD * d for d in _fromD]
    intoD = [d * DtoS for d in _intoD]
  else
    D = _D
    fromD = _fromD
    intoD = _intoD
  end
  # assemble the map :(
  return D, RingMultMap(R, D,
                    x -> sum(intoD[i](maps[i](projs[i](x))) for i in 1:length(maps)),
                    y -> sum(preimage(projs[i], preimage(maps[i], fromD[i](y))) for i in 1:length(maps)),
                   )
end

function abelianization_of_unit_group(R::Union{FiniteRing, Oscar.Hecke.AbstractAssociativeAlgebra})
  rings, projs = decompose_into_indecomposable_rings(R)
  k1s = [_abelianization_of_unit_group(RR) for RR in rings]
  return direct_product(R, projs, k1s)
end

# non-decomposing version (only the map)
function _abelianization_of_unit_group(R::Union{FiniteRing, Oscar.Hecke.AbstractAssociativeAlgebra})
  u = unit_group_nonrecursive(R)
  A, GtoA = Oscar.maximal_abelian_quotient(Oscar.FinGenAbGroup, codomain(u))
  return RingMultMap(R, A, x -> GtoA(u(x)), y -> preimage(u, (preimage(GtoA, y))))
end

# function _k1_naive(R::FiniteRing)
#   M = Oscar.matrix_ring(R, 3)
#   MR, MRtoM, MtoMR = finite_ring(M)
#   MA, MRtoMA = abelianization_of_unit_group(MR)
#   RA, RtoRA = abelianization_of_unit_group(R)
#   imgs = elem_type(MA)[]
#   for a in gens(RA)
#     m = M(Oscar.diagonal_matrix(R, [preimage(RtoRA, a), one(R), one(R)]))
#     b = MRtoMA(MtoMR(m))
#     push!(imgs, b)
#   end
#   h = hom(RA, MA, imgs)
#   K, KtoRA = Oscar.kernel(h)
#   U = unit_group(R)
#   G = U.G
#   D, DtoG = Oscar.derived_subgroup(G)
#   return vcat(preimage.(Ref(RtoRA), KtoRA.(gens(K))), U.backward.(DtoG.(gens(D))))
# end
#
# function _k1(R)
#   J = radical(R)
#   RR, RtoRR = quo(R, J)
#   RmodIgens = _k1_naive(RR)
#   #U = unit_group(RR)
#   #G = U.G
# #  D, DtoG = Oscar.derived_subgroup(G)
# #  kinR = preimage.(Ref(RtoRR), elem_type(RR)[U.backward.(DtoG(d)) for d in gens(D)])
#   A, RtoA = abelianization_of_unit_group(R)
# #  OJ = OnePlusIdeal(J)
# #  OJabs = AbstractPresentation(OJ)
# #  #gg = append!(RtoA.(kinR), map(x -> RtoA(x.elem), OJabs.backward.(gens(OJabs.G))))
#   gg = append!(RtoA.(preimage.(Ref(RtoRR), RmodIgens)))
#   Q, AtoQ = quo(A, gg)
#   return Q, RingMultMap(R, Q, x -> AtoQ(RtoA(x)), y -> AtoR(preimage(AtoQ, y)))
#   #(quo(A, gg)[1] |> snf)[1]
# end

function k1_simple_ring(R::FiniteRing)
  @assert is_prime(characteristic(R))
  A, AtoRs = Oscar.isomorphism(Oscar.MatAlgebra, R)
  @assert Oscar.is_simple(A)
  # just need to understand if it is M_2(F_2) or not
  q = order(base_ring(A))
  Rab, RtoRab = abelianization_of_unit_group(R)
  if q != 2 || dim(A) != 4
    return _abelianization_of_unit_group(R)
  end
  Q, RabtoQ = quo(Rab, gens(Rab), false)
  S, StoQ = snf(Q)
  return RingMultMap(R, S, x -> StoQ\(RabtoQ(RtoRab(x))), y -> preimage(RtoRab, preimage(RabtoQ, StoQ(y))))
end

function k1_semisimple_pring(R::FiniteRing)
  rings, projs = decompose_semisimple_pring(R)
  k1s = [k1_simple_ring(R) for R in rings]
  D, f = direct_product(R, projs, k1s)
  return f
end

function k1_semisimple_ring(R::FiniteRing)
  rings, projs = decompose_into_prings(R)
  k1s = [k1_semisimple_pring(R) for R in rings]
  return direct_product(R, projs, k1s)
end

# function k1(R::FiniteRing)
#   J = radical(R)
#   RR, RtoRR = quo(R, J)
#   RRu = unit_group(RR)
#   D, DtoG = Oscar.derived_subgroup(RRu.G)
#   RRk1, mRRk1 = k1_semisimple_ring(RR)
#   RRab, mRRab = abelianization_of_unit_group(RR)
#   K, KtoRRab = Oscar.kernel(hom(RRab, RRk1, [mRRk1(preimage(mRRab, x)) for x in gens(RRab)]))
#   # the kernel of R^(ab) -> K_1(R)
#   K = preimage.(Ref(RtoRR), vcat(preimage.(Ref(mRRab), KtoRRab.(gens(K))), RRu.backward.(DtoG.(gens(D)))))
#   Rab, mRab = abelianization_of_unit_group(R)
#   Q, RabtoQ = quo(Rab, mRab.(K), false)
#   return Q, RingMultMap(R, Q, x -> RabtoQ(mRab(x)), y -> preimage(mRab, preimage(RabtoQ, y)))
# end

function k1(R::Union{FiniteRing, Oscar.Hecke.AbstractAssociativeAlgebra})
  rngs, projs = decompose_into_indecomposable_rings(R)
  k1s = [_k1_naive_nonrec(S) for S in rngs]
  return direct_product(R, projs, k1s; simplify = true)
end

function _k1_naive_nonrec(R::Union{FiniteRing, Oscar.Hecke.AbstractAssociativeAlgebra})
  M = Oscar.matrix_ring(R, 3)
  @vprintln :FiniteRings "Constructing matrix ring for $R"
  MR, MRtoM, MtoMR = finite_ring(M)
  @vprintln :FiniteRings "Done"
  @vprintln :FiniteRings "Compute abelianization of unit groups of matrix ring"
  MRtoMA = _abelianization_of_unit_group(MR)
  MA = codomain(MRtoMA)
  @vprintln :FiniteRings "Compute abelianization of unit groups of ring"
  RtoRA = _abelianization_of_unit_group(R)
  RA = codomain(RtoRA)
  imgs = elem_type(MA)[]
  for a in gens(RA)
    m = M(Oscar.diagonal_matrix(R, [preimage(RtoRA, a), one(R), one(R)]))
    b = MRtoMA(MtoMR(m))
    push!(imgs, b)
  end
  h = hom(RA, MA, imgs)
  K, KtoRA = Oscar.kernel(h)
  #return quo(RA, KtoRA.(gens(K)))
  Q, RAtoQ = quo(RA, KtoRA.(gens(K)), false)
  return RingMultMap(R, Q, x -> RAtoQ(RtoRA(x)), y -> preimage(RtoRA, preimage(RAtoQ, y)))
end

