export fields


################################################################################
#
#  Types
#
################################################################################

mutable struct cocycle_ctx
  projection::GAP.GapObj
  inclusion::GAP.GapObj
  cocycle::Function
  values_cyclic::Function
  gen_kernel::GAP.GapObj
  inclusion_of_pSylow::GAP.GapObj

  function cocycle_ctx(proj::GAP.GapObj, incl::GAP.GapObj, cocycle::Function)
    z = new()
    z.projection = proj
    z.inclusion = incl
    z.cocycle = cocycle
    return z
  end
end


mutable struct FieldsTower
  field::AbsSimpleNumField
  generators_of_automorphisms::Vector{Hecke._AbsSimpleNumFieldAut}
  subfields::Vector{Hecke._AbsSimpleNumFieldHom}
  ramified_primes::Vector{ZZRingElem}
  is_abelian::Bool
  #Solvable embedding problems for the extension
  #They are here to improve the conductor computation
  isomorphism::Dict{Hecke._AbsSimpleNumFieldHom, GAP.GapObj}
  admissible_cocycles::Vector{cocycle_ctx}
  projections_for_conductors::Vector{GAP.GapObj}

  function FieldsTower(K::AbsSimpleNumField, auts::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, subfields::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})
    z = new()
    z.field = K
    z.generators_of_automorphisms = auts
    z.subfields = subfields
    z.is_abelian = false
    return z
  end

end

function Base.show(io::IO, F::FieldsTower)
  print(io, "Field context for the number field defined by $(F.field.pol)")
  return nothing
end

Hecke.degree(F::FieldsTower) = degree(F.field)
Hecke.maximal_order(F::FieldsTower) = maximal_order(F.field)
Hecke.number_field(F::FieldsTower) = F.field

function ramified_primes(F::FieldsTower)
  if !isdefined(F, :ramified_primes)
    f = factor(discriminant(maximal_order(F.field)))
    F.ramified_primes = collect(keys(f.fac))
  end
  return F.ramified_primes
end

################################################################################
#
#  Creation of the context
#
################################################################################

function Hecke.field_context(K::AbsSimpleNumField)
  layers = Vector{Hecke.Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)}[]
  autsK = automorphism_list(K, copy = false)
  lll(maximal_order(K))
  permGC = _from_autos_to_perm(autsK)
  G = _perm_to_gap_grp(permGC)
  D2 = Vector{Tuple{GAP.GapObj, Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)}}(undef, length(autsK))
  for i = 1:length(autsK)
    p =  _perm_to_gap_perm(permGC[i])
    D2[i] = (p, autsK[i])
  end
  @assert GAP.Globals.IsSolvable(G)
  L = GAP.Globals.DerivedSeries(G)
  embs = Vector{Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)}(undef, length(L)-1)
  F = K
  for i = length(L)-1:-1:2
    H = L[i]
    gensGAP = GAP.Globals.GeneratorsOfGroup(H)
    ggs = Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)[ x[2] for x in D2 if GAP.Globals.IN(x[1], gensGAP)]
    push!(layers, closure(ggs))
    Fnew, mF = fixed_field(K, ggs)
    Fnew, mS = simplify(Fnew, cached = false, save_LLL_basis = false)
    fl, mp = is_subfield(Fnew, F)
    @assert fl
    F = Fnew
    embs[i] = mp
  end
  H = L[1]
  gensGAP = GAP.Globals.GeneratorsOfGroup(H)
  ggs = Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)[ x[2] for x in D2 if GAP.Globals.IN(x[1], gensGAP)]
  push!(layers, closure(ggs))
  auts = small_generating_set(layers[1])
  for i = 2:length(layers)
    auts_layers = Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)[x for x in layers[i] if !(x in layers[i-1])]
    append!(auts, small_generating_set(auts_layers))
  end
  KQ = rationals_as_number_field()[1]
  embs[1] = hom(KQ, F, one(F))
  return FieldsTower(K, reverse(auts), embs)
end

################################################################################
#
#  Assure has automorphisms
#
################################################################################

function assure_automorphisms(T::FieldsTower)
  assure_automorphisms(T.field, T.generators_of_automorphisms)
end

function assure_automorphisms(K::AbsSimpleNumField, gens::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})
  if !is_automorphisms_known(K)
    auts = closure(gens, degree(K))
    set_automorphisms(K, auts)
  end
  return nothing
end

###############################################################################
#
#  From automorphisms to permutation groups
#
###############################################################################

function Base.push!(G::AbstractAlgebra.Generic.geobucket{T}, p::T) where {T <: AbstractAlgebra.MPolyRingElem}
   R = parent(p)
   i = max(1, ndigits(length(p), base=4))
   l = length(G.buckets)
   if length(G.buckets) < i
     resize!(G.buckets, i)
     for j in (l + 1):i
       G.buckets[j] = zero(R)
     end
   end
   G.buckets[i] = add!(G.buckets[i], p)
   while i <= G.len
      if length(G.buckets[i]) >= 4^i
         G.buckets[i + 1] = add!(G.buckets[i + 1], G.buckets[i])
         G.buckets[i] = R()
         i += 1
      end
      break
   end
   if i == G.len + 1
      Base.push!(G.buckets, R())
      G.len += 1
   end
end

function permutation_group(G::Vector{<:NumFieldHom{RelNonSimpleNumField{AbsSimpleNumFieldElem}, RelNonSimpleNumField{AbsSimpleNumFieldElem}}})
  permutations = permutation_group1(G)
  return _perm_to_gap_grp(permutations)
end


function permutations(G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})
  K = domain(G[1])
  n = length(G)
  dK = degree(K)
  d = numerator(discriminant(K.pol))
  p = 11
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  fmod = Rx(K.pol)
  while iszero(discriminant(fmod))
    p = next_prime(p)
    R = Native.GF(p, cached = false)
    Rx, x = polynomial_ring(R, "x", cached = false)
    fmod = Rx(K.pol)
  end
  pols = fpPolyRingElem[x]
  gpol = Rx(image_primitive_element(G[1]))
  if gpol != x
    push!(pols, gpol)
    gpol = compose_mod(gpol, pols[2], fmod)
    while gpol != x
      push!(pols, gpol)
      gpol = compose_mod(gpol, pols[2], fmod)
    end
  end
  order = length(pols)

  for i in 2:n
    pi = Rx(image_primitive_element(G[i]))
    if !(pi in pols)
      previous_order = order
      order = order + 1
      push!(pols, pi)
      for j in 2:previous_order
        order = order + 1
        push!(pols, compose_mod(pols[j], pi, fmod))
      end
      if order == dK
        break
      end
      rep_pos = previous_order + 1
      while rep_pos <= order
        for k in 1:i
          po = Rx(image_primitive_element(G[k]))
          att = compose_mod(pols[rep_pos], po, fmod)
          if !(att in pols)
            order = order + 1
            push!(pols, att)
            for j in 2:previous_order
              order = order + 1
              push!(pols, compose_mod(pols[j], att, fmod))
            end
            if order == dK
              break
            end
          end
          if order == dK
            break
          end
        end
        if order == dK
          break
        end
        rep_pos = rep_pos + previous_order
      end
    end
  end
  #Now, I have the images mod p
  Dcreation = Vector{Tuple{fpPolyRingElem, Int}}(undef, length(pols))
  for i = 1:length(pols)
    Dcreation[i] = (pols[i], i)
  end
  perms = Vector{Vector{Int}}(undef, n)
  for i = 1:n
    perms[i] = Vector{Int}(undef, dK)
  end
  gen_pols = fpPolyRingElem[Rx(image_primitive_element(s)) for s in G]
  D = Dict{fpPolyRingElem, Int}(Dcreation)
  for s = 1:n
    for i = 1:length(pols)
      perms[s][i] = D[Hecke.compose_mod(gen_pols[s], pols[i], fmod)]
    end
  end
  return perms
end

function permutation_group(G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})
  return _perm_to_gap_grp(permutations(G))
end

function _from_autos_to_perm(G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})

  K = domain(G[1])
  @assert degree(K) == length(G)
  n = length(G)
  #First, find a good prime
  p = 3
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  fmod = Rx(K.pol)
  while iszero(discriminant(fmod))
    p = next_prime(p)
    R = Native.GF(p, cached = false)
    Rx, x = polynomial_ring(R, "x", cached = false)
    fmod = Rx(K.pol)
  end
  pols = Vector{Tuple{fpPolyRingElem, Int}}(undef, n)
  for i = 1:n
    pols[i] = (Rx(image_primitive_element(G[i])), i)
  end
  D = Dict{fpPolyRingElem, Int}(pols)
  permutations = Vector{Vector{Int}}(undef, n)
  for s = 1:n
    perm = Vector{Int}(undef, n)
    for i = 1:n
      perm[i] = D[Hecke.compose_mod(pols[i][1], pols[s][1], fmod)]
    end
    permutations[s] = perm
  end
  return permutations

end

function _perm_to_gap_grp(perm::Vector{Vector{Int}})
  g = GAP.GapObj[]
  for x in perm
    z = _perm_to_gap_perm(x)
    push!(g, z)
  end
  g1 = GAP.GapObj(g)
  return GAP.Globals.Group(g1)
end

function _perm_to_gap_perm(x::Vector{Int})
  x1 = GAP.GapObj(x)
  z = GAP.Globals.PermList(x1)
  return z
end

function IdGroup(autos::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})
  G = permutation_group(autos)
  return GAP.Globals.IdGroup(G)
end

###############################################################################
#
#  Split Extensions
#
###############################################################################

function _split_extension(G::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, mats::Vector{Hecke.FinGenAbGroupHom})

  gtype = map(Int, domain(mats[1]).snf)
  G1 = permutation_group(G)
  gensG1 = GAP.Globals.GeneratorsOfGroup(G1)
  A = GAP.Globals.AbelianGroup(GAP.GapObj(gtype))
  gens = GAP.Globals.GeneratorsOfGroup(A)
  auts = Vector{GAP.GapObj}(undef, length(mats))
  for i = 1:length(mats)
    images = Vector{GAP.GapObj}(undef, length(gtype))
    for j = 1:length(gtype)
      g = GAP.Globals.Identity(A)
      for k = 1:length(gtype)
        if !iszero(mats[i].map[j,k])
          g *= gens[k]^Int(mats[i].map[j,k])
        end
      end
      images[j] = g
    end
    auts[i] = GAP.Globals.GroupHomomorphismByImages(A, A, gens, GAP.GapObj(images))
  end
  AutGrp = GAP.Globals.Group(GAP.GapObj(auts))
  mp = GAP.Globals.GroupHomomorphismByImages(G1, AutGrp, gensG1, GAP.GapObj(auts))
  return GAP.Globals.SplitExtension(G1, mp, A)

end

###############################################################################
#
#  Check group extension
#
###############################################################################

function check_group_extension(TargetGroup::GAP.GapObj, autos::Vector{<: NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, res_act::Vector{FinGenAbGroupHom})

  GS = domain(res_act[1])
  @assert is_snf(GS)
  expo = Int(GS.snf[end])
  K = domain(autos[1])
  d = degree(K)
  com, uncom = ppio(expo, d)

  if com == 1
    # I only need to check the split extension, since the second cohomology group is
    # trivial, regardless of the action
    if length(res_act) == 1 && is_prime(order(GS)) == 1 && is_prime(degree(K)) && is_coprime(d, order(GS))
      #Just need to check if the action is non trivial
      return !isone(mod(res_act[1].map[1, 1], GS.snf[1]))
    end
    H = _split_extension(autos, res_act)
    if GAP.Globals.IdGroup(H) == TargetGroup
      return true
    else
      return false
    end
  end

  if uncom == 1
    #Need a cohomological check. Only useful in the prime power case.
    return true
  end

  # I check the split extension related to only uncom
  #Now, I have to check if the split extension is isomorphic to IdH
  Qn, mQn = quo(GS, uncom, false)
  S1, mS1 = snf(Qn)
  new_res_act = Vector{FinGenAbGroupHom}(undef, length(res_act))
  for i = 1:length(res_act)
    Mat = mS1.map*mQn.imap*res_act[i].map*mQn.map*mS1.imap
    Hecke.reduce_mod_snf!(Mat, S1.snf)
    new_res_act[i] = hom(S1, S1, Mat)
  end
  H = _split_extension(autos, new_res_act)
  if GAP.Globals.IdGroup(H) == TargetGroup
    return true
  else
    return false
  end

end


###############################################################################
#
#  Interface to find Fields
#
###############################################################################

function field_extensions(list::Vector{FieldsTower}, bound::ZZRingElem, IsoE1::GAP.GapObj, l::Vector{Int}, only_real::Bool; unramified_outside::Vector{ZZRingElem} = ZZRingElem[])

  grp_to_be_checked = Dict{Int, GAP.GapObj}()
  d = degree(list[1])
  n = lcm(l)
  com, uncom = ppio(n, d)
  fac = factor(n)
  for (p, v) in fac
    grp_to_be_checked[Int(p)] = _construct_grp(IsoE1, Int(p)^v)
  end
  if uncom != 1
    IsoCheck = _construct_grp(IsoE1, uncom)
  else
    IsoCheck = IsoE1
  end
  final_list = FieldsTower[]
  for (j, x) in enumerate(list)
    @vprint :Fields 1 "Field $(j)/$(length(list)): $(x.field.pol)"
    @vprintln :FieldsNonFancy 1 "Field $(j)/$(length(list)): $(x.field.pol)"
    append!(final_list, field_extensions(x, bound, IsoCheck, l, only_real, grp_to_be_checked, IsoE1, unramified_outside = unramified_outside))
  end
  return final_list

end

function field_extensions(x::FieldsTower, bound::ZZRingElem, IsoE1::GAP.GapObj, l::Vector{Int}, only_real::Bool, grp_to_be_checked::Dict{Int, GAP.GapObj}, IsoG::GAP.GapObj; unramified_outside::Vector{ZZRingElem} = ZZRingElem[])

  list_cfields = _abelian_normal_extensions(x, l, bound, IsoE1, only_real, IsoG, unramified_outside = unramified_outside)
  if isempty(list_cfields)
    @vprintln :Fields 1 "\e[1F$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Number of new fields found: 0\n"
    @vprintln :FieldsNonFancy 1 "Number of new fields found: 0\n"
    return Vector{FieldsTower}()
  end
  list = from_class_fields_to_fields(list_cfields, x.generators_of_automorphisms, grp_to_be_checked, IsoG)
  @vprint :Fields 1 "\e[1F$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())Computing maximal orders"
  @vprintln :FieldsNonFancy 1 "Computing maximal orders"
  final_list = Vector{FieldsTower}(undef, length(list))
  for j = 1:length(list)
    @vtime :Fields 4 maximal_order(list[j][1])
    fld, autos, embed = _relative_to_absolute(list[j][1], list[j][2])
    previous_fields = Vector{Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)}(undef, length(x.subfields)+1)
    for s = 1:length(x.subfields)
      previous_fields[s] = x.subfields[s]
    end
    previous_fields[end] = embed
    final_list[j] = FieldsTower(fld, autos, previous_fields)
  end

  @vprint :Fields 1 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  @vprintln :Fields 1 "Number of new fields found: $(length(final_list))\n"
  @vprintln :FieldsNonFancy 1 "Number of new fields found: $(length(final_list))\n"
  return final_list

end

###############################################################################
#
#  Interface
#
###############################################################################

function Hecke.fields(a::Int, b::Int, list::Vector{FieldsTower}, absolute_bound::ZZRingElem; only_real::Bool = false, unramified_outside::Vector{ZZRingElem} = ZZRingElem[])
  G = GAP.Globals.SmallGroup(a, b)
  L = GAP.Globals.DerivedSeries(G)
  lvl = _real_level(L)
  first = true
  for i = 2:length(L)-1
    G1 = GAP.Globals.FactorGroup(L[1], L[i])
    if first && GAP.Globals.Size(G1) != degree(list[1].field)
      continue
    end
    first = false
    E1 = GAP.Globals.FactorGroup(L[1], L[i+1])
    H1 = GAP.Globals.FactorGroup(L[i], L[i+1])
    l = GAP.gap_to_julia(Vector{Int64}, GAP.Globals.AbelianInvariants(H1))
    @vprintln :Fields 1 "constructing abelian extensions with invariants $l"
    @vprintln :FieldsNonFancy 1 "constructing abelian extensions with invariants $l"
    o = divexact(GAP.Globals.Size(G), GAP.Globals.Size(E1))
    bound = iroot(absolute_bound, o)
    IsoE1 = GAP.Globals.IdGroup(E1)
    @vprintln :Fields 1 "Number of fields at the $i -th step: $(length(list))"
    @vprintln :FieldsNonFancy 1 "Number of fields at the $i -th step: $(length(list))"
    lG = snf(abelian_group(l))[1]
    invariants = map(Int, lG.snf)
    onlyreal = (lvl > i || only_real)
    #First, I search for obstruction.
    @vprintln :Fields 1 "Computing obstructions"
    @vprintln :FieldsNonFancy 1 "Computing obstructions"
    #@vtime :Fields 1
    list = check_obstruction(list, L, i, invariants)
    @vprintln :Fields 1 "Fields to check: $(length(list))\n"
    @vprintln :FieldsNonFancy 1 "Fields to check: $(length(list))\n"
    if isempty(list)
      return FieldsTower[]
    end
    list = field_extensions(list, bound, IsoE1, invariants, onlyreal, unramified_outside = unramified_outside)
    @vprintln :Fields 1 "Step $i completed"
    @vprintln :FieldsNonFancy 1 "Step $i completed"
    if isempty(list)
      return FieldsTower[]
    end
  end
  if first
    error("The fields given can not be extended!")
  end
  return list
end

function fields_direct_product(g1, g2, red::Int, redfirst::Int, absolute_bound::ZZRingElem; only_real::Bool = false, unramified_outside::Vector{ZZRingElem} = ZZRingElem[])
  b1 = iroot(absolute_bound, g2[1])
  b2 = iroot(absolute_bound, g1[1])
  @vprintln :Fields 1 "The group is the product of $(g1) and $(g2)"
  l2 = Hecke.fields(g2[1], g2[2], b2, only_real = only_real, unramified_outside = unramified_outside)
  if isempty(l2)
    return FieldsTower[]
  end
  if g1 == g2
    return _merge(l2, l2, absolute_bound, red, redfirst, g1, g2)
  end
  l1 = Hecke.fields(g1[1], g1[2], b1, only_real = only_real, unramified_outside = unramified_outside)
  if isempty(l1)
    return FieldsTower[]
  end
  return _merge(l1, l2, absolute_bound, red, redfirst, g1, g2)
end


function Hecke.fields(a::Int, b::Int, absolute_bound::ZZRingElem; using_direct_product::Bool = true, only_real::Bool = false, unramified_outside::Vector{ZZRingElem} = ZZRingElem[])
#fields with galois group: small_group(a, b)
  if a == 1
    @assert b == 1
    K = rationals_as_number_field()[1]
    g = hom(K, K, K(1))
    return FieldsTower[FieldsTower(K, Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)[g], Vector{Hecke.morphism_type(AbsSimpleNumField, AbsSimpleNumField)}())]
  end
  G = GAP.Globals.SmallGroup(a, b)
  if using_direct_product
    g1, g2, red, redfirst = direct_product_decomposition(G, (a, b))
    if g2 != (1, 1)
      @vprintln :Fields 1 "computing extensions with Galois group ($a, $b) and bound ~10^$(clog(absolute_bound, 10))"
      return fields_direct_product(g1, g2, red, redfirst, absolute_bound; only_real = only_real, unramified_outside = unramified_outside)
    end
  end
  L = GAP.Globals.DerivedSeries(G)
  G1 = GAP.Globals.FactorGroup(L[1], L[end-1])
  invariants = GAP.gap_to_julia(Vector{Int}, GAP.Globals.AbelianInvariants(L[end-1]))
  lG = snf(abelian_group(invariants))[1]
  invariants = map(Int, lG.snf)
  if GAP.Globals.IsAbelian(G)
    @vprintln :Fields 1 "computing abelian extension of Q with invariants $(invariants) and bound ~10^$(clog(absolute_bound, 10))"
    @vprintln :FieldsNonFancy 1 "Doing Group ($a, $b) with bound $absolute_bound"
    return abelian_extensionsQQ(invariants, absolute_bound, only_real, unramified_outside = unramified_outside)
  end
  must_be_ram_surely, must_be_ram_maybe = must_be_ramified(L, length(L)-1)
  lvl = _real_level(L)
  IdGroupGAP = GAP.Globals.IdGroup(G1)
  IdGroup = GAP.gap_to_julia(Vector{Int}, IdGroupGAP)
  pinvariants = prod(invariants)
  if must_be_ram_surely
    #The extension must be ramified. Find a constant...
    cd = 1
    if iszero(mod(invariants[end], 2))
      #2 must be wildly ramified
      #The conductor must have at least valuation 2 at every prime over 2...
      cd = 2^pinvariants
    else
      #2 is not wildly ramified. Then we only have the boring bound...
      d = minimum(keys(factor(invariants[end]).fac))
      cd = 2^((d-1)*div(pinvariants, d))
    end
    #But I want the minimum. So I have to look at the other primes..
    SP = PrimesSet(3, -1)
    for p in SP
      if p >= cd
        break
      end
      if iszero(mod(invariants[end], p))
        #p must be wildly ramified
        #The conductor must have at least valuation 2 at every prime over p...
        s = valuation(invariants[end], p)
        cd1 = p^(2*(p^s-p^(s-1))*divexact(pinvariants, p^s))
        if cd > cd1
          cd = cd1
        end
      else
        #p is not wildly ramified. Then we only have the boring bound...
        d = Int(minimum(keys(factor(invariants[end]).fac)))
        cd1 = p^((d-1)*div(pinvariants, d))
        if cd > cd1
          cd = cd1
        end
      end
    end
    bound = iroot(div(absolute_bound, cd), prod(invariants))
  else
    bound = iroot(absolute_bound, prod(invariants))
  end
  list = Hecke.fields(IdGroup[1], IdGroup[2], bound; using_direct_product = using_direct_product, only_real = (only_real || lvl == length(L)-1), unramified_outside = unramified_outside)
  if isempty(list)
    return list
  end
  @vprintln :Fields 1 "computing extensions with Galois group ($a, $b) and bound ~10^$(clog(absolute_bound, 10))"
  @vprintln :Fields 1 "Abelian invariants of the relative extension: $(invariants)"
  @vprintln :Fields 1 "Number of fields at this step: $(length(list))"
  @vprintln :FieldsNonFancy 1 "Number of fields at this step: $(length(list))"

  @vprintln :Fields 1 "Computing obstructions"
  @vprintln :FieldsNonFancy 1 "Computing obstructions"
  #@vtime :Fields 1
  list = check_obstruction(list, L, length(L)-1, invariants)
  @vprintln :Fields 1 "Fields to check: $(length(list))\n"
  @vprintln :FieldsNonFancy 1 "Fields to check: $(length(list))\n"
  if isempty(list)
    return FieldsTower[]
  end
  Id = GAP.Globals.IdGroup(G)
  return field_extensions(list, absolute_bound, Id, invariants, only_real, unramified_outside = unramified_outside)
end
