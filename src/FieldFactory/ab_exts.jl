add_verbosity_scope(:AbExt)
add_assertion_scope(:AbExt)

add_verbosity_scope(:MaxAbExt)

###############################################################################
#
#  Abelian extensions
#
###############################################################################

function abelian_extensions(O::Union{ZZRing, QQField},
                            gtype::Vector{Int}, discriminant_bound::ZZRingElem;
                            only_real::Bool = false,
                            tame::Bool = false)

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  K, _ = number_field(x - 1, "a", cached = false)
  OK = maximal_order(K)
  l = abelian_extensions(OK, gtype, discriminant_bound,
                         only_real = only_real,
                         tame = tame)
  return l
end

function abelian_extensions(gtype::Vector{Int}, conds::Vector{Int}; only_real::Bool = false)
  K = rationals_as_number_field()[1]
  O = maximal_order(K)
  gtype = map(Int, snf(abelian_group(gtype))[1].snf)
  n = prod(gtype)

  #Getting conductors
  @vprintln :AbExt 1 "Number of conductors: $(length(conds))"
  fields = ClassField{MapRayClassGrp, FinGenAbGroupHom}[]

  #Now, the big loop
  fun = (x, y) -> quo(x, y, false)[2]
  for (i, k) in enumerate(conds)
    @vprintln :AbExt 1 "Conductor: $k"
    if i % 10000 == 0
      @vprintln :AbExt 1 "Left: $(length(conds) - i)"
    end
    r, mr = Hecke.ray_class_groupQQ(O, k, !only_real, gtype[end])
    if !has_quotient(r, gtype)
      continue
    end
    ls = subgroups(r, quotype = gtype, fun = fun)
    for s in ls
      C = ray_class_field(mr, s)
      if Hecke._is_conductor_minQQ(C, n)
        @vprintln :AbExt 1 "New Field"
        push!(fields, C)
      end
    end
  end
  return fields
end

function abelian_extensions(gtype::Vector{Int}, conds::Vector{Int}, absolute_discriminant_bound::ZZRingElem; only_real::Bool = false)
  K = rationals_as_number_field()[1]
  O = maximal_order(K)
  gtype = map(Int, snf(abelian_group(gtype))[1].snf)
  n = prod(gtype)

  #Getting conductors
  @vprintln :AbExt 1 "Number of conductors: $(length(conds))"
  fields = ClassField{MapRayClassGrp, FinGenAbGroupHom}[]

  #Now, the big loop
  fun = (x, y) -> quo(x, y, false)[2]
  for (i, k) in enumerate(conds)
    @vprintln :AbExt 1 "Conductor: $k"
    if i % 10000 == 0
      @vprintln :AbExt 1 "Left: $(length(conds) - i)"
    end
    r, mr = Hecke.ray_class_groupQQ(O, k, !only_real, gtype[end])
    if !has_quotient(r, gtype)
      continue
    end
    ls = subgroups(r, quotype = gtype, fun = fun)
    for s in ls
      C = ray_class_field(mr, s)
      if Hecke._is_conductor_minQQ(C, n) && Hecke.discriminant_conductorQQ(O, C, k, absolute_discriminant_bound)
        @vprintln :AbExt 1 "New Field"
        push!(fields, C)
      end
    end
  end
  return fields
end

function abelian_extensions(O::AbsSimpleNumFieldOrder, gtype::Vector{Int}, absolute_discriminant_bound::ZZRingElem; only_real::Bool = false, only_complex::Bool = false, tame::Bool = false)
  K = nf(O)
  @assert degree(K)==1
  gtype = map(Int, snf(abelian_group(gtype))[1].snf)
  n = prod(gtype)
  real = only_real

  expo = lcm(gtype)

  #Getting conductors
  l_conductors = conductorsQQ(O, gtype, absolute_discriminant_bound, tame)
  @vprintln :AbExt 1 "Number of conductors: $(length(l_conductors))"
  fields = ClassField{MapRayClassGrp, FinGenAbGroupHom}[]

  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    @vprintln :AbExt 1 "Conductor: $k"
    @vprintln :AbExt 1 "Left: $(length(l_conductors) - i)"
    r, mr = Hecke.ray_class_groupQQ(O, k, !real, expo)
    if !has_quotient(r, gtype)
      continue
    end
    ls = subgroups(r,quotype = gtype, fun = (x, y) -> quo(x, y, false)[2])
    for s in ls
      C = ray_class_field(mr, s)
      if Hecke._is_conductor_minQQ(C,n) && Hecke.discriminant_conductorQQ(O,C,k,absolute_discriminant_bound)
        if only_complex
          rC, sC = signature(C)
          if !iszero(rC)
            continue
          end
        end
        @vprintln :AbExt 1 "New Field"
        push!(fields, C)
      end
    end
  end
  return fields
end


@doc doc"""
    abelian_normal_extension(K::AbsSimpleNumField, gtype::Vector{Int},
                             bound::ZZRingElem;
                             only_real = false,
                             only_complex = false,
                             tame = false)
                                                          -> Vector{ClassField}

Returns all abelian extension $L/K$ with Galois group with abelian invariants
`gtype`, such that $L/\mathbf{Q}$ is normal and the absolute discriminant of
$L$ is bounded by `bound`.

- `only_real = true`: Only totally real fields will be computed.
- `only_complex = true`: Only totally complex fields will be computed.
- `tame = true`: Only tame fields will be computed.

Note that fields are returned as class fields of $L$, which can be transformed
into number fields by calling `number_field`.
"""
function abelian_normal_extensions(K::AbsSimpleNumField, gtype::Vector{Int}, absolute_discriminant_bound::ZZRingElem; only_real::Bool = false, only_complex::Bool = false, tame::Bool = false, absolute_galois_group::Tuple{Int, Int} = (0, 0))

  @assert !(only_real && only_complex)
  O = maximal_order(K)
  d = degree(K)
  if d == 1
    return abelian_extensions(O, gtype, absolute_discriminant_bound, only_real = only_real, tame = tame)
  end
  gtype = map(Int, snf(abelian_group(gtype))[1].snf)
  n = prod(gtype)
  inf_plc = InfPlc[]

  fields = ClassField{MapRayClassGrp, FinGenAbGroupHom}[]
  bound = div(absolute_discriminant_bound, abs(discriminant(O))^n)

  if iszero(bound)
    return fields
  end

  if iseven(n) && !only_real
    inf_plc = real_places(K)
  end

  Aut = automorphism_list(K)
  @assert length(Aut) == d #The field is normal over Q
  gs = Hecke.small_generating_set(Aut)

  expo = lcm(gtype)
  Cl, mCl = class_group(O)
  cgrp = !is_coprime(n, order(Cl))
  allow_cache!(mCl)

  #Getting conductors
  l_conductors = conductors(O, gtype, bound, tame)
  @vprintln :AbExt 1 "Number of conductors: $(length(l_conductors))"

  ctx = rayclassgrp_ctx(O, expo)
  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    @vprintln :AbExt 1 "Conductor: $k"
    @vprintln :AbExt 1 "Left: $(length(l_conductors) - i)"
    r, mr = ray_class_group_quo(O, k[1], k[2], inf_plc, ctx)
    if !has_quotient(r, gtype)
      continue
    end
    act = induce_action(mr, gs)
    ls = stable_subgroups_for_abexts(r, act, gtype)
    for s in ls
      s::FinGenAbGroupHom
      @hassert :AbExt 1 order(codomain(s)) == n
      C = ray_class_field(mr, s)::ClassField{MapRayClassGrp, FinGenAbGroupHom}
      if _is_conductor_min_normal(C) && discriminant_conductor(C, bound)
        if only_complex
          rC, sC = signature(C)
          if !iszero(rC)
            continue
          end
        end
        if absolute_galois_group != (0, 0)
          autabs = absolute_automorphism_group(C, gs)
          G = generic_group(autabs, *)[1]
          id_G = find_small_group(G)
          if id_G == absolute_galois_group
            @vprintln :AbExt 1 "New Field"
            push!(fields, C)
          end
        else
          @vprintln :AbExt 1 "New Field"
          push!(fields, C)
        end
      end
    end
  end
  return fields
end

################################################################################
#
#  Abelian extensions of arbitrary fields
#
################################################################################

function abelian_extensions(K::AbsSimpleNumField, gtype::Vector{Int},
                            absolute_discriminant_bound::ZZRingElem;
                            absolutely_distinct::Bool = false,
                            ramified_at_inf_plc::Tuple{Bool, Vector{<: InfPlc}} = (false, InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}[]),
                            only_tame::Bool = false,
                            signatures::Vector{Tuple{Int, Int}} = Tuple{Int, Int}[],
                            conductors = nothing)

  if length(signatures) == 0
    return _abelian_extensions(K, gtype, absolute_discriminant_bound,
                               absolutely_distinct = absolutely_distinct,
                               ramified_at_inf_plc = ramified_at_inf_plc,
                               only_tame = only_tame,
                               conductors = conductors)
  else
    if ramified_at_inf_plc[1]
      error("Cannot specify ramified place and target signatures simultaneously")
    end
    n = prod(gtype)
    # this is the relative degree
    r, s = signature(K)
    rlp = real_places(K)
    @assert r == length(rlp)
    onetor = collect(1:r)
    fields = ClassField{MapRayClassGrp, FinGenAbGroupHom}[]
    for (R, S) in signatures
      if mod(r * n - R, n) != 0
        continue
      end
      # this many real places have to ramifiy
      # see Cohen, Advanced topics, Proposition 3.5.8
      num_ramified = div(r * n - R, n)
      # Sanity check for complex places
      if S != (s + num_ramified//2)*n
        continue
      end
      for s in subsets(onetor, num_ramified)
        rlp_ramify = rlp[s]
        more_fields =  _abelian_extensions(K, gtype, absolute_discriminant_bound,
                               absolutely_distinct = absolutely_distinct,
                               ramified_at_inf_plc = (true, rlp_ramify),
                               only_tame = only_tame,
                               conductors = conductors)
        for L in more_fields
          @assert signature(L) == (R, S)
        end
        append!(fields, more_fields)
      end
    end
    return fields
  end
end

function _abelian_extensions(K::AbsSimpleNumField, gtype::Vector{Int},
                            absolute_discriminant_bound::ZZRingElem;
                            absolutely_distinct::Bool = false,
                            ramified_at_inf_plc::Tuple{Bool, Vector{<: InfPlc}} = (false, InfPlc[]),
                            only_tame::Bool = false,
                            conductors = nothing)

  # quick check
  OK = lll(maximal_order(K))
  gtype = map(Int, snf(abelian_group(gtype))[1].snf)
  n = prod(gtype)
  fields = ClassField{MapRayClassGrp, FinGenAbGroupHom}[]
  bound = div(absolute_discriminant_bound, abs(discriminant(OK))^n)
  if iszero(bound)
    return fields
  end

  # TODO: better preprocessing of custom conductors
  # what to allow? lists of ideals, lists of factorizations, ...
  #
  # #Getting conductors first, because we also extrat the maximal order
  if conductors === nothing
    @vprintln :AbExt 1 "Computing conductors"
    l_conductors = conductors_generic(K, gtype, absolute_discriminant_bound, only_tame = only_tame)
  else
    @vprintln :AbExt 1 "Conductors provided"
    if conductors isa Vector{<:Dict}
      l_conductors = conductors
    else
      @assert conductors isa Vector{ideal_type(OK)}
      l_conductors = [factor(I) for I in conductors]
    end
    if !isempty(first(l_conductors))
      OK = order(first(keys(first(l_conductors))))
    end
  end

  inf_plc = real_places(K)
  if ramified_at_inf_plc[1]
    inf_plc = ramified_at_inf_plc[2]
  end

  expo = gtype[end]
  auts = automorphism_list(K)
  gens_auts = small_generating_set(auts)
  if isone(length(auts))
    absolutely_distinct = false
  end
  Cl, mCl = class_group(OK)
  cgrp = !is_coprime(n, order(Cl))
  allow_cache!(mCl)


  if absolutely_distinct
    l_conductors = _sieve_conjugates(auts, l_conductors)
  end
  @vprintln :AbExt 1 "Number of conductors: $(length(l_conductors))"

  ctx = rayclassgrp_ctx(OK, expo)
  fsub = (x, y) -> quo(x, y, false)[2]
  fsub_distinct = (x, y) -> (quo(x, y, false)[2], sub(x, y, false)[2])
  #Now, the big loop
  for (i, k) in enumerate(l_conductors)
    if i % 10000 == 0
      @vprintln :AbExt 1 "Conductors left: $(length(l_conductors) - i) (fields found: $(length(fields)))"
    end
    r, mr = ray_class_group_quo(OK, k, inf_plc, ctx)
    if !has_quotient(r, gtype)
      continue
    end
    if absolutely_distinct && _isstable(gens_auts, k)
      act = induce_action(mr, gens_auts)
      full_action = closure(act, *)
      ls_with_emb = subgroups(r, quotype = gtype, fun = fsub_distinct)
      _closure = Vector{FinGenAbGroupHom}()
      ls = Vector{FinGenAbGroupHom}()
      for (proj, emb) in ls_with_emb
        found = false
        for j = 1:length(_closure)
          if _issubset(emb, _closure[j])
            found = true
            break
          end
        end
        if !found
          push!(ls, proj)
          for mp in full_action
            push!(_closure, emb*mp)
          end
        end
      end
    else
      ls1 = subgroups(r, quotype = gtype, fun = fsub)
      ls = collect(ls1)::Vector{FinGenAbGroupHom}
    end
    new_fields = ClassField{MapRayClassGrp, FinGenAbGroupHom}[]
    for s in ls
      @hassert :AbExt 1 order(codomain(s)) == n
      C = ray_class_field(mr, s)::ClassField{MapRayClassGrp, FinGenAbGroupHom}
      cC = conductor(C)
      if ramified_at_inf_plc[1]
        if Set(cC[2]) != Set(ramified_at_inf_plc[2])
          continue
        end
      end
      if cC[1] == mr.defining_modulus[1] && norm(discriminant(C)) <= bound
        push!(new_fields, C)
      end
    end
    append!(fields, new_fields)
  end
  return fields
end



function _isstable(auts::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, d::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int})
  if isempty(d)
    return true
  end
  OK = order(first(keys(d)))
  #CAREFUL: BASE FIELD NOT NORMAL.
  #NEED TO ACT WITH automorphisms
  primes = Set{ZZRingElem}(minimum(x, copy = false) for x in keys(d))
  for p in primes
    lP = prime_decomposition(OK, p)
    prime_ideals = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[x[1] for x in lP]
    perms = [induce_action(prime_ideals, f) for f in auts]
    orbs = orbits(perms)
    for i = 1:length(orbs)
      P = prime_ideals[orbs[i][1]]
      if !haskey(d, P)
        for j = 2:length(orbs[i])
          if haskey(d, prime_ideals[orbs[i][j]])
            return false
          end
        end
      else
        e = d[P]
        for j = 2:length(orbs[i])
          if !haskey(d, prime_ideals[orbs[i][j]]) || d[prime_ideals[orbs[i][j]]] != e
            return false
          end
        end
      end
    end
  end
  return true
end

function _image(cache, auts, I, i)
  pos = Base.ht_keyindex(cache[i], I)
  if pos != -1
    return cache[i].vals[pos]
  end
  img = auts[i](I)
  cache[i][I] = img
  return img
end

function _sieve_conjugates(auts::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, conds::Vector{Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}})
  if isone(length(auts))
    return conds
  end
  closure = Set{Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}}()
  reps = Vector{Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}}()
  cache = Vector{Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}(undef, length(auts))
  for i = 1:length(cache)
    cache[i] = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  end
  for j = 1:length(conds)
    if conds[j] in closure
      continue
    end
    push!(reps, conds[j])
    for i = 1:length(auts)
      push!(closure, _induce_image(auts, i, conds[j], cache))
    end
  end
  return reps
end

function _induce_image(auts::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, i::Int, cond::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}, cache::Vector{Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}})
  res = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
  for (k, v) in cond
    res[_image(cache, auts, k, i)] = v
  end
  return res
end



################################################################################
#
#  Valuation bounds for discriminants
#
################################################################################

function valuation_bound_discriminant(n::Int, p::IntegerUnion)
  # First compute the p-adic expansion of n
  S = Vector{typeof(p)}()
	q = typeof(p)(n)
  q, r = divrem(q, p)
  push!(S, r)
  while q >= p
    q, r = divrem(q, p)
    push!(S, r)
  end

	if !iszero(q)
		push!(S, q)
	end

	@assert sum(S[i + 1] * p^i for i in 0:length(S)-1) == n

	b = zero(typeof(p))

	for i in 0:length(S) - 1
		b = b + S[i + 1] * (i + 1) * p^i
		if !iszero(S[i + 1])
			b = b - 1
		end
	end

  return b
end

###########################################################################
#
#  Some useful functions
#
###########################################################################

#This function gets a quotient of the ray class group and the action on
# the ray class group
# In output, we get the quotient group as a ZpnGModule

function _action_on_quo(mq::FinGenAbGroupHom, act::Vector{FinGenAbGroupHom})

  q=mq.header.codomain
  S,mS=snf(q)
  n=Int(S.snf[end])
  R=residue_field(FlintZZ, n, cached=false)[1]
  quo_action=Vector{zzModMatrix}(undef, length(act))
  for s=1:length(act)
    quo_action[s]= change_base_ring(mS.map*act[i].map*mS.imap, R)
  end
  return ZpnGModule(S, quo_action)

end

###############################################################################
#
#  Quadratic Extensions of Q
#
###############################################################################

function quadratic_fields(bound::Int; tame::Bool=false, real::Bool=false, complex::Bool=false, with_autos::Val{unused}=Val(false)) where unused

  @assert !(real && complex)
  Qx,x=polynomial_ring(FlintQQ, "x")
  sqf=squarefree_up_to(bound)
  if real
    deleteat!(sqf,1)
  elseif complex
    sqf=Int[-i for i in sqf]
  else
    sqf= vcat(sqf[2:end], Int[-i for i in sqf])
  end
  if tame
    filter!( x -> mod(x,4)==1, sqf)
    return ( number_field(x^2-x+divexact(1-i,4), cached=false, check = false)[1] for i in sqf)
  end
  final_list=Int[]
  for i=1:length(sqf)
    if abs(sqf[i]*4)< bound
      @views push!(final_list,sqf[i])
      continue
    end
    if mod(sqf[i],4)==1
      @views push!(final_list,sqf[i])
    end
  end
  return ( mod(i,4)!=1 ? number_field(x^2-i, cached=false, check = false)[1] : number_field(x^2-x+divexact(1-i,4), cached = false, check = false)[1] for i in final_list)

end

function _quad_ext(bound::Int, only_real::Bool = false; unramified_outside::Vector{ZZRingElem} = ZZRingElem[])

  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  K = number_field(x-1, cached = false, check = false)[1]
  sqf = squarefree_up_to(bound, prime_base = unramified_outside)
  final_list = Int[]
  for i=2:length(sqf)
    if abs(sqf[i]*4)< bound
      @views push!(final_list, sqf[i])
      continue
    end
    if mod(sqf[i], 4) == 1
      @views push!(final_list, sqf[i])
    end
  end
  if !only_real
    for i = 1:length(sqf)
      if abs(sqf[i]*4)< bound
        @views push!(final_list, -sqf[i])
        continue
      end
      if mod(sqf[i], 4) == 3
        @views push!(final_list, -sqf[i])
      end
    end
  end
  fields_list = Vector{Tuple{AbsSimpleNumField, Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}}}(undef, length(final_list))
  for i = 1:length(final_list)
    if mod(final_list[i],4) != 1
      cp = Vector{ZZRingElem}(undef, 3)
      cp[1] = -final_list[i]
      cp[2] = 0
      cp[3] = 1
      L, gL = number_field(Qx(cp), cached=false, check = false)
      auts = morphism_type(AbsSimpleNumField, AbsSimpleNumField)[hom(L, L, -gL, check = false)]
      emb = morphism_type(AbsSimpleNumField, AbsSimpleNumField)[hom(K, L, one(L), check = false)]
      fields_list[i] = (L, auts, emb)
    else
      cp = Vector{ZZRingElem}(undef, 3)
      cp[1] = divexact(1-final_list[i], 4)
      cp[2] = -1
      cp[3] = 1
      L, gL = number_field(Qx(cp), cached=false, check = false)
      auts = morphism_type(AbsSimpleNumField, AbsSimpleNumField)[hom(L, L, 1-gL, check = false)]
      emb = morphism_type(AbsSimpleNumField, AbsSimpleNumField)[hom(K, L, one(L), check = false)]
      fields_list[i] = (L, auts, emb)
    end
  end
  return fields_list

end

###############################################################################
#
#  C2 x C2 extensions of Q
#
###############################################################################

function C22_extensions(bound::Int)


  Qx, x=polynomial_ring(FlintZZ, "x")
  K, _=number_field(x-1, cached = false)
  Kx,x=polynomial_ring(K,"x", cached=false)
  b1=ceil(Int,Base.sqrt(bound))
  n=2*b1+1
  pairs = _find_pairs(bound)
  return (_ext(Kx,x,i,j) for (i, j) in pairs)

end

function _ext(Ox,x,i,j)

  y=mod(i,4)
  pol1 = x^2
  if y != 1
    pol1 = x^2-i
  else
    pol1 = x^2-x+divexact(1-i,4)
  end
  y=mod(j,4)
  pol2=Ox(1)
  if y!=1
    pol2=x^2-j
  else
    pol2=x^2-x+divexact(1-j,4)
  end
  return number_field([pol1,pol2], cached = false, check = false)

end


function _C22_exts_abexts(bound::Int, only_real::Bool = false; unramified_outside::Vector{ZZRingElem} = ZZRingElem[])
  Qx, x = polynomial_ring(FlintZZ, "x", cached = false)
  pairs = _find_pairs(bound, only_real, unramified_outside = unramified_outside)
  return (_ext_with_autos(Qx, x, i, j) for (i, j) in pairs)
end

function _ext_with_autos(Qx, x, i::Int, j::Int)
  first = i
  second = j
  g = gcd(i, j)
  if g != 1
    third = divexact(i*j, g^2)
    if gcd(first, third) == 1
      second = third
    elseif gcd(second, third) == 1
      first = third
    end
  end
  y1 = mod(first, 4)
  cp1 = Vector{ZZRingElem}(undef, 3)
  cp1[3] = ZZRingElem(1)
  if y1 != 1
    cp1[1] = ZZRingElem(-first)
    cp1[2] = ZZRingElem(0)
  else
    cp1[1] = ZZRingElem(divexact(1-first,4))
    cp1[2] = ZZRingElem(-1)
  end
  y2 = mod(second, 4)
  cp2 = Vector{ZZRingElem}(undef, 3)
  cp2[3] = ZZRingElem(1)
  if y2 != 1
    cp2[1] = ZZRingElem(-second)
    cp2[2] = ZZRingElem(0)
  else
    cp2[1] = ZZRingElem(divexact(1-second, 4))
    cp2[2] = ZZRingElem(-1)
  end
  return Qx(cp1), Qx(cp2)
end

function __get_term(a::QQMPolyRingElem, exps::Vector{UInt})
   z = QQFieldElem()
   ccall((:fmpq_mpoly_get_coeff_fmpq_ui, libflint), Nothing,
         (Ref{QQFieldElem}, Ref{QQMPolyRingElem}, Ptr{UInt}, Ref{QQMPolyRing}),
         z, a, exps, parent(a))
   return z
end

function _C22_with_max_ord(l)
  list = Vector{Tuple{AbsSimpleNumField, Vector{morphism_type(AbsSimpleNumField, AbsSimpleNumField)}, Vector{morphism_type(AbsSimpleNumField, AbsSimpleNumField)}}}()
  Qx, x = polynomial_ring(FlintQQ, "x", cached = false)
  K = number_field(x-1, cached = false)[1]
  @vprintln :AbExt 1 "Constructing the C2xC2 extension: $(length(l))"
  for (i, (p1, p2)) in enumerate(l)
    if i % 10000 == 0
      @vprintln :AbExt 1 "Left: $(length(l) - i)"
    end
    Kns, g = number_field(ZZPolyRingElem[p1, p2], check = false, cached = false)
    S, mS = simple_extension(Kns, check = false, cached = false, simplified = true)
    Hecke._assure_has_inverse_data(mS)
    gen1 = mS\(g[1])
    gen2 = mS\(g[2])
    d1 = discriminant(p1)
    d2 = discriminant(p2)
    cf = gcd(d1, d2)
    if isone(cf)
      B = Vector{AbsSimpleNumFieldElem}(undef, 4)
      B[1] = S(1)
      B[2] = mS\(g[1])
      B[3] = mS\(g[2])
      B[4] = B[2] * B[3]
      M = basis_matrix(B, FakeFmpqMat)
      hnf_modular_eldiv!(M.num, M.den, :lowerleft)
      O = AbsNumFieldOrder(S, FakeFmpqMat(M.num, M.den))
      O.disc = d1^2*d2^2
      d3 = numerator(discriminant(S))
      if d3 < 0
        O.disc = -O.disc
      end
      O.index = divexact(d3, O.disc)
      O.is_maximal = 1
      set_attribute!(S, :maximal_order => O)
    else
      maximal_order(S)
    end
    auts = small_generating_set(automorphism_list(S, is_abelian = true, copy = false))
    push!(list, (S, auts, morphism_type(AbsSimpleNumField, AbsSimpleNumField)[hom(K, S, S(1), check = false)]))
  end
  return list
end

function _disc(a::Int, b::Int, c::Int, bound::Int)
  a1 = mod(a, 4)
  b1 = mod(b, 4)
  if a1 == 1 && b1 == 1
    return widemul(a, b) * c <= bound
  end
  c1 = mod(c, 4)
  if a1 == 1 || b1 == 1 || c1 == 1
    return 16*widemul(a, b)*c <= bound
  else
    return 64*widemul(a, b)*c <= bound
  end
end

function _pairs_totally_real(pairs, ls, bound)
  #b1=floor(Int, Base.sqrt(bound))
  b1 = isqrt(bound)
  # We look for Q(sqrt{a},sqrt{b})
  # Remove all with a = 1
  pairs[1, :] .= false
  # Remove all with b = 1
  pairs[:, 1] .= false
  # Because of symmetry, look at only one half of the pairs
  for j = 2:length(ls)
    @inbounds pairs[j:end, j] .= false
  end
  @vprintln :AbExt 1 "Number of quadratic discriminants to check: $(length(ls))"
  for j = 2:length(ls)
    if j % 10000 == 0
      @vprintln :AbExt 1 "Left: $(length(ls) - j)"
    end
    second = ls[j]
    for i = 2:j-1
      if (@inbounds pairs[i, j])
        first = @inbounds ls[i]
        g = gcd(first, second)
        if isone(g)
          third = first*second
        else
          third = divexact(first*second, g^2)
        end
        if abs(third) > b1
          @inbounds pairs[i, j] = false
          continue
        end
        k = searchsortedfirst(ls, third)
        if i < k
          @inbounds pairs[i, k] = false
        else
          @inbounds pairs[k, i] = false
        end
        if j < k
          @inbounds pairs[j, k] = false
        else
          @inbounds pairs[k, j] = false
        end
        if !_disc(first, second, third, bound)
          @inbounds pairs[i, j] = false
        end
      end
    end
  end
  it = findall(pairs)
  totally_real_exts = Vector{Tuple{Int, Int}}(undef, length(it))
  ind = 1
  for I in it
    totally_real_exts[ind] = (ls[I[1]], ls[I[2]])
    ind += 1
  end
  return totally_real_exts

end


function _find_pairs(bound::Int, only_real::Bool = false; unramified_outside::Vector{ZZRingElem} = ZZRingElem[] )
  #first, we need the squarefree numbers
  #b1=ceil(Int, Base.sqrt(bound))
  b1 = isqrt(bound)
  ls = squarefree_up_to(b1, prime_base = unramified_outside)
  #The first step is to enumerate all the totally real extensions.
  pairs = trues(length(ls), length(ls))
  real_exts = _pairs_totally_real(pairs, ls, bound)
  if only_real
    return real_exts
  end
  ls1 = -ls
  #Now, all the others.
  pairs[1:length(ls), 2:length(ls)] .= true
  @vprintln :AbExt 1 "Number of quadratic discriminants to check: $(length(ls))"
  for j = 2:length(ls)
    if j % 10000 == 0
      @vprintln :AbExt 1 "Left: $(length(ls) - j)"
    end
    second = ls[j]
    for i = 1:length(ls)
      if pairs[i, j]
        first = ls1[i]
        g = gcd(first, second)
        if isone(g)
          third = first*second
        else
          third = divexact(first*second, g^2)
        end
        abt = -third
        if abt > b1
          pairs[i, j] = false
          continue
        end
        k = searchsortedfirst(ls, abt)
        pairs[k, j] = false
        if !_disc(first, second, third, bound)
          pairs[i, j] = false
        end
      end
    end
  end
  it = findall(pairs)
  ind = 1
  res = Vector{Tuple{Int, Int}}(undef, length(it))
  for I in it
    res[ind] = (ls1[I[1]], ls[I[2]])
    ind += 1
  end
  return vcat(res, real_exts)
end



function _from_relative_to_abs(L::RelNonSimpleNumField{T}, auts::Vector{<: NumFieldHom{RelNonSimpleNumField{T}, RelNonSimpleNumField{T}}}) where T

  @vtime :AbExt 2 Ks, mKs = simplified_absolute_field(L, cached = false)
  #Now, we have to construct the maximal order of this field.
  #I am computing the preimages of mKs by hand, by inverting the matrix.
  #Now, the automorphisms.
  autos=Vector{morphism_type(AbsSimpleNumField, AbsSimpleNumField)}(undef, length(auts))
  el = mKs(gen(Ks))
  for i = 1:length(auts)
    y = mKs\(auts[i](el))
    autos[i] = hom(Ks, Ks, y, check = false)
  end
  set_automorphisms(Ks, closure(autos, degree(Ks)))
  @vprintln :AbExt 2 "Finished"
  return Ks, autos
end


#######################################################################################
#
#  relative discriminant for abelian extension function
#
#######################################################################################

function discriminant_conductor(C::ClassField{MapClassGrp, FinGenAbGroupHom}, bound::ZZRingElem; lwp::Dict{Tuple{Int, Int}, Vector{FinGenAbGroupElem}} = Dict{Tuple{Int, Int}, Vector{FinGenAbGroupElem}}())
  return true
end

function discriminant_conductor(C::ClassField, bound::ZZRingElem; lwp::Dict{Tuple{Int, Int}, Vector{FinGenAbGroupElem}} = Dict{Tuple{Int, Int}, Vector{FinGenAbGroupElem}}())

  mr = C.rayclassgroupmap
  O = base_ring(C)
  n = degree(C)
  e = Int(exponent(C))
  lp = mr.fact_mod
  abs_disc = factor(discriminant(O)^n).fac
  if isempty(lp)
    C.absolute_discriminant=abs_disc
    return true
  end
  K = nf(O)
  d = degree(K)
  discr = ZZRingElem(1)
  mp = pseudo_inv(C.quotientmap) * mr
  R = domain(mp)
  a = minimum(defining_modulus(mr)[1])
  primes_done = ZZRingElem[]
  if is_prime(n)
    for (p, v) in lp
      if minimum(p, copy = false) in primes_done
        continue
      end
      push!(primes_done, minimum(p, copy = false))
      ap = n*v-v
      qw = divexact(d, p.splitting_type[1])*ap
      mul!(discr, discr, ZZRingElem(p.minimum)^qw)
      if discr > bound
        @vprintln :AbExt 2 "too large"
        return false
      else
        if haskey(abs_disc, p.minimum)
          abs_disc[p.minimum] += qw
        else
          abs_disc[p.minimum] = qw
        end
      end
    end
    return true
  end

  powers = mr.powers
  groups_and_maps = mr.groups_and_maps

  for i = 1:length(powers)
    p, q = powers[i]
    if p.minimum in primes_done
      continue
    end
    push!(primes_done, p.minimum)
    if p == q
      ap = n
      tmg = groups_and_maps[i][2].tame[p]
      el = C.quotientmap(tmg.disc_log)
      Q, mQ = quo(R, FinGenAbGroupElem[el], false)
      ap -= order(Q)
      qw = divexact(d, p.splitting_type[1])*ap
      mul!(discr, discr, ZZRingElem(p.minimum)^qw)
      if discr > bound
        @vprintln :AbExt 2 "too large"
        return false
      else
        if haskey(abs_disc, p.minimum)
          abs_disc[p.minimum] += qw
        else
          abs_disc[p.minimum] = qw
        end
      end
      continue
    end
    np = p.minimum^divexact(d, p.splitting_type[1])
    ap = n*lp[p]
    s = lp[p]
    @hassert :AbExt 1 s>=2
    els=FinGenAbGroupElem[]
    for k=2:lp[p]
      s = s-1
      pk = p^s
      pv = pk*p
      if haskey(lwp, (Int(p.minimum), s+1))
        gens = lwp[(Int(p.minimum), s+1)]
      else
        gens_els = _1pluspk_1pluspk1(O, p, pk, pv, powers, a, e)
        gens = Vector{FinGenAbGroupElem}(undef, length(gens_els))
        for i = 1:length(gens)
          gens[i] = mr\(ideal(O, gens_els[i]))
        end
        lwp[(Int(p.minimum), s+1)] = gens
      end
      for i = 1:length(gens)
        push!(els, C.quotientmap(gens[i]))
      end
      o = order(quo(R, els, false)[1])
      ap -= o
      tentative_ap = ap - (lp[p] - k + 1)*o
      tentative_discr = discr * (np^tentative_ap)
      if tentative_discr > bound
        return false
      end
      @hassert :AbExt 1 ap>0
    end
    if haskey(groups_and_maps[i][2].tame, p)
      v = groups_and_maps[i][2].tame[p]
      push!(els, C.quotientmap(v.disc_log))
    end
    ap -= order(quo(R, els, false)[1])
    @hassert :AbExt 1 ap>0
    np1 = np^ap
    mul!(discr, discr, np1)
    if discr > bound
      @vprintln :AbExt 2 "too large"
      return false
    else
      if haskey(abs_disc, p.minimum)
        abs_disc[p.minimum] += ap*divexact(d, p.splitting_type[1])
      else
        abs_disc[p.minimum] = ap*divexact(d, p.splitting_type[1])
      end
    end
  end
  C.absolute_discriminant = abs_disc
  return true

end

#same function but for ray class groups over QQ

function discriminant_conductorQQ(O::AbsSimpleNumFieldOrder, C::ClassField, m::Int, bound::ZZRingElem)

  n = degree(C)
  discr=ZZRingElem(1)
  mp = pseudo_inv(C.quotientmap) * C.rayclassgroupmap
  G=domain(mp)

  cyc_prime= is_prime(n)==true

  lp=factor(m).fac
  abs_disc=Dict{ZZRingElem,Int}()

  R=residue_ring(FlintZZ, m, cached=false)[1]

  for (p,v) in lp
    if v==1
      ap=n
      if cyc_prime
        ap-=1
      else
        x=_unit_grp_residue_field_mod_n(Int(p),n)[1]
        s=divexact(m,Int(p))
        d,a,b=gcdx(s, Int(p))
        l=Int((R(x)*a*s+b*Int(p)).data)
        el=mp\ideal(O,l)
        q,mq=quo(G, FinGenAbGroupElem[el], false)
        ap-= order(q)
      end
      discr*=p^ap
      if discr>bound
        @vprintln :AbExt 2 "too large"
        return false
      else
        abs_disc[p]=ap
      end
    else
      ap=n*v
      pow=Int(p)^Int(v)
      el = R(1)
      if cyc_prime
        ap-=v
      else
        if isodd(p)
          s=divexact(m,pow)
          d,a,b=gcdx(pow,s)
          s1=R(1+p)^(p-1)
          el=G[1]
          if v==2
            el=mp\ideal(O,Int((b*s*R(s1)+a*pow).data))
            ap-=order(quo(G,FinGenAbGroupElem[el], false)[1])
          else
            for k=0:v-2
              el=mp\ideal(O,Int((b*s*R(s1)^(p^k)+a*pow).data))
              ap-=order(quo(G, FinGenAbGroupElem[el], false)[1])
              @hassert :AbExt 1 ap>0
            end
          end
          if gcd(n,p-1)==1
            ap-=order(quo(G, FinGenAbGroupElem[mp\(ideal(O,ZZRingElem((b*s*R(s1)+a*pow).data)))], false)[1])
          else
            x=_unit_grp_residue_field_mod_n(Int(p),n)[1]
            el1=mp\ideal(O,Int((R(x)*b*s+a*pow).data))
            ap-=order(quo(G, FinGenAbGroupElem[mp\(ideal(O,Int((b*s*R(s1)+a*pow).data))), el1], false)[1])
          end
        else
          s=divexact(m,2^v)
          d,a,b=gcdx(2^v,s)
          el=0*G[1]
          for k=v-3:-1:0
            el=mp\ideal(O,Int((R(5)^(2^k)*b*s+a*2^v).data))
            ap-=order(quo(G, FinGenAbGroupElem[el], false)[1])
          end
          el1=mp\ideal(O,Int((R(-1)*b*s+a*p^v).data))
          ap-=2*order(quo(G, FinGenAbGroupElem[el, el1], false)[1])
        end
      end
      discr*=p^ap
      if discr>bound
        @vprintln :AbExt 2 "too large"
        return false
      else
        abs_disc[p]=ap
      end
    end
  end
  C.absolute_discriminant=abs_disc
  return true
end

function discriminantQQ(O::AbsSimpleNumFieldOrder, C::ClassField, m::Int)

  discr=ZZRingElem(1)
  n = degree(C)
  mp = pseudo_inv(C.quotientmap) * C.rayclassgroupmap
  G = domain(mp)

  cyc_prime= is_prime(n)==true

  lp=factor(m).fac
  abs_disc=Dict{ZZRingElem,Int}()

  R=residue_ring(FlintZZ, m, cached=false)[1]

  for (p,v) in lp
    if v==1
      ap=n
      if cyc_prime
        ap-=1
      else
        x=_unit_grp_residue_field_mod_n(Int(p),n)[1]
        s=divexact(m,Int(p))
        d,a,b=gcdx(s, Int(p))
        l=Int((R(x)*a*s+b*Int(p)).data)
        el=mp\ideal(O,l)
        q,mq=quo(G, FinGenAbGroupElem[el], false)
        ap-= order(q)
      end
      discr*=p^ap
      abs_disc[p]=ap
    else
      ap=n*v
      pow=Int(p)^Int(v)
      el = R(1)
      if cyc_prime
        ap-=v
      else
        if isodd(p)
          s=divexact(m,pow)
          d,a,b=gcdx(pow,s)
          s1=R(1+p)^(p-1)
          el=G[1]
          if v==2
            el=mp\ideal(O,Int((b*s*R(s1)+a*pow).data))
            ap-=order(quo(G,FinGenAbGroupElem[el], false)[1])
          else
            for k=0:v-2
              el=mp\ideal(O,Int((b*s*R(s1)^(p^k)+a*pow).data))
              ap-=order(quo(G, FinGenAbGroupElem[el], false)[1])
              @hassert :AbExt 1 ap>0
            end
          end
          if gcd(n,p-1)==1
            ap-=order(quo(G, FinGenAbGroupElem[mp\(ideal(O,ZZRingElem((b*s*R(s1)+a*pow).data)))], false)[1])
          else
            x=_unit_grp_residue_field_mod_n(Int(p),n)[1]
            el1=mp\ideal(O,Int((R(x)*b*s+a*pow).data))
            ap-=order(quo(G, FinGenAbGroupElem[mp\(ideal(O,Int((b*s*R(s1)+a*pow).data))), el1], false)[1])
          end
        else
          s=divexact(m,2^v)
          d,a,b=gcdx(2^v,s)
          el=0*G[1]
          for k=v-3:-1:0
            el=mp\ideal(O,Int((R(5)^(2^k)*b*s+a*2^v).data))
            ap-=order(quo(G, FinGenAbGroupElem[el], false)[1])
          end
          el1=mp\ideal(O,Int((R(-1)*b*s+a*p^v).data))
          ap-=2*order(quo(G, FinGenAbGroupElem[el, el1], false)[1])
        end
      end
      discr*=p^ap
      abs_disc[p]=ap
    end
  end
  C.absolute_discriminant=abs_disc
  return discr
end

###############################################################################
#
#  conductor function for abelian extension function
#
###############################################################################

#  For this function, we assume the base field to be normal over Q and the conductor of the extension we are considering to be invariant
#  Checks if the defining modulus is the conductor of C

function _is_conductor_min_normal(C::ClassField{MapClassGrp, FinGenAbGroupHom}; lwp::Dict{Int, Vector{FinGenAbGroupElem}} = Dict{Int, Vector{FinGenAbGroupElem}}())
  return true
end

function _is_conductor_min_normal(C::Hecke.ClassField; lwp::Dict{Int, Vector{FinGenAbGroupElem}} = Dict{Int, Vector{FinGenAbGroupElem}}())
  mr = C.rayclassgroupmap
  lp = mr.fact_mod
  if isempty(lp)
    return true
  end

  a = minimum(defining_modulus(mr)[1])
  mp = pseudo_inv(C.quotientmap) * mr
  R = domain(mp)
  e = Int(exponent(C))
  O = base_ring(C)
  K = nf(O)
  lp = mr.fact_mod
  powers = mr.powers
  groups_and_maps = mr.groups_and_maps
  #first, tame part
  primes_done = ZZRingElem[]
  for i = 1:length(powers)
    p, q = powers[i]
    if p.minimum in primes_done
      continue
    end
    push!(primes_done, p.minimum)
    if p == q
      #The prime is tamely ramified
      v = groups_and_maps[i][2].tame[p]
      el = C.quotientmap(v.disc_log)
      if iszero(el)
        return false
      end
      continue
    end
    if haskey(lwp, Int(p.minimum))
      gens = lwp[Int(p.minimum)]
    else
      k = lp[p]-1
      pk = p^k
      pv = q
      gens_els = _1pluspk_1pluspk1(O, p, pk, pv, powers, a, e)
      gens = Vector{FinGenAbGroupElem}(undef, length(gens_els))
      for i = 1:length(gens)
        gens[i] = mr\(ideal(O, gens_els[i]))
      end
      lwp[Int(p.minimum)] = gens
    end
    iscond = false
    for i in 1:length(gens)
      if !iszero(C.quotientmap(gens[i]))
        iscond = true
        break
      end
    end
    if !iscond
      return false
    end
  end
  return true
end

#
#  Same function as above, but in the assumption that the map comes from a ray class group over QQ
#

function _is_conductor_minQQ(C::Hecke.ClassField, n::Int)

  mr = C.rayclassgroupmap
  mp = pseudo_inv(C.quotientmap) * mr
  m = defining_modulus(mr)[1]
  mm = Int(minimum(m))
  lp = factor(mm)

  O=order(m)
  K=nf(O)

  R=residue_ring(FlintZZ, mm, cached=false)[1]
  for (p,v) in lp.fac
    if isodd(p)
      if v==1
        x=_unit_grp_residue_field_mod_n(Int(p), n)[1]
        s=divexact(mm,Int(p))
        d,a,b=gcdx(s,Int(p))
        l=a*s*R(x)+p*b
        if iszero(mp\(ideal(O,Int(l.data))))
          return false
        end
      else
        s=divexact(mm,p^v)
        d,a,b=gcdx(s,p^v)
        x=a*s*R(1+p)^((p-1)*p^(v-2))+p^v*b
        if iszero(mp\(ideal(O,Int(x.data))))
          return false
        end
      end
    else
      if v==1
        return false
      end
      if v==2
        s=divexact(mm,4)
        d,a,b=gcdx(s,4)
        l=a*s*R(-1)+4*b
        if iszero(mp\(ideal(O,Int(l.data))))
          return false
        end
      else
        s=divexact(mm,2^v)
        d,a,b=gcdx(s, 2^v)
        l=a*s*R(5)^(2^(v-3))+2^v*b
        if iszero(mp\(ideal(O,Int(l.data))))
          return false
        end
      end
    end
  end
  return true

end


#Returns the cyclic extension of prime degree i with minimal discriminant
function minimal_prime_cyclic_extension(i::Int)
  k = 2
  while !is_prime(k*i+1)
    k +=1
  end
  K, a = cyclotomic_field(k*i+1)
  auts = small_generating_set(automorphism_list(K))
  auts[1] = auts[1]^i
  g = auts[1]
  el = g(a)
  for i = 2:k
    g *= auts[1]
    el += g(a)
  end
  f = minpoly(el)
  L = number_field(f, check = false, cached = false)[1]
  set_attribute!(L, :is_abelian => true)
  return simplify(L, cached = false)[1]
end
