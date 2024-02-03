function _add_relations_from_subfield(mL::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}; use_aut = true, redo = false, bound::Int = -1)
  L = codomain(mL)
  K = domain(mL)
  OK = lll(maximal_order(L))
  c = create_ctx(OK, use_aut = use_aut, redo = redo, bound = bound)
  U = UnitGrpCtx{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(OK)
  set_attribute!(OK, :UnitGrpCtx => U)
  set_attribute!(OK, :ClassGrpCtx => c)

  lp = Set{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  for p in c.FB.ideals
    push!(lp, intersect_prime(mL, p))
  end
  lp1 = collect(lp)

  vals_subfield = val_from_subfield(c.FB, mL, lp1)
  cache_mL = Dict{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}()
  @vprintln :ClassGroup 1 "Computing S-units of totally real subfield"
  S, mS = Hecke.sunit_group_fac_elem(lp1)
  @vprintln :ClassGroup 1 "Embedding S-units of totally real subfield"
  for i = 1:ngens(S)
    @vprintln :ClassGroup 1 "Embedding S-units $i/$(ngens(S))"
    sup = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem}((mS.idl[i], v) for (i, v) in mS.valuations[i])
    u = compact_presentation(mS(S[i]), 2, decom = sup)
    if iszero(mS.valuations[i])
      if is_torsion_unit(u)[1]
        continue
      end
      add_unit!(U, u)
    else
      img_u = FacElem(Dict{AbsSimpleNumFieldElem, ZZRingElem}((_embed(mL, cache_mL, x), v) for (x,v) = u.fac if !iszero(v)))
      valofnewelement = mS.valuations[i] * vals_subfield
      Hecke.class_group_add_relation(c, u, valofnewelement, add_orbit = false, always = false)
    end
  end
  c.finished = false
  d = root(abs(discriminant(OK)), 2)
  @show c.expect = class_group_expected(c, 100)
  class_group_via_lll(c)
  return nothing
end

function _embed(mL, D, a)
  b = get(D, a, nothing)
  if b === nothing
    c = mL(a)
    D[a] = c
    return c
  else
     return b
  end
end

function val_from_subfield(FB, mk, s)
  S = FB.ideals
  ZK = order(S[1])

  z = zero_matrix(SMat, FlintZZ, 0, length(S))

  zk = order(s[1])

  @assert mod(degree(ZK), degree(zk)) == 0
  reldeg = divexact(degree(ZK), degree(zk))

  for l in 1:length(s)
    v = Tuple{Int, ZZRingElem}[]
    P = s[l]
    genofsl = elem_in_nf(mk(P.gen_two.elem_in_nf))
    pmin = minimum(P, copy = false)
    # Compute the number of ideals
    # Assume that L/K and L/Q are normal
    rele = divexact(ramification_index((FB.fb[pmin].lp)[1][2]), ramification_index(P))
    relf = divexact(degree((FB.fb[pmin].lp)[1][2]), degree(P))
    @assert mod(reldeg, rele * relf) == 0
    numb_ideal = divexact(reldeg, rele * relf)
    found = 0
    for k in 1:length(S)
      Q = S[k]
      if minimum(Q, copy = false) == pmin
        if genofsl in Q
          found += 1
          @assert mod(ramification_index(Q), ramification_index(s[l])) == 0
          push!(v, (k, divexact(ramification_index(Q), ramification_index(s[l]))))
        end
      end
    end
    sort!(v, by = x -> x[1])
    push!(z, sparse_row(FlintZZ, v))
  end
  return z
end

function class_group_cm(OK::AbsSimpleNumFieldOrder; redo = false, use_aut = true, bound::Int = Int(ceil((log(abs(discriminant(OK)))^2)*0.3)))
  K = nf(OK)
  O = lll(OK)
  fl, conj = is_cm_field(nf(O))
  L, mL = fixed_field1(K, [conj])
  _add_relations_from_subfield(mL, use_aut = use_aut, redo = redo, bound = bound)
  c, U, b = _class_unit_group(O, use_aut = true)
  return class_group(c, OK)
end

function create_ctx(OK::AbsSimpleNumFieldOrder; bound::Int = -1, method::Int = 3, large::Int = 1000, redo::Bool = false, use_aut::Bool = false)
  if !redo
    c = get_attribute(OK, :ClassGrpCtx)
    if c !== nothing
      return c::ClassGrpCtx{SMat{ZZRingElem}}
    end
  end

  if bound == -1
    bound = Int(ceil(log(abs(discriminant(OK)))^2*0.3))
    (bound == 0) && (bound = 1)
  end

  c = class_group_init(OK, bound, complete = false, use_aut = use_aut)::ClassGrpCtx{SMat{ZZRingElem}}
  @assert order(c) === OK
  return c
end
