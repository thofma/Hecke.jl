###############################################################################
#
#  Map Type
#
###############################################################################

mutable struct MapRayClassGrp <: Map{FinGenAbGroup, FacElemMon{Hecke.AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, HeckeMap, MapRayClassGrp}
  header::Hecke.MapHeader{FinGenAbGroup, FacElemMon{Hecke.AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}}
  defining_modulus::Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}}}
  fact_mod::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int} #The factorization of the finite part of the defining modulus

  gens::Tuple{Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, Vector{FinGenAbGroupElem}}

  #Dictionaries to cache preimages. Used in the action on the ray class group
  prime_ideal_preimage_cache::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FinGenAbGroupElem}
  prime_ideal_cache::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}

  clgrpmap::MapClassGrp
  powers::Vector{Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}
  groups_and_maps::Vector{Tuple{FinGenAbGroup, GrpAbFinGenToAbsOrdQuoRingMultMap}}
  disc_log_inf_plc::Dict{InfPlc, FinGenAbGroupElem} #The infinite places and the corresponding discrete logarithm.
  gens_mult_grp_disc_log::Vector{Tuple{AbsSimpleNumFieldOrderElem, FinGenAbGroupElem}}

  function MapRayClassGrp()
    z = new()
    z.prime_ideal_preimage_cache = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FinGenAbGroupElem}()
    return z
  end
end

defining_modulus(mR) = mR.defining_modulus

################################################################################
#
#  Function that stores the principal generators element of the powers
#  of the generators in the class group map
#
################################################################################

function __assure_princ_gen(c::Hecke.ClassGrpCtx{sparse_matrix_type(ZZ)}, nquo::Int)
  module_trafo_assure(c.M)
  C = c.dl_data[3]
  OK = order(c)
  s = c.dl_data[1]
  if length(c.dl_data) == 4
    T = c.dl_data[4]
  else
    T = inv(c.dl_data[2])
    c.dl_data = (s, c.dl_data[2], C, T)
  end
  RelHnf = c.M.basis
  gens = c.FB.ideals
  rels = vcat(c.R_gen, c.R_rel)
  trafo = c.M.trafo
  res = Tuple{FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}[]
  diff = ppio(Int(C.snf[end]), nquo)[2]
  diff_gens = ncols(T) - ngens(C)
  for i = 1:ngens(C)
    if nquo != -1
      if is_coprime(C.snf[i], nquo)
        continue
      end
      el = diff*sub(T, i+diff_gens:i+diff_gens, 1:ncols(T))
      ex = Int(ppio(Int(C.snf[i]), nquo)[1])
    else
      el = sub(T, i+diff_gens:i+diff_gens, 1:ncols(T))
      ex = Int(C.snf[i])
    end
    els_r = Tuple{Int, ZZRingElem}[]
    DI = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem}()
    for j = 1:ncols(el)
      if !iszero(el[1, j])
        add_to_key!(DI, gens[j+s-1], el[1, j])
        push!(els_r, (j+s-1, ex*el[1, j]))
      end
    end
    r = sparse_row(FlintZZ, els_r, sort = false)
    sol, d = _solve_ut(RelHnf, r)
    @assert isone(d)
    rs = zeros(ZZRingElem, c.M.bas_gens.r + c.M.rel_gens.r)

    for (p,v) in sol
      rs[p] = v
    end

    for i in length(trafo):-1:1
      apply_right!(rs, trafo[i])
    end

    e = FacElem(rels, rs)
    e = reduce_mod_units([e], get_attribute(OK, :UnitGrpCtx))[1]
    dd = e.fac
    for i = dd.idxfloor:length(dd.vals)
      if dd.slots[i] == 0x1 && iszero(dd.vals[i])
        dd.count -= 1
        dd.slots[i] = 0x0
      end
    end
    I = FacElem(DI)
    J, a = reduce_ideal(I)
    inv!(a)
    pow!(a, ex)
    mul!(e, e, a)
    push!(res, (FacElem(Dict(J => 1)), e))
  end
  return res
end

function _assure_princ_gen(mC::MapClassGrp)
  if isdefined(mC, :princ_gens)
    return nothing
  end
  C = domain(mC)
  OK = order(codomain(mC))
  K = nf(OK)
  if order(domain(mC)) == 1
    res1 = Vector{Tuple{FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}}()
    if ngens(domain(mC)) == 1
      push!(res1, (FacElem(Dict(ideal(OK, 1) => 1)), FacElem(Dict(K(1) => 1))))
    end
    mC.princ_gens = res1
    return nothing
  end
  c = get_attribute(OK, :ClassGrpCtx)
  if c !== nothing && isdefined(c, :dl_data)
    res = __assure_princ_gen(c, mC.quo)
    @hassert :RayFacElem 1 is_consistent(mC, res)
    mC.princ_gens = res
    return nothing
  else
    c = get_attribute(OK.lllO, :ClassGrpCtx)
    reslll = __assure_princ_gen(c, mC.quo)
    res = Vector{Tuple{FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}}(undef, length(reslll))
    for i = 1:length(res)
      fe = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem}()
      for (k, v) in reslll[i][1]
        fe[IdealSet(OK)(k)] = v
      end
      res[i] = (FacElem(fe), reslll[i][2])
    end
    @hassert :RayFacElem 1 is_consistent(mC, res)
    mC.princ_gens = res
    return nothing
  end
end

function is_consistent(mC, res)
  C = domain(mC)
  OK = order(codomain(mC))
  for i = 1:length(res)
    I = evaluate(res[i][1]).num
    if mC\I != C[i]
      return false
    end
    e = evaluate(res[i][2])
    J = ideal(OK, OK(e))
    if I^Int(C.snf[i]) != J
      return false
    end
  end
  return true
end

################################################################################
#
#  Class group as a ray class group
#
################################################################################

function class_as_ray_class(C::FinGenAbGroup, mC::MapClassGrp, exp_class::Function,  m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, expo::Int)

  O = order(m)
  X = abelian_group(rels(C))

  if expo != -1
    Q, mQ = quo(C, expo, false)
    local disclog1
    let Q = Q, mC = mC, mQ = mQ, X = X
      function disclog1(J::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
        return mQ(mC\(J))
      end

      function disclog1(J::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
        a = X[0]
        for (f, k) in J.fac
          a += k*disclog(f)
        end
        return a
      end
    end

    local expo_map
    let mQ = mQ, exp_class = exp_class
      function expo_map(el::FinGenAbGroupElem)
        @assert parent(el) === codomain(mQ)
        return exp_class(mQ\el)
      end
    end

    mp1 = Hecke.MapRayClassGrp()
    mp1.header = Hecke.MapHeader(Q, FacElemMon(parent(m)), expo_map, disclog1)
    mp1.fact_mod = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
    mp1.defining_modulus = (m, InfPlc[])
    mp1.clgrpmap = mC
    return Q, mp1
  end

  local disclog
  let X = X, mC = mC
    function disclog(J::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      return X((mC\J).coeff)
    end

    function disclog(J::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
      a = X[0]
      for (f, k) in J.fac
        a += k*disclog(f)
      end
      return a
    end
  end

  mp = Hecke.MapRayClassGrp()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)), exp_class, disclog)
  mp.fact_mod = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
  mp.defining_modulus = (m, InfPlc[])
  mp.clgrpmap = mC
  return X, mp
end

function empty_ray_class(m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  O = order(parent(m))
  X = abelian_group(Int[])

  local exp
  let O = O, X = X
    function exp(a::FinGenAbGroupElem)
      @assert parent(a) === X
      return FacElem(Dict(ideal(O,1) => ZZRingElem(1)))
    end
  end

  local disclog
  let X = X
    function disclog(J::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}})
      return id(X)
    end
  end

  mp = Hecke.MapRayClassGrp()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)) , exp, disclog)
  mp.defining_modulus = (m, InfPlc[])
  return X,mp

end

##############################################################################
#
#  Functions for the evaluation of factored elements
#
###############################################################################

#
#  Multiple elements evaluation
#
function fac_elems_eval(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, q::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, elems::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}, exponent::ZZRingElem)
  return _eval_quo(elems, p, q, exponent)
end

function _preproc(el::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, exponent::ZZRingElem)
  K = base_ring(el)
  OK = maximal_order(K)
  Qx = parent(K.pol)
  x = Dict{AbsSimpleNumFieldElem, ZZRingElem}()
  for (f, k) in el
    l = mod(k,exponent)
    if iszero(l)
      continue
    end
    if f in OK
      add_to_key!(x, f, l)
    else
      d = denominator(f, OK)
      add_to_key!(x, K(d), exponent-l)
      n = d*f
      c = numerator(content(Qx(n)))
      if isone(c)
        add_to_key!(x, n, l)
      else
        add_to_key!(x, divexact(n, c), l)
        add_to_key!(x, K(c), l)
      end
    end
  end
  if !isempty(x)
    return FacElem(x)
  else
    return FacElem(Dict(K(1)=> 1))
  end
end

function _preproc(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, el::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, exponent::ZZRingElem)
  O = order(p)
  K = nf(O)
  Qx = parent(K.pol)
  x = Dict{AbsSimpleNumFieldElem, ZZRingElem}()
  P = minimum(p, copy = false)
  for (f, k) in el
    l = mod(k,exponent)
    if iszero(l)
      continue
    end
    n = numerator(f)
    d = denominator(f)
    if !isone(d)
      com, uncom = ppio(d, P)
      if !isone(uncom)
        add_to_key!(x, K(mod(uncom, P)), exponent-l)
      end
      if !isone(com)
        e, b = is_perfect_power_with_data(com)
        add_to_key!(x, K(b), -e*l)
      end
    end
    c = numerator(content(Qx(n)))
    if isone(c)
      add_to_key!(x, n, l)
    else
      add_to_key!(x, divexact(n, c), l)
      com, uncom = ppio(c, P)
      if !isone(uncom)
        add_to_key!(x, K(mod(uncom, P)), l)
      end
      if !isone(com)
        e, b = is_perfect_power_with_data(com)
        add_to_key!(x, K(b), e*l)
      end
    end
  end
  if !isempty(x)
    return FacElem(x)
  else
    return FacElem(Dict(K(1)=> 1))
  end
end

function _preproc(p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, elems::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}, exponent::ZZRingElem)
  newelems = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[_preproc(p, x, exponent) for x in elems]
  return newelems
end


function _powermod(a::AbsSimpleNumFieldElem, i::Int, p::ZZRingElem)
  if iszero(i)
    return one(parent(a))
  elseif isone(i)
    b = mod(a, p)
    return b
  else
    bit = ~((~UInt(0)) >> 1)
    while (UInt(bit) & i) == 0
      bit >>= 1
    end
    z = deepcopy(a)
    bit >>= 1
    while bit != 0
      mul!(z, z, z)
      z = mod(z, p)
      if (UInt(bit) & i) != 0
        mul!(z, z, a)
        z = mod(z, p)
      end
      bit >>= 1
    end
    return z
  end
end

function _ev_quo(Q, mQ, elems, p, exponent, multiplicity::Int)
  el = elem_type(Q)[one(Q) for i = 1:length(elems)]
  anti_uni = anti_uniformizer(p)
  powers = Dict{Int, AbsSimpleNumFieldElem}()
  powers[1] = anti_uni
  O = order(p)
  F, mF = residue_field(O, p)
  for i = 1:length(elems)
    J = elems[i]
    vp = ZZRingElem(0)
    for (f, k1) in J
      k = mod(k1, exponent)
      if iszero(k)
        continue
      end
      if isinteger(f)
        inte = numerator(coeff(f, 0))
        vpp, np = remove(inte, minimum(p, copy = false))
        mul!(el[i], el[i], Q(np)^k)
        vp += vpp*k
        continue
      end
      el1 = O(f, false)
      if !iszero(mF(el1))
        if !isone(k)
          mul!(el[i], el[i], mQ(el1)^k)
        else
          mul!(el[i], el[i], mQ(el1))
        end
        continue
      end
      val = valuation(f, p)
      if haskey(powers, val)
        act_el = O(powers[val]*f, false)
      else
        exp_av = div(multiplicity*val, ramification_index(p))
        anti_val = _powermod(anti_uni, val, minimum(p)^(exp_av+1))
        powers[val] = anti_val
        act_el = O(anti_val*f, false)
      end
      if !isone(k)
        mul!(el[i], el[i], mQ(act_el)^k)
      else
        mul!(el[i], el[i], mQ(act_el))
      end
    end
    vp = mod(vp, exponent)
    if !iszero(vp)
      if haskey(powers, ramification_index(p))
        eli = minimum(p, copy = false)*powers[ramification_index(p)]
      else
        powers[ramification_index(p)] = _powermod(anti_uni, ramification_index(p), minimum(p)^(multiplicity+1))
        eli = minimum(p, copy = false)*powers[ramification_index(p)]
      end
      if isone(vp)
        mul!(el[i], el[i], mQ(O(eli, false)))
      else
        mul!(el[i], el[i], mQ(O(eli, false))^vp)
      end
    end
  end
  return AbsSimpleNumFieldOrderElem[mQ\el[i] for i=1:length(el)]
end

function _eval_quo(elems::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, q::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, exponent::ZZRingElem)
  O = order(p)
  if p == q
    if fits(Int, p.minimum)
      Q, mQ = ResidueFieldSmall(O, p)
      return _ev_quo(Q, mQ, elems, p, exponent, 1)
    else
      Q, mQ = residue_field(O, p)
      return _ev_quo(Q, mQ, elems, p, exponent, 1)
    end
  else
    Q, mQ = quo(O, q)
    mult = Int(clog(norm(q), norm(p)))
    return _ev_quo(Q, mQ, elems, p, exponent, mult)
  end
end

################################################################################
#
#  n-part of the class group
#
################################################################################

function is_coprime(a, b)
  return isone(gcd(a, b))
end

function n_part_class_group(mC::Hecke.MapClassGrp, n::Integer)
  O = order(codomain(mC))
  C = domain(mC)
  @assert is_snf(C)
  K = nf(O)
  if is_coprime(exponent(C), n)
    G = abelian_group(ZZRingElem[])
    local exp1
    let O = O, G = G
      function exp1(a::FinGenAbGroupElem)
        @assert parent(a) === G
        return ideal(O, one(O))
      end
    end

    local disclog1
    let G = G
      function disclog1(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
        return G[0]
      end
    end

    mp=Hecke.MapClassGrp()
    mp.quo = n
    mp.header=Hecke.MapHeader(G, mC.header.codomain, exp1, disclog1)
    mp.princ_gens = Tuple{FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}[]
    return G, mp
  end

  ind = findfirst(x -> !is_coprime(x, n), C.snf)
  diff = ppio(exponent(C), ZZRingElem(n))[2]

  invariants = ZZRingElem[ppio(x, ZZRingElem(n))[1] for x in C.snf[ind:end]]
  #filter!(!isone, invariants)
  G = abelian_group(invariants)
  local exp2
  let O = O, G = G
    function exp2(a::FinGenAbGroupElem)
      @assert parent(a) === G
      new_coeff = zero_matrix(FlintZZ, 1, ngens(C))
      for i = 1:ngens(G)
        new_coeff[1, i+ind-1] = a[i]*diff
      end
      return mC(C(new_coeff))
    end
  end


  local disclog2
  let G = G, mC = mC, C = C, diff = diff
    idiff = invmod(diff, exponent(G))
    function disclog2(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      if I.is_principal == 1
        return id(G)
      end
      x=idiff*(mC\I)
      y = zero_matrix(FlintZZ, 1, ngens(G))
      for i=ind:ngens(C)
        y[1,i-ind+1]=x.coeff[1,i]
      end
      return FinGenAbGroupElem(G, y)
    end
  end

  mp = Hecke.MapClassGrp()
  mp.header = Hecke.MapHeader(G, mC.header.codomain, exp2, disclog2)
  mp.quo = Int(exponent(G))
  if isdefined(mC, :princ_gens)
    princ_gens = Vector{Tuple{FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}}(undef, length(mC.princ_gens))
    for i = 1:length(princ_gens)
      princ_gens[i] = (mC.princ_gens[ind+i-1][1]^diff, mC.princ_gens[ind+i-1][2])
    end
    mp.princ_gens = princ_gens
  end
  return G, mp
end

################################################################################
#
#  Make positive
#
################################################################################

#makes the element x positive at all the embeddings adding a multiple of a
#TODO: Do this properly!
function make_positive(x::AbsSimpleNumFieldOrderElem, a::ZZRingElem)
  els = conjugates_real(elem_in_nf(x))
  m = ZZRingElem(0)
  for i=1:length(els)
    if is_positive(els[i])
      continue
    end
    y = abs(lower_bound(els[i], ZZRingElem))
    mu = div(y, a)
    m = max(m, mu+1)
  end
  #@hassert :RayFacElem 1 is_coprime(ideal(parent(x),x), ideal(parent(x), a))
  #@hassert :RayFacElem 1 is_coprime(ideal(parent(x),x+ZZRingElem(m)*a), ideal(parent(x), a))
  @hassert :RayFacElem 1 is_totally_positive(x+m*a)
  el_to_add = m*a
  return x+el_to_add
end

###################################################################################
#
#  Narrow Class Group
#
###################################################################################

@doc raw"""
    narrow_class_group(O::AbsSimpleNumFieldOrder) -> FinGenAbGroup, Map

Computes the narrow (or strict) class group of $O$, ie. the group of invertable
ideals modulo principal ideals generated by elements that are
positive at all real places.
"""
function narrow_class_group(O::AbsSimpleNumFieldOrder)
  @assert is_maximal_known_and_maximal(O)
  K = nf(O)
  plc = real_places(K)
  return ray_class_group(ideal(O, 1), real_places(K))
end

###################################################################################
#
#  Ray Class Group
#
###################################################################################

function ray_class_group(O::AbsSimpleNumFieldOrder, D::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}, inf_plc::Vector{<:InfPlc} = InfPlc[]; n_quo::Int = -1, GRH::Bool = true)
  I = ideal(O, 1)
  minI = ZZRingElem(1)
  for (p, v) in D
    q = p^v
    I *= q
    minI = lcm(minI, minimum(q))
  end
  I.minimum = minI
  return ray_class_group(I, inf_plc, GRH = GRH, n_quo = n_quo, lp = D)
end

#
# We compute the group using the sequence U -> (O/m)^* _> Cl^m -> Cl -> 1
#
@doc raw"""
    ray_class_group(m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, inf_plc::Vector{InfPlc}; n_quo::Int, lp::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}) -> FinGenAbGroup, MapRayClassGrp

Given an ideal $m$ and a set of infinite places of $K$,
this function returns the corresponding ray class group as an abstract group $\mathcal {Cl}_m$ and a map going
from the group into the group of ideals of $K$ that are coprime to $m$.
If `n_quo` is set, it will return the group modulo `n_quo`. The factorization of $m$ can be given with the keyword argument `lp`.
"""
function ray_class_group(m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, inf_plc::Vector{<:InfPlc} = Vector{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}}(); GRH::Bool = true, n_quo::Int = -1, lp::Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int} = factor(m))

  O = order(m)
  K = nf(O)

  C, mC = class_group(O, GRH = GRH)
  expC = exponent(C)
  diffC = ZZRingElem(1)
  if n_quo != -1
    C, mC = n_part_class_group(mC, n_quo)
    diffC = divexact(expC, exponent(C))
    expC = exponent(C)
  end
  if isone(m) && isempty(inf_plc)
    local exp_c
    let mC = mC
      function exp_c(a::FinGenAbGroupElem)
        return FacElem(Dict(mC(a) => 1))
      end
    end
    return class_as_ray_class(C, mC, exp_c, m, n_quo)
  end
  _assure_princ_gen(mC)

  exp_class, Kel = find_coprime_representatives(mC, m, lp)

  if n_quo != -1
    powers = Vector{Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}()
    quo_rings = Tuple{AbsSimpleNumFieldOrderQuoRing, Hecke.AbsOrdQuoMap{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsSimpleNumFieldOrderElem}}[]
    groups_and_maps = Tuple{FinGenAbGroup, Hecke.GrpAbFinGenToAbsOrdQuoRingMultMap{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsSimpleNumFieldOrderElem}}[]
    for (pp, vv) in lp
      dtame = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
      dwild = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
      npp = norm(pp)
      qq = ideal(O, 1)
      if !is_coprime(npp-1, n_quo)
        dtame[pp] = 1
        qq = pp
      end
      if vv > 1 && !is_coprime(npp, n_quo)
        dwild[pp] = vv
        qq = pp^vv
      end
      if isempty(dtame) && isempty(dwild)
        continue
      end
      push!(powers, (pp, qq))
      Q, mQ = quo(O, qq)
      if pp == qq
        Q.factor = dtame
      else
        Q.factor = dwild
      end
      push!(quo_rings, (Q, mQ))
      push!(groups_and_maps, _mult_grp_mod_n(quo_rings[end][1], dtame, dwild, n_quo))
    end
  else
    powers = Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}[(p, p^v) for (p, v) in lp]
    quo_rings = Tuple{AbsSimpleNumFieldOrderQuoRing, Hecke.AbsOrdQuoMap{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsSimpleNumFieldOrderElem}}[quo(O, q) for (p, q) in powers]
    groups_and_maps = Tuple{FinGenAbGroup, Hecke.GrpAbFinGenToAbsOrdQuoRingMultMap{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsSimpleNumFieldOrderElem}}[_multgrp(x[1], true) for x in quo_rings]
  end
  if isempty(groups_and_maps)
    nG = 0
    expon = ZZRingElem(1)
  else
    nG = sum(ngens(x[1]) for x in groups_and_maps)
    expon = lcm([exponent(x[1]) for x in groups_and_maps])
  end

  if n_quo == -1 || iseven(n_quo)
    p = filter(is_real, inf_plc)
  else
    p = InfPlc[]
  end
  H, eH, lH = sign_map(O, _embedding.(p), m)
  expon = lcm(expon, exponent(H))

  U, mU = unit_group_fac_elem(O, GRH = GRH)

  # We construct the relation matrix and evaluate units and relations with the class group in the quotient by m
  # Then we compute the discrete logarithms

  if n_quo == -1
    R = zero_matrix(FlintZZ, ngens(C)+nG+ngens(H)+ngens(U), ngens(H)+ngens(C)+nG)
  else
    R = zero_matrix(FlintZZ, 2*(ngens(C)+nG+ngens(H))+ngens(U), ngens(C)+ngens(H)+nG)
    for i = 1:ncols(R)
      R[i+ngens(C)+nG+ngens(H)+ngens(U), i] = n_quo
    end
  end
  for i=1:ngens(C)
    R[i,i] = C.snf[i]
  end
  ind = 1
  for s = 1:length(quo_rings)
    G = groups_and_maps[s][1]
    @assert is_snf(G)
    for i = 1:ngens(G)
      R[i+ngens(C)+ind-1, i+ngens(C)+ind-1] = G.snf[i]
    end
    ind += ngens(G)
  end
  for i = 1:ngens(H)
    R[ngens(C)+nG+i, ngens(C)+nG+i] = 2
  end

  @vprintln :RayFacElem 1 "Collecting elements to be evaluated; first, units"
  tobeeval1 = Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}(undef, ngens(U)+ngens(C))
  for i = 1:ngens(U)
    tobeeval1[i] = mU(U[i])
  end
  for i = 1:ngens(C)
    tobeeval1[i+ngens(U)] = mC.princ_gens[i][2]*(FacElem(Dict(Kel[i] => C.snf[i])))
  end
  tobeeval = _preproc(m, tobeeval1, expon)

  ind = 1
  for i = 1:length(groups_and_maps)
    exp_q = gcd(expon, norm(powers[i][2])- divexact(norm(powers[i][2]), norm(powers[i][1])))
    @vtime :RayFacElem 3 evals = fac_elems_eval(powers[i][1], powers[i][2], tobeeval, exp_q)
    Q = quo_rings[i][1]
    mG = groups_and_maps[i][2]
    for j = 1:ngens(U)
      a = (mG\Q(evals[j])).coeff
      for s = 1:ncols(a)
        R[j+nG+ngens(H)+ngens(C), ngens(C)+s+ind-1] = a[1, s]
      end
    end

    for j = 1:ngens(C)
      a = (mG\Q(evals[j+ngens(U)])).coeff
      for s = 1:ncols(a)
        R[j, ngens(C)+ind+s-1] = -a[1, s]
      end
    end
    ind += ngens(groups_and_maps[i][1])
  end

  if !isempty(p)
    for j = 1:ngens(U)
      a = lH(tobeeval1[j]).coeff
      for s = 1:ncols(a)
        R[j+nG+ngens(C)+ngens(H), ngens(C)+ind-1+s] = a[1, s]
      end
    end
    for j = 1:ngens(C)
      a = lH(tobeeval1[j+ngens(U)]).coeff
      for s = 1:ncols(a)
        R[j, ngens(C)+ind-1+s] = -a[1, s]
      end
    end
  end

  X = abelian_group(R)
  if n_quo != -1
    X.exponent = n_quo
  end

  local disclog
  let X = X, mC = mC, C = C, exp_class = exp_class, powers = powers, groups_and_maps = groups_and_maps, quo_rings = quo_rings, lH = lH, diffC = diffC, n_quo = n_quo, m = m, expon = expon
    invd = invmod(ZZRingElem(diffC), expon)
    # Discrete logarithm
    function disclog(J::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
      @vprintln :RayFacElem 1 "Disc log of element $J"
      a = id(X)
      for (f, k) in J
        a += k*disclog(f)
      end
      return a
    end

    function disclog(J::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      @hassert :RayFacElem 1 is_coprime(J, m)
      if isone(J)
        @vprintln :RayFacElem 1 "J is one"
        return id(X)
      end
      coeffs = zero_matrix(FlintZZ, 1, ngens(X))
      if J.is_principal == 1 && isdefined(J, :princ_gen)
        z = FacElem(Dict(J.princ_gen.elem_in_nf => diffC))
      else
        L = mC\J
        for i = 1:ngens(C)
          coeffs[1, i] = L[i]
        end
        @vprintln :RayFacElem 1 "Disc log of element J in the Class Group: $(L.coeff)"
        s = exp_class(L)
        inv!(s)
        add_to_key!(s.fac, J, 1)
        pow!(s, diffC)
        @vprintln :RayFacElem 1 "This ideal is principal: $s"
        z = principal_generator_fac_elem(s)
      end
      ii = 1
      z1 = _preproc(m, z, expon)
      for i = 1:length(powers)
        P, Q = powers[i]
        exponq = gcd(expon, norm(Q)-divexact(norm(Q), norm(P)))
        el = fac_elems_eval(P, Q, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[z1], exponq)
        y = (invd*(groups_and_maps[i][2]\quo_rings[i][1](el[1]))).coeff
        for s = 1:ncols(y)
          coeffs[1, ii-1+ngens(C)+s] = y[1, s]
        end
        ii += ngens(groups_and_maps[i][1])
      end
      if !isempty(p)
        b = lH(z).coeff
        for s = 1:ncols(b)
          coeffs[1, ii-1+s+ngens(C)] = b[1, s]
        end
      end
      return FinGenAbGroupElem(X, coeffs)
    end
  end

  Dgens = Tuple{AbsSimpleNumFieldOrderElem, FinGenAbGroupElem}[]
  ind = 1
  #For the exponential map and other purposes, we need generators of the full multiplicative group
  #In particular, we need the idempotents...
  for i = 1:length(powers)
    P, Q = powers[i]
    mG = groups_and_maps[i][2]
    J = ideal(O, 1)
    minJ = ZZRingElem(1)
    mins = ZZRingElem(1)
    for (PP, vPP) in lp
      if minimum(PP, copy = false) != minimum(P, copy = false)
        mins = lcm(mins, minimum(PP, copy = false)^vPP)
        continue
      end
      if PP != P
        Jm = PP^vPP
        J *= Jm
        minJ = lcm(minJ, minimum(Jm))
      end
    end
    J.minimum = minJ
    i1, i2 = idempotents(Q, J)
    if !isone(mins)
      d, u1, v1 = gcdx(minimum(Q, copy = false), mins)
      i1 = i1*(u1*minimum(Q, copy = false) + v1*mins) + u1*minimum(Q, copy = false) *i2
      i2 = v1*mins*i2
    end
    gens = mG.generators
    if isempty(p)
      if haskey(mG.tame, P)
        gens_tame = mG.tame[P].generators
        for s = 1:length(gens_tame)
          gens_tame[s] = gens_tame[s]*i2 + i1
        end
        mG.tame[P].generators = gens_tame
      end
      if haskey(mG.wild, P)
        gens_wild = mG.wild[P].generators
        for s = 1:length(gens_wild)
          gens_wild[s] = gens_wild[s]*i2 + i1
        end
        mG.wild[P].generators = gens_wild
      end
      for s = 1:length(gens)
        push!(Dgens, (gens[s].elem*i2+i1, X[ngens(C)+ind-1+s]))
      end

    else
      if haskey(mG.tame, P)
        gens_tame = mG.tame[P].generators
        for s = 1:length(gens_tame)
          gens_tame[s] = make_positive(gens_tame[s]*i2 + i1, minimum(m, copy = false))
        end
        mG.tame[P].generators = gens_tame
      end
      if haskey(mG.wild, P)
        gens_wild = mG.wild[P].generators
        for s = 1:length(gens_wild)
          gens_wild[s] = make_positive(gens_wild[s]*i2 + i1, minimum(m, copy = false))
        end
        mG.wild[P].generators = gens_wild
      end
      for s = 1:length(gens)
        elgen = make_positive(gens[s].elem*i2 + i1, minimum(m, copy = false))
        push!(Dgens, (elgen, X[ngens(C)+ind-1+s]))
      end
    end
    ind += length(gens)
  end

  local expo
  let C = C, O = O, groups_and_maps = groups_and_maps, exp_class = exp_class, eH = eH, H = H, K = K, Dgens = Dgens, X = X, p = p
    function expo(a::FinGenAbGroupElem)
      @assert parent(a) === X
      b = FinGenAbGroupElem(C, sub(a.coeff, 1:1, 1:ngens(C)))
      res = exp_class(b)
      for i = 1:nG
        if !iszero(a.coeff[1, ngens(C)+i])
          add_to_key!(res.fac, ideal(O, Dgens[i][1]), a.coeff[1, ngens(C)+i])
        end
      end
      for i = 1:length(p)
        if !iszero(a.coeff[i+nG+ngens(C)])
          add_to_key!(res.fac, ideal(O, O(1+eH(H[i]))), 1)
        end
      end
      return res
    end
  end

  ind = 1
  for i = 1:length(powers)
    mG = groups_and_maps[i][2]
    for (prim, mprim) in mG.tame
      dis = zero_matrix(FlintZZ, 1, ngens(X))
      to_be_c = mprim.disc_log.coeff
      for i = 1:length(to_be_c)
        dis[1, ind-1+i+ngens(C)] = to_be_c[1, i]
      end
      mprim.disc_log = FinGenAbGroupElem(X, dis)
    end
    ind += ngens(domain(mG))
  end

  disc_log_inf = Dict{InfPlc, FinGenAbGroupElem}()
  for i = 1:length(p)
    eldi = zero_matrix(FlintZZ, 1,  ngens(X))
    eldi[1, ngens(X) - length(p) + i] = 1
    disc_log_inf[p[i]] = FinGenAbGroupElem(X, eldi)
  end

  mp = MapRayClassGrp()
  mp.header = Hecke.MapHeader(X, FacElemMon(parent(m)), expo, disclog)
  mp.fact_mod = lp
  mp.defining_modulus = (m, inf_plc)
  mp.powers = powers
  mp.groups_and_maps = groups_and_maps
  mp.disc_log_inf_plc = disc_log_inf
  mp.gens_mult_grp_disc_log = Dgens
  mp.clgrpmap = mC
  return X, mp

end

##################################################################################
#
#  Ray Class Group over QQ
#
##################################################################################

function ray_class_groupQQ(O::AbsSimpleNumFieldOrder, modulus::Int, inf_plc::Bool, n_quo::Int)

  R=residue_ring(FlintZZ, modulus, cached=false)[1]
  U, mU = unit_group_mod(R, n_quo)
  U.exponent = n_quo
  if inf_plc
    function disc_log1(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      @assert gcd(minimum(I),modulus)==1
      i = Int(mod(I.minimum, modulus))
      return mU\(R(i))
    end

    function expon1(a::FinGenAbGroupElem)
      @assert parent(a) === domain(mU)
      x=mU(a)
      return FacElem(Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem}(ideal(O,lift(x)) => 1))
    end

    mp=Hecke.MapRayClassGrp()
    mp.header = Hecke.MapHeader(U, FacElemMon(parent(ideal(O,1))) , expon1, disc_log1)
    mp.defining_modulus = (ideal(O, modulus), real_places(nf(O)))
    return U, mp


  elseif isodd(n_quo)

    function disc_log2(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      @assert gcd(minimum(I),modulus)==1
      i=Int(mod(I.minimum, modulus))
      return mU\(R(i))
    end

    function expon2(a::FinGenAbGroupElem)
      @assert parent(a) === domain(mU)
      x=mU(a)
      return FacElem(Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem}(ideal(O,lift(x)) => 1))
    end

    mp = Hecke.MapRayClassGrp()
    mp.header = Hecke.MapHeader(U, FacElemMon(parent(ideal(O,1))) , expon2, disc_log2)
    mp.defining_modulus = (ideal(O, modulus), InfPlc[])
    return U,mp

  else

    Q, mQ = quo(U, FinGenAbGroupElem[mU\(R(-1))], false)

    function disc_log(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
      i=Int(mod(minimum(I), modulus))
      return mQ(mU\(R(i)))
    end

    function expon(a::FinGenAbGroupElem)
      @assert parent(a) === codomain(mQ)
      x=mU(mQ\a)
      return FacElem(Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem}(ideal(O,x) => 1))
    end

    mp=Hecke.MapRayClassGrp()
    mp.header = Hecke.MapHeader(Q, FacElemMon(parent(ideal(O,1))) , expon, disc_log)
    mp.defining_modulus = (ideal(O, modulus), InfPlc[])
    return Q,mp

  end

end

##################################################################################
#
#  Action of the Galois Group on the Ray Class Group
#
##################################################################################

#changes the generators of the multiplicative group so that they are coprime to a
function change_into_coprime(mR::MapRayClassGrp, a::ZZRingElem)
  m = minimum(mR.defining_modulus[1])
  com, uncom = ppio(a, m)
  if uncom == 1
    return nothing
  end
  _, s, t = gcdx(uncom, m)
  gens = mR.gens_mult_grp_disc_log
  for i = 1:length(gens)
    gens[i] = (gens[i][1]*s*uncom+m*t, gens[i][2])
  end
  mR.gens_mult_grp_disc_log = gens
  return nothing
end


#  Find convenient ideals that generate the ray class groups
function find_gens(mR::MapRayClassGrp; coprime_to::ZZRingElem = ZZRingElem(-1))

  O = order(codomain(mR))
  R = domain(mR)
  m = mR.defining_modulus[1]
  mm = minimum(m)
  if coprime_to != -1
    mm = lcm(mm, coprime_to)
  end
  mm = lcm(mm, discriminant(EquationOrder(nf(O))))
  if isdefined(mR, :gens)
    if coprime_to == -1
      return mR.gens[1], mR.gens[2]
    else
      found = false
      sR = FinGenAbGroupElem[]
      lp = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
      for i = 1:length(mR.gens[1])
        if is_coprime(mR.gens[1][i], coprime_to)
          push!(lp, mR.gens[1][i])
          push!(sR, mR.gens[2][i])
        else
          found = true
        end
      end
      if !found
        return lp, sR
      end
    end
  else
    sR = FinGenAbGroupElem[]
    lp = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  end

  q, mq = quo(R, sR, false)
  s, ms = snf(q)

  #  First, generators of the multiplicative group.
  #  If the class group is trivial, they are enough
  if isdefined(mR, :fact_mod) && !isempty(mR.fact_mod)
    if coprime_to != -1
      # First, I change them in order to be coprime to coprime_to
      change_into_coprime(mR, coprime_to)
    end
    gens_m = mR.gens_mult_grp_disc_log
    for i = 1:length(gens_m)
      el_q = mq(gens_m[i][2])
      if iszero(el_q)
        continue
      end
      if is_prime_power(order(s))
        el_in_s = ms\el_q
        found = false
        for j = 1:ngens(s)
          if is_coprime(el_in_s[j], s.snf[j])
            found = true
            break
          end
        end
        if found
          push!(sR, gens_m[i][2])
          push!(lp, ideal(O, gens_m[i][1]))
          q, mq = quo(R, sR, false)
          s, ms = snf(q)
          if order(s) == 1
            if !isdefined(mR, :gens)
              mR.gens = (lp, sR)
            end
            return lp, sR
          end
        end
      else
        push!(sR, gens_m[i][2])
        push!(lp, ideal(O, gens_m[i][1]))
        q, mq = quo(R, sR, false)
        s, ms = snf(q)
        if order(s) == 1
          if !isdefined(mR, :gens)
            mR.gens = (lp, sR)
          end
          return lp, sR
        end
      end
    end
  end

  if !isempty(mR.defining_modulus[2])
    S, ex, lo = sign_map(O, _embedding.(mR.defining_modulus[2]), m)
    for i=1:length(mR.defining_modulus[2])
      pl = mR.defining_modulus[2][i]
      if is_complex(pl)
        continue
      end
      f = mR.disc_log_inf_plc[pl]
      if iszero(mq(f))
        continue
      else
        el_in_snf = ms\mq(f)
        found = false
        for j = 1:ngens(s)
          if is_coprime(s.snf[j], el_in_snf[j])
            found = true
            break
          end
        end
        if found
          I = ideal(O, 1+ex(S[i])) # Careful! This way I am assuming an ordering!
          push!(sR, f)
          push!(lp, I)
          q, mq = quo(R, sR, false)
          s, ms = snf(q)
          if order(s)==1
	          if !isdefined(mR, :gens)
              mR.gens = (lp, sR)
            end
            return lp, sR
          end
        end
      end
    end
  end

  #This means that the class group is non trivial. I need primes generating the class group
  mC = mR.clgrpmap
  C = domain(mC)
  primes_class_group = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  disc_log_primes_class_grp = Vector{FinGenAbGroupElem}()
  if isdefined(mC, :small_gens)
    for x in mC.small_gens
      if !is_coprime(mm, minimum(x, copy = false))
        continue
      end
      push!(primes_class_group, x)
      push!(disc_log_primes_class_grp, mC\x)
    end
  end
  Q1, mQ1 = quo(C, disc_log_primes_class_grp, false)
  S1, mS1 = snf(Q1)
  p1 = ZZRingElem(2)
  while order(S1) != 1
    p1 = next_prime(p1)
    if !is_coprime(p1, mm)
      continue
    end
    lP = prime_decomposition(O, p1)
    for i = 1:length(lP)-1
      x = lP[i][1]
      f = mC\x
      el_in_snf = mS1\(mQ1(f))
      found = false
      for j = 1:ngens(S1)
        if is_coprime(S1.snf[j], el_in_snf[j])
          found = true
          break
        end
      end
      if found
        push!(primes_class_group, x)
        push!(disc_log_primes_class_grp, f)
        Q1, mQ1 = quo(C, disc_log_primes_class_grp, false)
        S1, mS1 = snf(Q1)
        if order(S1) == 1
          break
        end
      end
    end
  end
  for i = 1:length(primes_class_group)
    push!(lp, primes_class_group[i])
    push!(sR, mR\primes_class_group[i])
  end
  if !isdefined(mR, :gens)
    mR.gens = (lp, sR)
  end
  return lp, sR
end

function induce_action(mR::Union{MapRayClassGrp, MapClassGrp}, Aut::Vector{<:Hecke.NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, mp::FinGenAbGroupHom = id_hom(domain(mR)))
  R = domain(mR)
  G = Vector{FinGenAbGroupHom}(undef, length(Aut))
  if isempty(Aut)
    return G
  end
  K = domain(Aut[1])
  O = order(codomain(mR))

  #  Instead of applying the automorphisms to the elements given by mR, I choose small primes
  #  generating the group and study the action on them. In this way, I take advantage of the cache of the
  #  class group map

  Igens, IPgens, subs, IPsubs = find_gens_for_action(mR)
  genstot = vcat(subs, IPsubs)
  for k = 1:length(Aut)
    images = Vector{FinGenAbGroupElem}(undef, length(Igens)+length(IPgens))
    for i=1:length(Igens)
      J = induce_image(Aut[k], Igens[i])
      images[i] = mR\J
    end
    for i = 1:length(IPgens)
      Pn = induce_image(Aut[k],IPgens[i])
      images[i+length(Igens)] = mR.disc_log_inf_plc[Pn]
    end

    if mp == id_hom(R)
      G[k] = hom(genstot, images, check = true)
    else
      G[k] = hom(FinGenAbGroupElem[mp(x) for x = genstot], FinGenAbGroupElem[mp(x) for x = images], check = true)
    end
    @hassert :RayFacElem 1 is_bijective(G[k])
  end
  return G

end

function find_gens_for_action(mR::MapClassGrp)

	lp, sR = find_gens(pseudo_inv(mR), PrimesSet(2, -1))
  ip = InfPlc[]
  sR1 = FinGenAbGroupElem[]
	return lp, ip, sR, sR1

end

#  Find places that generate the ray class group
function find_gens_for_action(mR::MapRayClassGrp)
  O = order(codomain(mR))
  R = domain(mR)
  m = mR.defining_modulus[1]
  mm = minimum(m)
  lp = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
  sR = FinGenAbGroupElem[]
  ip = InfPlc[]
  sR1 = FinGenAbGroupElem[]
  q, mq = quo(R, sR, false)

  #  First, generators of the multiplicative group.
  #  If the class group is trivial, they are enough
  if isdefined(mR, :fact_mod) && !isempty(mR.fact_mod)
    gens_and_logs = mR.gens_mult_grp_disc_log
    for j = 1:length(gens_and_logs)
    	if iszero(mq(gens_and_logs[j][2]))
    	  continue
    	end
    	push!(sR, gens_and_logs[j][2])
    	push!(lp, ideal(O, gens_and_logs[j][1]))
      q, mq = quo(R, sR, false)
      if order(q) == 1
        return lp, ip, sR, sR1
      end
    end
  end

  if !isempty(defining_modulus(mR)[2])
    dlog_dict = mR.disc_log_inf_plc
    for (p, v) in dlog_dict
      if iszero(mq(v))
        continue
      end
      push!(ip, p)
      push!(sR1, v)
      q, mq = quo(R, vcat(sR, sR1), false)
      if order(q) == 1
        return lp, ip, sR, sR1
      end
    end
  end
  #Now, gens of class group. Those are cached in the class group map
  mC = mR.clgrpmap
  if isdefined(mC, :small_gens)
    for P in mC.small_gens
      if is_coprime(minimum(P, copy = false), mm)
        push!(lp, P)
        push!(sR, mR\P)
      end
    end
  end
  q, mq = quo(R, vcat(sR, sR1), false)
  if order(q) != 1
    lpmC, srmC = find_gens(pseudo_inv(mC), PrimesSet(2, -1), mm)
    for P in lpmC
      push!(lp, P)
      push!(sR, mR\P)
    end
  end
  return lp, ip, sR, sR1
end

################################################################################
#
#  Generator 1 mod m
#
################################################################################

@doc raw"""
    has_principal_generator_1_mod_m(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, inf_plc::Vector{InfPlc} = InfPlc[]) -> Bool, AbsSimpleNumFieldOrderElem

Given an ideal $I$, this function checks if the ideal is trivial in the ray class group mod ($m$, inf_plc).
If this is the case, we also return a generator which is 1 mod $m$. If not, the second return value is wrong.
"""
function has_principal_generator_1_mod_m(I::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}}, m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, inf_plc::Vector{<:InfPlc} = InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}[]; GRH::Bool = true)

  # This function could be optimized if I cache some stuff from the construction
  # of the ray class group, but only in the case of the full ray_class_group
  # and not in the quotient.

  @assert all(x -> isreal(x), inf_plc)

  O = order(m)
  C, mC = class_group(O, GRH = GRH)
  fl, gen = is_principal_fac_elem(I)
  if !fl
    return fl, gen
  end
  U, mU = unit_group_fac_elem(O, GRH = GRH)

  lp = factor(m)
  powers = Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}[(x, x^v) for (x, v) in lp]
  quo_rings = Tuple{AbsSimpleNumFieldOrderQuoRing, NfOrdQuoMap}[quo(O, q) for (x, q) in powers]
  groups_and_maps = Tuple{FinGenAbGroup, Hecke.GrpAbFinGenToAbsOrdQuoRingMultMap{AbsNumFieldOrder{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsNumFieldOrderIdeal{AbsSimpleNumField,AbsSimpleNumFieldElem},AbsSimpleNumFieldOrderElem}}[multiplicative_group(Q[1]) for Q in quo_rings]
  invariants = Vector{ZZRingElem}()
  for x in groups_and_maps
    append!(invariants, x[1].snf)
  end
  for x in inf_plc
    push!(invariants, ZZRingElem(2))
  end
  G = abelian_group(invariants)

  expo = exponent(G)
  tobeeval1 = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[mU(x) for x in gens(U)]
  push!(tobeeval1, gen)
  tobeeval = _preproc(m, tobeeval1, expo)
  coeffs = Vector{ZZMatrix}(undef, length(tobeeval))
  for i = 1:length(coeffs)
    coeffs[i] = zero_matrix(FlintZZ, 1, ngens(G))
  end
  ii = 1
  for i = 1:length(powers)
    P, Q = powers[i]
    exponq = gcd(expo, norm(Q)-divexact(norm(Q), norm(P)))
    els = fac_elems_eval(P, Q, tobeeval, exponq)
    for t = 1:length(els)
      el = els[t]
      y = (groups_and_maps[i][2]\quo_rings[i][1](el)).coeff
      for s = 1:ncols(y)
        coeffs[t][1, ii-1+s] = y[1, s]
      end
    end
    ii += ngens(groups_and_maps[i][1])
  end
  if !isempty(inf_plc)
    H, eH, lH = infinite_primes_map(O, inf_plc, m)
    for t = 1:length(tobeeval)
      el = lH(tobeeval[i])
      for s = 1:ngens(H)
        coeffs[t][1, ii-1+s] = el[s]
      end
    end
  end
  els_G = FinGenAbGroupElem[G(x) for x in coeffs]
  S, mS = sub(G, els_G[1:end-1])
  fl1, coord = has_preimage_with_preimage(mS, els_G[end])
  if !fl1
    return false, gen
  end
  @assert ngens(S) == ngens(U)
  for i = 1:ngens(U)
    if coord[i] != 0
      mul!(gen, gen, tobeeval1[i]^-Int(coord[i]))
    end
  end
  return true, gen
end

function disc_log_generalized_ray_class_grp(I::Union{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}}, mr::MapRayClassGrp)
  el = mr\I
  J = mr(el)
  I1 = I * inv(J)
  fl1, gen1 = has_principal_generator_1_mod_m(I1, mr.defining_modulus[1], mr.defining_modulus[2])
  @assert fl1
  return gen1, el
end
