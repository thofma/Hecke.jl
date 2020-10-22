add_verbose_scope(:Automorphisms)

################################################################################
#
#  Automorphisms
#
################################################################################


function _automorphisms(K::NfAbsNS; isabelian::Bool = false)
  pols = fmpq_poly[isunivariate(x)[2] for x in K.pol]
  rt = Vector{Vector{NfAbsNSElem}}(undef, length(pols))
  for i = 1:length(pols)
    rt[i] = roots(pols[i], K)
  end
  auts = Vector{NfAbsNSToNfAbsNS}(undef, prod(length(x) for x in rt))
  ind = 1
  for i in CartesianIndices(Tuple(1:length(x) for x in rt))
    auts[ind] = hom(K, K, [rt[i[j]] for j = 1:length(pols)])
    ind += 1
  end
  return auts
end


function _automorphisms(K::AnticNumberField; isabelian::Bool = false)
  if degree(K) == 1
    return NfToNfMor[hom(K, K, one(K))]
  end
  if Nemo.iscyclo_type(K)
    f = get_special(K, :cyclo)::Int
    a = gen(K)
    A, mA = unit_group(ResidueRing(FlintZZ, f, cached = false))
    auts = NfToNfMor[ hom(K, K, a^lift(mA(g)), check = false) for g in A]
    return auts
  end
  if isabelian
    return _automorphisms_abelian(K)
  end
  c = get_special(K, :isabelian)
  if c !== nothing && c
    return _automorphisms_abelian(K)
  end
  f = K.pol
  ord_aut = _order_bound(K)
  if ord_aut == 1
    return NfToNfMor[id_hom(K)]
  end
  Kt, t = PolynomialRing(K, "t", cached = false)
  f1 = change_base_ring(K, f, parent = Kt)
  divpol = Kt(nf_elem[-gen(K), K(1)])
  f1 = divexact(f1, divpol)
  lr = roots(f1, max_roots = div(ord_aut, 2))
  Aut1 = Vector{NfToNfMor}(undef, length(lr)+1)
  for i = 1:length(lr)
    Aut1[i] = hom(K, K, lr[i], check = false)
  end
  Aut1[end] = id_hom(K)
  auts = closure(Aut1, degree(K))
  return auts
end


function _order_bound(K::AnticNumberField)
  p = 101
  i = 0
  ord = degree(K)
  while i < 15 && !isone(ord)
    p = next_prime(p)
    F = GF(p, cached = false)
    Fx, x = PolynomialRing(F, cached = false)
    fF = Fx(K.pol)
    if degree(fF) != degree(K) || iszero(discriminant(fF))
      continue
    end
    i += 1
    fF1 = gcd(powmod(x, p, fF)-x, fF) 
    if !isone(fF1)
      ord = gcd(ord, degree(fF1))
    end
  end
  return ord
end
  
function _generator_automorphisms(K::AnticNumberField)
  if degree(K) == 1
    return NfToNfMor[]
  end
  if Nemo.iscyclo_type(K)
    f = get_special(K, :cyclo)::Int
    a = gen(K)
    A, mA = unit_group(ResidueRing(FlintZZ, f, cached = false))
    auts = NfToNfMor[ hom(K, K, a^lift(mA(g)), check = false) for g in gens(A)]
    return auts
  end
  f = K.pol
  Kt, t = PolynomialRing(K, "t", cached = false)
  f1 = change_base_ring(K, f, parent = Kt)
  divpol = Kt(nf_elem[-gen(K), K(1)])
  f1 = divexact(f1, divpol)
  lr = roots(f1, max_roots = div(degree(K), 2))
  Aut1 = Vector{NfToNfMor}(undef, length(lr))
  for i = 1:length(lr)
    Aut1[i] = hom(K, K, lr[i], check = false)
  end
  return small_generating_set(Aut1)
end

automorphism_type(::AnticNumberField) = NfToNfMor
automorphism_type(::NfAbsNS) = NfAbsNSToNfAbsNS
  

@doc Markdown.doc"""
    automorphisms(K::AnticNumberField) -> Vector{NfToNfMor}

Returns the set of automorphisms of K
"""  
function automorphisms(K::NumField{fmpq}; copy::Bool = true, isabelian::Bool = false)
  T = automorphism_type(K)
  if isautomorphisms_known(K)
    Aut = get_automorphisms(K)
    if copy
      v = Vector{T}(undef, length(Aut))
      for i = 1:length(v)
        v[i] = Aut[i]
      end
      return v
    else
      return Aut::Vector{T}
    end
  end
  auts = _automorphisms(K, isabelian = isabelian)
  set_automorphisms(K, auts)
  if copy
    v = Vector{T}(undef, length(auts))
    for i = 1:length(v)
      v[i] = auts[i]
    end
    return v
  else
    return auts
  end
end
  
function isautomorphisms_known(K::AnticNumberField)
  return _get_automorphisms_nf(K, false) != nothing
end

function isautomorphisms_known(K::NfAbsNS)
  return get_special(K, :automorphisms) !== nothing
end

function get_automorphisms(K::AnticNumberField)
  return _get_automorphisms_nf(K)::Vector{NfToNfMor}
end

function get_automorphisms(K::NfAbsNS)
  return get_special(K, :automorphisms)::Vector{NfAbsNSToNfAbsNS}
end

function set_automorphisms(K::AnticNumberField, auts::Vector{NfToNfMor})
  _set_automorphisms_nf(K, auts)
  return nothing
end

function set_automorphisms(K::NfAbsNS, auts::Vector{NfAbsNSToNfAbsNS})
  set_special(K, :automorphisms => auts)
  return nothing
end


################################################################################
#
#  Automorphism Group
#
################################################################################

@doc Markdown.doc"""
    automorphism_group(K::AnticNumberField) -> GenGrp, GrpGenToNfMorSet

Given a number field $K$, this function returns a group $G$ and a map from $G$ to the automorphisms of $K$.
"""  
function automorphism_group(K::AnticNumberField)
  if Nemo.iscyclo_type(K)
    return _automorphism_group_cyclo(K)
  else
    return _automorphism_group_generic(K)
  end
end

function _automorphism_group_cyclo(K)
  f = get_special(K, :cyclo)
  a = gen(K)
  A, mA = unit_group(ResidueRing(FlintZZ, f))
  G, AtoG, GtoA = generic_group(collect(A), +)
  aut = NfToNfMor[ hom(K, K, a^lift(mA(GtoA[g])), check = false) for g in G]
  _set_automorphisms_nf(K, aut)
  return G, GrpGenToNfMorSet(G, aut, K)
end

function _automorphism_group_generic(K)
  aut = automorphisms(K)
  n = degree(K)
  #First, find a good prime
  p = 11
  d = numerator(discriminant(K.pol))
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  fmod = Rx(K.pol)
  pols = gfp_poly[Rx(g.prim_img) for g in aut]
  Dcreation = Vector{Tuple{gfp_poly, Int}}(undef, length(pols))
  for i = 1:length(pols)
    Dcreation[i] = (pols[i], i)
  end
  D = Dict{gfp_poly, Int}(Dcreation)
  mult_table = Array{Int, 2}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = D[Hecke.compose_mod(pols[s], pols[i], fmod)]
    end
  end
  G = GrpGen(mult_table)
  return G, GrpGenToNfMorSet(G, aut, K)
end

###############################################################################
#
#  NfToNfMor closure
#
###############################################################################

function closure(S::Vector{NfToNfMor}, final_order::Int = -1)

  K = domain(S[1])
  d = numerator(discriminant(K.pol))
  p = 11
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  fmod = Rx(K.pol)

  t = length(S)
  order = 1
  elements = NfToNfMor[id_hom(K)]
  pols = gfp_poly[x]
  gpol = Rx(S[1].prim_img)
  if gpol != x
    push!(pols, gpol)
    push!(elements, S[1])
    order += 1

    gpol = compose_mod(gpol, pols[2], fmod)

    while gpol != x
      order = order +1
      push!(elements, S[1]*elements[end])
      push!(pols, gpol)
      gpol = compose_mod(gpol, pols[2], fmod)
    end
  end

  if order == final_order
    return elements
  end

  for i in 2:t
    if !(S[i] in elements)
      pi = Rx(S[i].prim_img)
      previous_order = order
      order = order + 1
      push!(elements, S[i])
      push!(pols, Rx(S[i].prim_img))
      for j in 2:previous_order
        order = order + 1
        push!(pols, compose_mod(pols[j], pi, fmod))
        push!(elements, elements[j]*S[i])
      end
      if order == final_order
        return elements
      end
      rep_pos = previous_order + 1
      while rep_pos <= order
        for k in 1:i
          s = S[k]
          po = Rx(s.prim_img)
          att = compose_mod(pols[rep_pos], po, fmod)
          if !(att in pols)
            elt = elements[rep_pos]*s
            order = order + 1
            push!(elements, elt)
            push!(pols, att)
            for j in 2:previous_order
              order = order + 1
              push!(pols, compose_mod(pols[j], att, fmod))
              push!(elements, elements[j] *elt)
            end
            if order == final_order
              return elements
            end
          end
        end
        rep_pos = rep_pos + previous_order
      end
    end
  end
  return elements
end

function generic_group(G::Vector{NfToNfMor}, ::typeof(*), full::Bool = true)
  K = domain(G[1])
  n = length(G)
  #First, find a good prime
  p = 11
  d = numerator(discriminant(K.pol))
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = GF(p, cached = false)
  Rx, x = PolynomialRing(R, "x", cached = false)
  fmod = Rx(K.pol)
  pols = gfp_poly[Rx(g.prim_img) for g in G]
  Dcreation = Vector{Tuple{gfp_poly, Int}}(undef, length(pols))
  for i = 1:length(pols)
    Dcreation[i] = (pols[i], i)
  end
  D = Dict{gfp_poly, Int}(Dcreation)
  #full && @assert length(D) == degree(K)
  permutations = Array{Array{Int, 1},1}(undef, n)

  m_table = Array{Int, 2}(undef, n, n)

  for s = 1:n
    for i = 1:n
      m_table[s, i] =  D[Hecke.compose_mod(pols[s], pols[i], fmod)]
    end
  end

  Gen = GrpGen(m_table)
  GentoG = Dict{GrpGenElem, eltype(G)}(Gen[i] => G[i] for i in 1:length(G))
  GtoGen = Dict{eltype(G), GrpGenElem}(G[i] => Gen[i] for i in 1:length(G))
  return Gen, GtoGen, GentoG
end

################################################################################
#
#  Automorphisms abelian fields
#
################################################################################

function _automorphisms_abelian(K::AnticNumberField)

  #@assert isabelian(K)
  auts = NfToNfMor[id_hom(K)]
  p = 2
  dp = denominator(K.pol)
  while length(auts) != degree(K)
    p = next_prime(p)
    if divisible(dp, p)
      continue
    end
    F = GF(p, cached = false)
    Fx = PolynomialRing(F, cached = false)[1]
    fF = Fx(K.pol)
    if degree(fF) != degree(K) || iszero(discriminant(fF))
      continue 
    end
    @vprint :Automorphisms 1 "Trying $p \n"
    @vtime :Automorphisms 1 isnew, h = _frobenius_at(K, p, auts)
    if !isnew
      @vprint :Automorphisms "Not new! \n"
      continue
    end
    @vprint :Automorphisms "New! Computing closure \n"
    push!(auts, h)
    auts = closure(auts)
  end
  return auts
end


function _frobenius_at(K::AnticNumberField, p::Int, auts::Vector{NfToNfMor} = NfToNfMor[]; bound::Int = 100)

  Zx = FlintZZ["x"][1]
  F = ResidueRing(FlintZZ, p, cached = false)
  Fx, gFx = PolynomialRing(F, "x", cached = false)
  fF = map_coeffs(F, Zx(K.pol), parent = Fx)
  b = powmod(gFx, p, fF)
  if b in nmod_poly[Fx(x.prim_img) for x in auts]
    return false, id_hom(K)
  end
  if fF == gcd(powmod(gFx, p, fF)-gFx, fF)
    return false, id_hom(K)
  end
  test = 2^10
  dfF = derivative(fF)
  dF = K(derivative(K.pol))
  evdfF = compose_mod(dfF, b, fF)
  w = invmod(evdfF, fF)
  b_0 = lift(Zx, b)
  w_0 = lift(Zx, w)
  #Now, the lifting
  r_old = one(K)
  modu = fmpz(p)^2
  R = ResidueRing(FlintZZ, modu, cached = false)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  fR = map_coeffs(R, Zx(K.pol), parent = Rx)
  Rb_0 = Rx(b_0)
  Rw_0 = Rx(w_0)
  bi = compose_mod(fR, Rb_0, fR)
  bi = mulmod(Rw_0, bi, fR)
  bi = sub!(bi, Rb_0, bi)
  b_0 = lift(Zx, bi)
  r = K(parent(K.pol)(b_0))
  mul!(r, r, dF)
  mod_sym!(r, modu)
  i = 0
  while i < bound && r != r_old && !check_root(K, test, r) 
    i += 1
    modu = modu^2
    R = ResidueRing(FlintZZ, modu, cached = false)
    Rx = PolynomialRing(R, "x", cached = false)[1]
    fR = map_coeffs(R, Zx(K.pol), parent = Rx)
    Rb_0 = Rx(b_0)
    Rw_0 = Rx(w_0)
    @vtime :Automorphisms 4 A, fRinv = precomp_compose_mod(Rb_0, fR)
    @vtime :Automorphisms 4 wi = compose_mod_precomp(derivative(fR), A, fR, fRinv)
    wi = wi * Rw_0
    wi = 2 - wi
    wi = mulmod(wi, Rw_0, fR)
    @vtime :Automorphisms 4 bi = my_compose_mod_precomp(fR, A, fR, fRinv)
    bi = mulmod(bi, wi, fR)
    bi = Rb_0 - bi
    b_0 = lift(Zx, bi)
    w_0 = lift(Zx, wi)
    r = K(parent(K.pol)(b_0))
    r = mul!(r, r, dF)
    r = mod_sym!(r, modu)
  end
  if i == bound
    if check_root(K, test, r)
      return true, hom(K, K, divexact(r, dF), check = false)
    else
      return false, id_hom(K)
    end
  end
  return true, hom(K, K, divexact(r, dF), check = false)
end


function _coefficients_bound(K::AnticNumberField)
  r1, r2 = signature(K)
  bound_root = Vector{arb}(undef, r1 + r2)
  a = gen(K)
  dfa = K(derivative(K.pol))
  dfa_conjs = conjugates_arb(dfa, 32)
  RR = ArbField(64, cached = false)
  RRt, t = PolynomialRing(RR, "t", cached = false)
  ub_f = roots_upper_bound(RRt(K.pol))
  for i in 1:r1+r2
    bound_root[i] = ub_f * abs(dfa_conjs[i])
  end
  E = EquationOrder(K)
  c1, c2 = norm_change_const(E)

  #First, t2 norm 
  R = parent(bound_root[1])
  bd = zero(R)
  for i in 1:r1
    bd += bound_root[i]^2
  end

  for i=1:r2
    bd += 2*bound_root[i+r1]^2
  end
  boundt2 = max(bd, one(R))
  return upper_bound(sqrt(R(c2)*boundt2), fmpz)
end

function check_root(K::AnticNumberField, p::Int, el::nf_elem)
  isroot = true
  cnt = 0
  q = p
  while cnt < 10
    q = next_prime(q)
    F = GF(q, cached = false)
    Fx = PolynomialRing(F, cached = false)[1]
    fF = Fx(K.pol)
    if degree(fF) != degree(K) || iszero(discriminant(fF))
      continue
    end
    cnt += 1
    img_el = Fx(el)*invmod(derivative(fF), fF)
    if !iszero(compose_mod(fF, img_el, fF))
      isroot = false
      break
    end
  end
  if !isroot
    @vprint :Automorphisms 4 "Not yet a root!\n"
  end
  return isroot
end


function _automorphisms_center(K::AnticNumberField)
  auts = NfToNfMor[id_hom(K)]
  p = 2
  dp = denominator(K.pol)
  coeffs_bound = 2*_coefficients_bound(K)
  cnt = 0
  while length(auts) != degree(K) && cnt < 40
    p = next_prime(p)
    if divisible(dp, p)
      continue
    end
    F = GF(p, cached = false)
    Fx = PolynomialRing(F, cached = false)[1]
    fF = Fx(K.pol)
    if degree(fF) != degree(K) || iszero(discriminant(fF))
      continue 
    end
    cnt += 1
    lf = factor_distinct_deg(fF)
    if length(lf) != 1
      continue
    end
    it_bound = clog(fmpz(clog(coeffs_bound, p)), 2)
    @vprint :Automorphisms "Trying $p \n"
    isnew, h = _frobenius_at(K, p, auts, bound = it_bound)
    if !isnew
      @vprint :Automorphisms "Not new! \n"
      continue
    end
    cnt = 0
    @vprint :Automorphisms "New! Computing closure \n"
    push!(auts, h)
    auts = closure(auts)
  end
  return auts
end
