add_verbose_scope(:Automorphisms)

################################################################################
#
#  Automorphisms
#
################################################################################

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
    c = get_special(K, :isabelian)
    if c !== nothing && c
      return _automorphisms_abelian(K)
    end
    if isabelian
      return _automorphisms_abelian(K)
    end
    f = K.pol
    Kt, t = PolynomialRing(K, "t", cached = false)
    f1 = change_base_ring(K, f, parent = Kt)
    divpol = Kt(nf_elem[-gen(K), K(1)])
    f1 = divexact(f1, divpol)
    lr = roots(f1, max_roots = div(degree(K), 2))
    Aut1 = Vector{NfToNfMor}(undef, length(lr)+1)
    for i = 1:length(lr)
      Aut1[i] = hom(K, K, lr[i], check = false)
    end
    Aut1[end] = id_hom(K)
    auts = closure(Aut1, degree(K))
    return auts
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
  
  @doc Markdown.doc"""
      automorphisms(K::AnticNumberField) -> Vector{NfToNfMor}
  
  Returns the set of automorphisms of K
  """  
  function automorphisms(K::AnticNumberField; copy::Bool = true, isabelian::Bool = false)
    if isautomorphisms_known(K)
      Aut = _get_automorphisms_nf(K)::Vector{NfToNfMor}
      if copy
        v = Vector{NfToNfMor}(undef, length(Aut))
        for i = 1:length(v)
          v[i] = Aut[i]
        end
        return v
      else
        return Aut::Vector{NfToNfMor}
      end
    end
    auts = _automorphisms(K, isabelian = isabelian)
    _set_automorphisms_nf(K, auts)
    if copy
      v = Vector{NfToNfMor}(undef, length(auts))
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
    @vprint :Automorphisms "Trying $p \n"
    isnew, h = _frobenius_at(K, p)
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


function _frobenius_at(K::AnticNumberField, p::Int, auts::Vector{NfToNfMor} = NfToNfMor[])

  Zx = FlintZZ["x"][1]
  F = ResidueRing(FlintZZ, p, cached = false)
  Fx, gFx = PolynomialRing(F, "x", cached = false)
  fF = map_coeffs(F, Zx(K.pol), parent = Fx)
  b = powmod(gFx, p, fF)
  if b in nmod_poly[map_coeffs(F, x, parent = Fx) for x in auts]
    return false, id_hom(K)
  end
  fshape = factor_shape(fF)
  if first(keys(fshape)) == 1
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
  while r != r_old && !check_root(K, test, r)
    modu = modu^2
    R = ResidueRing(FlintZZ, modu, cached = false)
    Rx = PolynomialRing(R, "x", cached = false)[1]
    fR = map_coeffs(R, Zx(K.pol), parent = Rx)
    Rb_0 = Rx(b_0)
    Rw_0 = Rx(w_0)
    @vtime :Automorphisms 1 A, fRinv = precomp_compose_mod(Rb_0, fR)
    @vtime :Automorphisms 1 wi = compose_mod_precomp(derivative(fR), A, fR, fRinv)
    wi = wi * Rw_0
    wi = 2 - wi
    wi = mulmod(wi, Rw_0, fR)
    @vtime :Automorphisms 1 bi = my_compose_mod_precomp(fR, A, fR, fRinv)
    bi = mulmod(bi, wi, fR)
    bi = Rb_0 - bi
    b_0 = lift(Zx, bi)
    w_0 = lift(Zx, wi)
    r = K(parent(K.pol)(b_0))
    r = mul!(r, r, dF)
    r = mod_sym!(r, modu)
  end
  return true, hom(K, K, divexact(r, dF))
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
    @vprint :Automorphisms 1 "Not yet a root!\n"
  end
  return isroot
end


