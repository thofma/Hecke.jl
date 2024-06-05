add_verbosity_scope(:Automorphisms)

################################################################################
#
#  Automorphisms
#
################################################################################


function _automorphisms(K::AbsNonSimpleNumField; is_abelian::Bool = false)
  pols = QQPolyRingElem[to_univariate(Globals.Qx, x) for x in K.pol]
  rt = Vector{Vector{AbsNonSimpleNumFieldElem}}(undef, length(pols))
  for i = 1:length(pols)
    rt[i] = roots(K, pols[i])
  end
  auts = Vector{automorphism_type(K)}(undef, prod(length(x) for x in rt))
  ind = 1
  I = cartesian_product_iterator([1:length(x) for x in rt], inplace = true)
  for i in I
    auts[ind] = hom(K, K, elem_type(K)[rt[j][i[j]] for j = 1:length(pols)])
    ind += 1
  end
  return auts
end


function _automorphisms(K::AbsSimpleNumField; is_abelian::Bool = false)
  if degree(K) == 1
    return automorphism_type(K)[hom(K, K, one(K))]
  end
  if Nemo.is_cyclo_type(K)
    f = get_attribute(K, :cyclo)::Int
    a = gen(K)
    A, mA = unit_group(residue_ring(FlintZZ, f, cached = false)[1])
    auts = automorphism_type(K)[ hom(K, K, a^lift(mA(g)), check = false) for g in A]
    return auts
  end
  if is_abelian
    return _automorphisms_abelian(K)
  end
  c = get_attribute(K, :is_abelian)
  if c !== nothing && c
    return _automorphisms_abelian(K)
  end
  f = K.pol
  ord_aut = _order_bound(K)
  if ord_aut == 1
    return automorphism_type(K)[id_hom(K)]
  end

  Kt, t = polynomial_ring(K, "t", cached = false)
  f1 = change_base_ring(K, f, parent = Kt)
  divpol = Kt(AbsSimpleNumFieldElem[-gen(K), K(1)])
  f1 = divexact(f1, divpol)
  lr = roots(f1, max_roots = div(ord_aut, 2))
  Aut1 = Vector{automorphism_type(K)}(undef, length(lr)+1)
  for i = 1:length(lr)
    Aut1[i] = hom(K, K, lr[i], check = false)
  end
  Aut1[end] = id_hom(K)
  auts = closure(Aut1, degree(K))
  return auts
end


function _order_bound(K::AbsSimpleNumField)
  p = 101
  i = 0
  ord = degree(K)
  is_normal = true
  while i < 15 && !isone(ord)
    p = next_prime(p)
    F = GF(p, cached = false)
    Fx, x = polynomial_ring(F, cached = false)
    fF = Fx(K.pol)
    if degree(fF) != degree(K) || iszero(discriminant(fF))
      continue
    end
    i += 1
    sh = factor_shape(fF)
    if length(sh) != 1
      is_normal = false
    end
    if haskey(sh, 1)
      ord = gcd(ord, sh[1])
    end
  end
  if ord == degree(K) && !is_normal
    lf = factor(ord)
    divs = collect(keys(lf.fac))
    ord = Int(div(ord, minimum(divs)))
  end
  return ord
end

function _auts_cyclo(K::AbsSimpleNumField)
  f = get_attribute(K, :cyclo)::Int
  a = gen(K)
  A, mA = unit_group(residue_ring(FlintZZ, f, cached = false)[1])
  auts = automorphism_type(K)[ hom(K, K, a^lift(mA(g)), check = false) for g in gens(A)]
  return auts
end

function _generator_automorphisms(K::AbsSimpleNumField)
  if degree(K) == 1
    return automorphism_type(K)[]
  end
  if Nemo.is_cyclo_type(K)
    return _auts_cyclo(K)
  end
  f = K.pol
  Kt, t = polynomial_ring(K, "t", cached = false)
  f1 = change_base_ring(K, f, parent = Kt)
  divpol = Kt(AbsSimpleNumFieldElem[-gen(K), K(1)])
  f1 = divexact(f1, divpol)
  lr = roots(f1, max_roots = div(degree(K), 2))
  Aut1 = Vector{automorphism_type(K)}(undef, length(lr))
  for i = 1:length(lr)
    Aut1[i] = hom(K, K, lr[i], check = false)
  end
  return small_generating_set(Aut1)
end

automorphism_type(K::AbsSimpleNumField) = morphism_type(K, K)
automorphism_type(K::AbsNonSimpleNumField) = morphism_type(K)

function automorphism_list(K::NumField{QQFieldElem}; copy::Bool = true, is_abelian::Bool = false)
  T = automorphism_type(K)
  if is_automorphisms_known(K)
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
  auts = _automorphisms(K, is_abelian = is_abelian)
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

function is_automorphisms_known(K::Union{AbsSimpleNumField,AbsNonSimpleNumField})
  return has_attribute(K, :automorphisms)
end

function get_automorphisms(K::AbsSimpleNumField)
  return get_attribute(K, :automorphisms)::Vector{automorphism_type(K)}
end

function get_automorphisms(K::AbsNonSimpleNumField)
  return get_attribute(K, :automorphisms)::Vector{automorphism_type(K)}
end

function set_automorphisms(K::Union{AbsSimpleNumField,AbsNonSimpleNumField}, auts::Vector)
  set_attribute!(K, :automorphisms => auts)
end

function involution(K::Union{RelSimpleNumField, AbsSimpleNumField})
  @req degree(K) == 2 "Number field must have degree 2 over its base field"
  a = gen(K)
  A = automorphism_list(K)
  if A[1](a) == a
    return A[2]
  else
    return A[1]
  end
end

################################################################################
#
#  Automorphism Group
#
################################################################################

@doc raw"""
    automorphism_group(K::NumField) -> GenGrp, GrpGenToNfMorSet

Given a number field $K$, this function returns a group $G$ and a map from $G$ to the automorphisms of $K$.
"""
function automorphism_group(K::AbsSimpleNumField)
  if Nemo.is_cyclo_type(K)
    return _automorphism_group_cyclo(K)
  else
    return _automorphism_group_generic(K)
  end
end

function _automorphism_group_cyclo(K)
  f = get_attribute(K, :cyclo)::Int
  a = gen(K)
  A, mA = unit_group(residue_ring(FlintZZ, f)[1])
  G, AtoG, GtoA = generic_group(collect(A), +)
  aut = automorphism_type(K)[ hom(K, K, a^lift(mA(GtoA[g])), check = false) for g in G]
  set_automorphisms(K, aut)
  return G, GrpGenToNfMorSet(G, aut, K)
end

function _automorphism_group_generic(K::AbsSimpleNumField)
  aut = automorphism_list(K)
  n = degree(K)
  #First, find a good prime
  p = 11
  d = numerator(discriminant(K.pol))
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  fmod = Rx(K.pol)
  pols = fpPolyRingElem[Rx(image_primitive_element(g)) for g in aut]
  Dcreation = Vector{Tuple{fpPolyRingElem, Int}}(undef, length(pols))
  for i = 1:length(pols)
    Dcreation[i] = (pols[i], i)
  end
  D = Dict{fpPolyRingElem, Int}(Dcreation)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = D[Hecke.compose_mod(pols[s], pols[i], fmod)]
    end
  end
  G = MultTableGroup(mult_table)
  return G, GrpGenToNfMorSet(G, aut, K)
end

function automorphism_group(K::NumField)
  aut = automorphism_list(K)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = findfirst(isequal(aut[s]*aut[i]), aut)
    end
  end
  G = MultTableGroup(mult_table)
  return G, GrpGenToNfMorSet(G, aut, K)
end

@doc raw"""
    automorphism_group(L::NumField, K::NumField) -> GenGrp, GrpGenToNfMorSet

Given the number field extension $L$ and $K$, this function returns a group $G$
and a map from $G$ to the automorphisms of $L$ that fix $K$.
"""
function automorphism_group(L::NumField, K::NumField)
  aut = automorphism_list(L, K)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = findfirst(isequal(aut[s]*aut[i]), aut)
    end
  end
  G = MultTableGroup(mult_table)
  return G, GrpGenToNfMorSet(G, aut, L)
end

@doc raw"""
    absolute_automorphism_group(L::NumField) -> GenGrp, GrpGenToNfMorSet

Given the number field $L$, this function returns a group $G$
and a map from $G$ to the automorphisms of $L$ over the rationals.
"""
function absolute_automorphism_group(L::NumField)
  aut = absolute_automorphism_list(L)
  mult_table = Matrix{Int}(undef, length(aut), length(aut))
  for s = 1:length(aut)
    for i = 1:length(aut)
      mult_table[s, i] = findfirst(isequal(aut[s]*aut[i]), aut)
    end
  end
  G = MultTableGroup(mult_table)
  return G, GrpGenToNfMorSet(G, aut, L)
end

automorphism_group(L::NumField, ::QQField) = absolute_automorphism_group(L)

###############################################################################
#
#  NumFieldHom{AbsSimpleNumField, AbsSimpleNumField} closure
#
###############################################################################

function closure(S::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, final_order::Int = -1)

  K = domain(S[1])
  d = numerator(discriminant(K.pol))
  p = 11
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  fmod = Rx(K.pol)

  t = length(S)
  order = 1
  elements = automorphism_type(K)[id_hom(K)]
  pols = fpPolyRingElem[x]
  gpol = Rx(image_primitive_element(S[1]))
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
      pi = Rx(image_primitive_element(S[i]))
      previous_order = order
      order = order + 1
      push!(elements, S[i])
      push!(pols, Rx(image_primitive_element(S[i])))
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
          po = Rx(image_primitive_element(s))
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

function generic_group(G::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, ::typeof(*), full::Bool = true)
  K = domain(G[1])
  n = length(G)
  #First, find a good prime
  p = 11
  d = numerator(discriminant(K.pol))
  while mod(d, p) == 0
    p = next_prime(p)
  end
  R = Native.GF(p, cached = false)
  Rx, x = polynomial_ring(R, "x", cached = false)
  fmod = Rx(K.pol)
  pols = fpPolyRingElem[Rx(image_primitive_element(g)) for g in G]
  Dcreation = Vector{Tuple{fpPolyRingElem, Int}}(undef, length(pols))
  for i = 1:length(pols)
    Dcreation[i] = (pols[i], i)
  end
  D = Dict{fpPolyRingElem, Int}(Dcreation)
  #full && @assert length(D) == degree(K)
  permutations = Vector{Vector{Int}}(undef, n)

  m_table = Matrix{Int}(undef, n, n)

  for s = 1:n
    for i = 1:n
      m_table[s, i] =  D[Hecke.compose_mod(pols[s], pols[i], fmod)]
    end
  end

  Gen = MultTableGroup(m_table)
  GentoG = Dict{MultTableGroupElem, eltype(G)}(Gen[i] => G[i] for i in 1:length(G))
  GtoGen = Dict{eltype(G), MultTableGroupElem}(G[i] => Gen[i] for i in 1:length(G))
  return Gen, GtoGen, GentoG
end

################################################################################
#
#  Automorphisms abelian fields
#
################################################################################

function _automorphisms_abelian(K::AbsSimpleNumField)

  #@assert is_abelian(K)
  auts = automorphism_type(K)[id_hom(K)]
  p = 2
  dp = denominator(K.pol)
  while length(auts) != degree(K)
    p = next_prime(p)
    if is_divisible_by(dp, p)
      continue
    end
    F = GF(p, cached = false)
    Fx = polynomial_ring(F, cached = false)[1]
    fF = Fx(K.pol)
    if degree(fF) != degree(K) || iszero(discriminant(fF))
      continue
    end
    @vprintln :Automorphisms 1 "Trying $p"
    @vtime :Automorphisms 1 isnew, h = _frobenius_at(K, p, auts)
    if !isnew
      @vprintln :Automorphisms "Not new!"
      continue
    end
    @vprintln :Automorphisms "New! Computing closure"
    push!(auts, h)
    auts = closure(auts)
  end
  return auts
end

function lift_root(K::AbsSimpleNumField, b, bound::Int)
  Fx = parent(b)
  fF = Fx(K.pol)
  Zx = polynomial_ring(FlintZZ, "x")[1]
  p = modulus(Fx)
  test = 2^10
  dfF = derivative(fF)
  dF = K(derivative(K.pol))
  evdfF = compose_mod(dfF, b, fF)
  w = invmod(evdfF, fF)
  b_0 = lift(Zx, b)
  w_0 = lift(Zx, w)
  #Now, the lifting
  r_old = one(K)
  modu = ZZRingElem(p)^2
  R = residue_ring(FlintZZ, modu, cached = false)[1]
  Rx = polynomial_ring(R, "x", cached = false)[1]
  fR = map_coefficients(R, Zx(K.pol), parent = Rx)
  Rb_0 = Rx(b_0)
  Rw_0 = Rx(w_0)
  bi = compose_mod(fR, Rb_0, fR)
  bi = mulmod(Rw_0, bi, fR)
  bi = sub!(bi, Rb_0, bi)
  b_0 = lift(Zx, bi)
  r = K(parent(K.pol)(b_0))
  r_old = r + 1
  mul!(r, r, dF)
  mod_sym!(r, modu)
  i = 0
  while i < bound && r != r_old && !check_root(K, test, r)
    i += 1
    modu = modu^2
    R = residue_ring(FlintZZ, modu, cached = false)[1]
    Rx = polynomial_ring(R, "x", cached = false)[1]
    fR = Rx(K.pol)
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
      return true, divexact(r, dF)
    else
      return false, gen(K)
    end
  end
  return true, divexact(r, dF)
end


function _frobenius_at(K::AbsSimpleNumField, p::Int, auts::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}} = automorphism_type(K)[]; bound::Int = 100)

  Zx = FlintZZ["x"][1]
  F = residue_ring(FlintZZ, p, cached = false)[1]
  Fx, gFx = polynomial_ring(F, "x", cached = false)
  fF = map_coefficients(F, Zx(K.pol), parent = Fx)
  b = powermod(gFx, p, fF)
  if b in zzModPolyRingElem[Fx(image_primitive_element(x)) for x in auts]
    return false, id_hom(K)
  end
  fl, rt = lift_root(K, b, bound)
  if fl
    return true, hom(K, K, rt, check = false)
  else
    return false, id_hom(K)
  end
end


function _coefficients_bound(K::AbsSimpleNumField)
  r1, r2 = signature(K)
  bound_root = Vector{ArbFieldElem}(undef, r1 + r2)
  a = gen(K)
  dfa = K(derivative(K.pol))
  dfa_conjs = conjugates_arb(dfa, 32)
  RR = ArbField(64, cached = false)
  RRt, t = polynomial_ring(RR, "t", cached = false)
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
  return upper_bound(ZZRingElem, sqrt(R(c2)*boundt2))
end

function check_root(K::AbsSimpleNumField, p::Int, el::AbsSimpleNumFieldElem)
  isroot = true
  cnt = 0
  q = p
  while cnt < 10
    q = next_prime(q)
    F = Native.GF(q, cached = false)
    Fx = polynomial_ring(F, cached = false)[1]
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
    @vprintln :Automorphisms 4 "Not yet a root!"
  end
  return isroot
end

# This is flag, v
# If flag == true, then v is the center of the automorphism group
# If flag == false, then v is contained in the center
function _automorphisms_center(K::AbsSimpleNumField)
  auts = morphism_type(K)[id_hom(K)]
  p = 2
  dp = denominator(K.pol)
  coeffs_bound = 2*_coefficients_bound(K)
  cnt = 0
  ord = _order_bound(K)
  threshold = max(60, ord^2)
  while length(auts) < ord && cnt < threshold
    cnt += 1
    p = next_prime(p)
    if is_divisible_by(dp, p)
      continue
    end
    F = GF(p, cached = false)
    Fx = polynomial_ring(F, cached = false)[1]
    fF = Fx(K.pol)
    if degree(fF) != degree(K) || iszero(discriminant(fF))
      continue
    end
    lf = factor_distinct_deg(fF)
    if length(lf) != 1
      continue
    end
    it_bound = clog(ZZRingElem(clog(coeffs_bound, p)), 2)
    @vprintln :Automorphisms "Trying $p"
    isnew, h = _frobenius_at(K, p, auts, bound = it_bound)
    if !isnew
      @vprintln :Automorphisms "Not new!"
      continue
    end
    cnt = 0
    @vprintln :Automorphisms "New! Computing closure"
    push!(auts, h)
    auts = closure(auts)
  end
  return length(auts) == ord, auts
end

function is_abelian2(K::AbsSimpleNumField)
  if is_automorphisms_known(K)
    return is_abelian(automorphism_group(K)[1])
  end
  auts = automorphism_type(K)[id_hom(K)]
  p = 2
  dp = denominator(K.pol)
  coeffs_bound = 2*_coefficients_bound(K)
  while length(auts) != degree(K)
    p = next_prime(p)
    if is_divisible_by(dp, p)
      continue
    end
    F = GF(p, cached = false)
    Fx, gFx = polynomial_ring(F, cached = false)
    fF = Fx(K.pol)
    if degree(fF) != degree(K) || iszero(discriminant(fF))
      continue
    end
    lf = factor_distinct_deg(fF)
    if length(lf) != 1
      return false
    end
    it_bound = clog(ZZRingElem(clog(coeffs_bound, p)), 2)
    @vprintln :Automorphisms 1 "Trying $p"
    b = powermod(gFx, p, fF)
    if b in fpPolyRingElem[Fx(x(gen(K))) for x in auts]
      continue
    end
    fl, rt = lift_root(K, b, it_bound)
    if !fl
      return false
    end
    cnt = 0
    @vprintln :Automorphisms 1 "New! Computing closure"
    push!(auts, hom(K, K, rt, check = false))
    auts = closure(auts)
  end
  set_automorphisms(K, auts)
  return true
end

################################################################################
#
#   Automorphisms of relative extensions
#
################################################################################

function automorphism_list(K::NumField, L::NumField)
  return _automorphisms(K, K, L)
end

function absolute_automorphism_list(K::NumField)
  return _automorphisms(K, K, FlintQQ)
end

function _automorphisms(K::NumField{QQFieldElem}, F::NumField, L::QQField)
  rt = roots(F, defining_polynomial(K))
  auts = morphism_type(K, F)[hom(K, F, x) for x in rt]
  return auts
end

function _automorphisms(K::T, F::NumField, L::T) where {T <: NumField{QQFieldElem}}
  if K == L
    return morphism_type(K, F)[hom(K, F, F(gen(K)))]
  else
    error("The base field is not naturally a subfield!")
  end
end

function _automorphisms(K::NumField, F::NumField, L::T) where {T <: Union{NumField, QQField}}
  if absolute_degree(K) < absolute_degree(L)
    error("The base field is not naturally a subfield!")
  end
  if K == L
    return morphism_type(K, F)[hom(K, F, F(gen(K)))]
  end
  autsk = _automorphisms(base_field(K), F, L)
  auts = morphism_type(K, F)[]
  for f in autsk
    rt = roots(map_coefficients(f, defining_polynomial(K), cached = false))
    for x in rt
      push!(auts, hom(K, F, f, x))
    end
  end
  return auts
end
