################################################################################
#
#  Simplify
#
################################################################################

function simplify(K::NfRel{nf_elem}; cached::Bool = true, prec::Int = 100)
  Kabs, mK, mk = absolute_field(K, cached = false)
  OK = maximal_order(K)
  new_basis = Vector{nf_elem}(undef, degree(Kabs))
  B = pseudo_basis(OK)
  ideals = Dict{NfOrdIdl, Vector{nf_elem}}()
  for i = 1:length(B)
    I = B[i][2].num
    if !haskey(ideals, I)
      bas = lll_basis(I)
      ideals[I] = nf_elem[mK\(K(x)) for x in bas]
    end
  end
  ind = 1
  for i = 1:degree(OK)
    I = B[i][2]
    bI = ideals[I.num]
    el = mK\(B[i][1])
    for j = 1:length(bI)
      new_basis[ind] = divexact(el*bI[j], I.den)
      ind += 1
    end
  end
  O = NfOrd(new_basis)
  O.ismaximal = 1
  O.disc = absolute_discriminant(OK)
  if prec == 100
    OLLL = lll(O)
  else
    OLLL = lll(O, prec = prec)
  end
  el = _simplify(OLLL, mK)
  pel = mK(el)
  f = minpoly(pel)
  @assert degree(f) == degree(K)
  Ks = number_field(f, cached = cached, check = false)[1]
  mKs = hom(Ks, K, pel)
  return Ks, mKs
end

#Finds a small elements given by small combinations of the basis of O 
#that generates the extension given by mK
function _simplify(O::NfOrd, mK::NfToNfRel)
  L = nf(O)
  #First, we choose the candidates
  B = basis(O, L)
  a = gen(L)
  Bnew = nf_elem[]
  nrep = min(3, degree(L))
  for i = 1:length(B)
    push!(Bnew, B[i])
    for j = 1:nrep
      push!(Bnew, B[i]+B[j])
      push!(Bnew, B[i]-B[j])
    end
  end

  #Now, we test for primitiveness.
  Lrel = codomain(mK)
  OLrel = maximal_order(Lrel)
  K = base_field(Lrel)
  OK = maximal_order(K)

  n = degree(Lrel)

  P, d = _find_prime(Lrel)
  p = minimum(P, copy = false)
  abs_deg = degree(P)*d
  FP, mFP = ResidueField(OK, P)
  mFP1 = extend_easy(mFP, K)
  #First, we search for elements that are primitive using block systems
  F = FlintFiniteField(p, abs_deg, "w", cached = false)[1]
  emb = find_embedding(FP, F)
  rt = roots(map_coeffs(emb, map_coeffs(mFP1, Lrel.pol)))

  indices = Int[]
  for i = 1:length(Bnew)
    if isone(denominator(Bnew[i]))
      continue
    end
    if _is_primitive_via_block(mK(Bnew[i]), rt, mFP1, emb)
      push!(indices, i)
    end
  end
  #Now, we select the one of smallest T2 norm
  I = t2(a)
  for i = 1:length(indices)
    t2n = t2(Bnew[indices[i]])
    if t2n < I
      a = Bnew[indices[i]]
      I = t2n
    end
  end
  return a
end

function find_embedding(F::FqFiniteField, K::FqFiniteField)
  f = defining_polynomial(F)
  rt = roots(f, K)
  img = rt[1]
  return (x -> sum([coeff(x, i)*img^i for i = 0:degree(F)-1]))
end


function _is_primitive_via_block(a::NfRelElem{nf_elem}, rt::Vector{fq}, mF, emb)
  n = degree(parent(a))
  pol = data(a)
  polF = map_coeffs(emb, map_coeffs(mF, pol))
  nconjs = 1
  conjs = Set{fq}([evaluate(polF, rt[1])])
  for i = 2:length(rt)
    ev = evaluate(polF, rt[i])
    if ev in conjs
      return false
    end
    push!(conjs, ev)
    nconjs += 1
    if nconjs > div(n, 2)
      return true
    end
  end
  error("Something went wrong")
end


function _block(a::NfRelElem{nf_elem}, rt::Vector{fq}, mF, emb)
  pol = data(a)
  polF = map_coeffs(emb, map_coeffs(mF, pol))
  evs = fq[evaluate(polF, x) for x in rt]
  b = Vector{Int}[]
  a = BitSet()
  i = 0
  n = length(rt)
  while i < length(evs)
    i += 1
    if i in a
      continue
    end
    z = evs[i]
    push!(b, findall(x-> evs[x] == z, 1:n))
    for j in b[end]
      push!(a, j)
    end
  end
  return b
end

function _find_prime(L::NfRel{nf_elem})
  p = 2^10
  K = base_field(L)
  OK = maximal_order(K)
  OL = maximal_order(L)

  n_attempts = min(degree(L), 10)
  candidates = Vector{Tuple{NfOrdIdl, Int}}(undef, n_attempts)
  i = 1
  f = L.pol
  threshold = degree(f)^2
  while i < n_attempts+1
    p = next_prime(p)
    if isindex_divisor(OK, p)
      continue
    end
    lp = prime_decomposition(OK, p)
    P = lp[1][1]
    if isindex_divisor(OL, P)
      continue
    end
    F, mF = ResidueField(OK, P)
    mF1 = extend_easy(mF, K)
    fF = map_coeffs(mF1, f)
    if degree(fF) != degree(f) || !issquarefree(fF)
      continue
    end
    FS = factor_shape(fF)
    d = lcm(Int[x for (x, v) in FS])
    if d < threshold
      candidates[i] = (P, d)
      i += 1
    end
  end
  res =  candidates[1]
  for j = 2:n_attempts
    if candidates[j][2] < res[2]
      res = candidates[j]
    end
  end
  return res[1], res[2]
end



function _sieve_primitive_elements(B::Vector{T}) where T <: NumFieldElem
  K = parent(B[1])
  n = absolute_degree(K)
  B1 = typeof(B)()
  k = div(n, 2)
  for x in B
    c = conjugates_arb(x, 16)
    isprimitive = true
    for i = 2:k+1
      for j = 1:i-1
        if overlaps(c[i], c[j])
          isprimitive = false
          break
        end
      end
      if !isprimitive
        break
      end
    end
    if isprimitive
      push!(B1, x)
    end
  end
  return B1
end

function _find_prime(L::NfRelNS{nf_elem})
  p = 2^10
  K = base_field(L)
  OK = maximal_order(K)
  OL = maximal_order(L)
  dL = numerator(discriminant(L, FlintQQ))

  n_attempts = min(degree(L), 10)
  candidates = Vector{Tuple{NfOrdIdl, Int}}(undef, n_attempts)
  i = 1
  pols = L.pol
  threshold = absolute_degree(L)^2
  polsR = Vector{fq_poly}(undef, length(pols))
  while i < n_attempts+1
    p = next_prime(p)
    if isindex_divisor(OK, p) || divisible(dL, p)
      continue
    end
    lp = prime_decomposition(OK, p)
    P = lp[1][1]
    @assert !isindex_divisor(OL, P)
    F, mF = ResidueField(OK, P)
    mF1 = extend(mF, K)
    is_proj = true
    for j = 1:length(pols)
      fF = isunivariate(map_coeffs(mF1, pols[j]))[2]
      if degree(fF) != total_degree(pols[j]) || !issquarefree(fF)
        is_proj = false
        break
      end
      polsR[j] = fF
    end
    if !is_proj
      continue
    end
    d = 1
    for j = 1:length(polsR)
      FS = factor_shape(polsR[j])
      d1 = lcm(Int[x for (x, v) in FS])
      d = lcm(d, d1)
    end
    if d < threshold
      candidates[i] = (P, d)
      i += 1
    end
  end
  res = candidates[1]
  for j = 2:n_attempts
    if candidates[j][2]*degree(candidates[j][1]) < res[2]*degree(res[1])
      res = candidates[j]
    end
  end
  return res[1], res[2]
end

function _sieve_primitive_elements(B::Vector{NfRelNSElem{nf_elem}}; parameter::Int = 3)
  Lrel = parent(B[1])
  #First, we choose the candidates
  Bnew = NfRelNSElem{nf_elem}[]
  nrep = min(parameter, absolute_degree(Lrel))
  for i = 1:length(B)
    push!(Bnew, B[i])
    for j = 1:nrep
      if i != j
        push!(Bnew, B[i]+B[j])
        push!(Bnew, B[i]-B[j])
      end
    end
  end
  #Now, we test for primitiveness.
  K = base_field(Lrel)
  OK = maximal_order(K)
  Zx = ZZ["x"][1]

  n = absolute_degree(Lrel)

  P, d = _find_prime(Lrel)
  p = minimum(P, copy = false)
  abs_deg = d*degree(P)
  #First, we search for elements that are primitive using block systems
  Fp = GF(p, cached = false)
  Fpx = PolynomialRing(Fp, cached = false)[1]
  F = FlintFiniteField(p, abs_deg, "w", cached = false)[1]
  Fx = PolynomialRing(F, cached = false)[1]
  rt_base_field = roots(Zx(K.pol), F)
  rt = Dict{fq, Vector{Vector{fq}}}()
  Rxy = PolynomialRing(F, ngens(Lrel), cached = false)[1]
  tmp = Fpx()
  for r in rt_base_field
    vr = Vector{Vector{fq}}()
    for f in Lrel.pol
      g = isunivariate(f)[2]
      coeff_gF = fq[]
      for i = 0:degree(g)
        nf_elem_to_gfp_fmpz_poly!(tmp, coeff(g, i))
        push!(coeff_gF, evaluate(tmp, r))
      end
      gF = Fx(coeff_gF)
      push!(vr, roots(gF))
    end
    rt[r] = vr
  end
  rt1 = Dict{fq, Vector{Vector{fq}}}()
  ind = 1
  nconjs_needed = div(n, 2)+1
  for (r, v) in rt
    rtv = Vector{Vector{fq}}()
    it = cartesian_product_iterator([1:length(v[i]) for i in 1:length(v)])
    for i in it
      push!(rtv, [v[j][i[j]] for j = 1:length(v)])
      ind += 1
      if ind > nconjs_needed
        break
      end
    end
    rt1[r] = rtv
    if ind > nconjs_needed
      break
    end
  end
  indices = Int[]
  for i = 1:length(Bnew)
    if length(vars(Bnew[i].data)) < ngens(Lrel)
      continue
    end
    if _is_primitive_via_block(Bnew[i], rt1, Rxy, tmp)
      push!(indices, i)
    end
  end
  return Bnew[indices]
end




function _is_primitive_via_block(a::NfRelNSElem{nf_elem}, rt::Dict{fq, Vector{Vector{fq}}}, Rxy, tmp)
  n = degree(parent(a))
  pol = data(a)
  conjs = Set{fq}()
  for (r, vr) in rt
    ctx = MPolyBuildCtx(Rxy)
    for (c, v) in zip(coeffs(pol), exponent_vectors(pol))
      nf_elem_to_gfp_fmpz_poly!(tmp, c)
      push_term!(ctx, evaluate(tmp, r), v)
    end
    g = finish(ctx)
    for i = 1:length(vr)
      ev = evaluate(g, vr[i])
      if ev in conjs
        return false
      end
      push!(conjs, ev)
    end
  end
  return true
end

function simplified_absolute_field(L::NfRelNS; cached = false)
  OL = maximal_order(L)
  B = lll_basis(OL)
  B1 = _sieve_primitive_elements(B)
  nrep = 3
  while isempty(B1)
    nrep += 1
    B1 = _sieve_primitive_elements(B, parameter = nrep)
  end
  a = B1[1]
  I = t2(a)
  for i = 2:min(50, length(B1))
    J = t2(B1[i])
    if J < I
      a = B1[i]
      I = J
    end
  end
  f = absolute_minpoly(a)
  @assert degree(f) == absolute_degree(L)
  K = number_field(f, check = false, cached = cached)[1]
  mp = hom(K, L, a)
  return K, mp
end

function simplified_absolute_field(L::NfRel{nf_elem}; cached::Bool = false)
  OL = maximal_order(L)
  B = lll_basis(OL)
  B1 = _sieve_primitive_elements(B)
  nrep = 4
  while isempty(B1)
    nrep += 1
    B1 = _sieve_primitive_elements(B, parameter = nrep)
  end
  a = B1[1]
  I = t2(a)
  for i = 2:min(50, length(B1))
    J = t2(B1[i])
    if J < I
      a = B1[i]
      I = J
    end
  end
  f = absolute_minpoly(a)
  @assert degree(f) == absolute_degree(L)
  K = number_field(f, check = false, cached = cached)[1]
  mp = hom(K, L, a)
  imp = inv(mp)
  return K, mp, hom(base_field(L), K,  imp(L(gen(base_field(L)))))
end