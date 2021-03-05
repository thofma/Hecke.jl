################################################################################
#
#  Simplify
#
################################################################################

function simplify(K::NfRel; cached::Bool = true, prec::Int = 100)
  Kabs, mK, mk = absolute_field(K, cached = false)
  OK = maximal_order(K)
  B = lll_basis(OK)
  B1 = _sieve_primitive_elements(B)
  i = 6
  while isempty(B1)
    B1 = _sieve_primitive_elements(B, parameter = i)
    i += 3
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
  f = minpoly(a)
  @assert degree(f) == degree(K)
  Ks = number_field(f, cached = cached, check = false)[1]
  mKs = hom(Ks, K, a)
  return Ks, mKs
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


function _is_primitive_via_block(a::NfRelElem{nf_elem}, rt::Dict{fq, Vector{fq}}, Fx, tmp::gfp_fmpz_poly)
  n = degree(parent(a))
  pol = data(a)
  conjs = Set{fq}()
  for (r, vr) in rt
    coeffs = Vector{fq}(undef, degree(pol)+1)
    for i = 0:degree(pol)
      nf_elem_to_gfp_fmpz_poly!(tmp, coeff(pol, i))
      coeffs[i+1] = evaluate(tmp, r)
    end
    g = Fx(coeffs)
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

function _find_prime(L::NfRel{nf_elem})
  p = 2^10
  K = base_field(L)
  OK = maximal_order(K)
  OL = maximal_order(L)

  n_attempts = max(5, min(degree(L), 10))
  candidates = Vector{Tuple{Int, Int}}(undef, n_attempts)
  i = 1
  f = L.pol
  threshold = degree(f)^2
  den = lcm(fmpz[denominator(coeff(f, i)) for i = 0:degree(f)])
  while i < n_attempts+1
    p = next_prime(p)
    if isindex_divisor(OK, p) || divisible(absolute_discriminant(OL), p) || divisible(den, p)
      continue
    end
    lp = prime_decomposition(OK, p)
    P = lp[1][1]
    F, mF = ResidueField(OK, P)
    mF1 = extend(mF, K)
    fF = map_coeffs(mF1, f)
    if degree(fF) != degree(f) || !issquarefree(fF)
      continue
    end
    FS = factor_shape(fF)
    d = lcm(Int[x for (x, v) in FS])*degree(P)
    acceptable = true
    for j = 2:length(lp)
      Q = lp[j][1]
      F2, mF2 = ResidueField(OK, Q)
      mF3 = extend(mF2, K)
      fF2 = map_coeffs(mF3, f)
      if degree(fF2) != degree(f) || !issquarefree(fF2)0
        break
      end
      FS = factor_shape(fF2)
      d1 = lcm(Int[x for (x, v) in FS])
      d = lcm(d, d1*degree(Q))
    end
    if acceptable && d < threshold
      candidates[i] = (p, d)
      i += 1
    end
  end
  
  res = candidates[1]
  for j = 2:n_attempts
    if candidates[j][2] < res[2]
      res = candidates[j]
    end
  end
  return res[1], res[2]
end


function _sieve_primitive_elements(B::Vector{NfRelElem{nf_elem}}; parameter::Int = 3)
  Lrel = parent(B[1])
  n = absolute_degree(Lrel)
  #First, we choose the candidates
  Bnew = NfRelElem{nf_elem}[]
  nrep = parameter
  if n < parameter
    nrep = n
  end
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

  pint, d = _find_prime(Lrel)
  p = fmpz(pint)
  abs_deg = d
  #First, we search for elements that are primitive using block systems
  Fp = GF(p, cached = false)
  Fpx = PolynomialRing(Fp, cached = false)[1]
  F = FlintFiniteField(p, abs_deg, "w", cached = false)[1]
  Fx = PolynomialRing(F, cached = false)[1]
  rt_base_field = roots(Zx(K.pol), F)
  tmp = Fpx()
  g = Lrel.pol
  rt = Dict{fq, Vector{fq}}()
  nroots = 0
  roots_needed = div(n, 2)+1
  for r in rt_base_field
    coeff_gF = fq[]
    for i = 0:degree(g)
      nf_elem_to_gfp_fmpz_poly!(tmp, coeff(g, i))
      push!(coeff_gF, evaluate(tmp, r))
    end
    gF = Fx(coeff_gF)
    rt[r] = roots(gF)
    nroots += length(roots(gF))
    if nroots >= roots_needed
      break
    end
  end
  indices = Int[]
  for i = 1:length(Bnew)
    if _is_primitive_via_block(Bnew[i], rt, Fx, tmp)
      push!(indices, i)
    end
  end
  return Bnew[indices]

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
    it = cartesian_product_iterator([1:length(v[i]) for i in 1:length(v)], inplace = true)
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

function _find_short_primitive_element(OL::NfRelOrd)
  L = nf(OL)
  K = base_field(L)
  OK = maximal_order(K)
  Zx = ZZ["x"][1]

  n = absolute_degree(L)

  #First, I set up the "block system" machine to detect primitiveness
  P, d = _find_prime(L)
  p = minimum(P, copy = false)
  abs_deg = d*degree(P)
  Fp = GF(p, cached = false)
  Fpx = PolynomialRing(Fp, cached = false)[1]
  F = FlintFiniteField(p, abs_deg, "w", cached = false)[1]
  Fx = PolynomialRing(F, cached = false)[1]
  rt_base_field = roots(Zx(K.pol), F)
  rt = Dict{fq, Vector{Vector{fq}}}()
  Rxy = PolynomialRing(F, ngens(L), cached = false)[1]
  tmp = Fpx()
  for r in rt_base_field
    vr = Vector{Vector{fq}}()
    for f in L.pol
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
    it = cartesian_product_iterator([1:length(v[i]) for i in 1:length(v)], inplace = true)
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
  
  #Now, lattice enumeration
  B = lll_basis(OL)
  ind = 0
  I = arb()
  for j = 1:length(B)
    if _is_primitive_via_block(B[j], rt1, Rxy, tmp)
      if iszero(ind)
        ind = j
        I = t2(B[j])
      else
        J = t2(B[j])
        if J < I
          I = J
          ind = j
        end
      end
    end
  end
  all_a = NfRelNSElem{nf_elem}[absolute_primitive_element(L), B[ind]]
  prec = 100 + 25*div(absolute_degree(L), 3)
  old = precision(BigFloat)
  setprecision(BigFloat, prec)
  
  M = minkowski_gram_mat_scaled(B, prec)
  G = FakeFmpqMat(minkowski_gram_mat_scaled(B, prec), fmpz(2)^prec)
  E = enum_ctx_from_gram_canonical_simplify(G)
  while true
    try
      if E.C[end] + 0.0001 == E.C[end]  # very very crude...
        prec *= 2
        continue
      end
      break
    catch e
      if isa(e, InexactError) || isa(e, LowPrecisionLLL) || isa(e, LowPrecisionCholesky)
        prec *= 2
        continue
      end
      rethrow(e)
    end
    setprecision(BigFloat, prec)
    G = FakeFmpqMat(minkowski_gram_mat_scaled(B, prec), fmpz(2)^prec)
    E = enum_ctx_from_gram_canonical_simplify(G)
  end
  l = zeros(FlintZZ, n)
  l[ind] = 1
  
  scale = 1.0
  enum_ctx_start(E, matrix(FlintZZ, 1, n, l), eps = 1.01)
  
    
  la = absolute_degree(L)*BigFloat(E.t_den^2)
  Ec = BigFloat(E.c//E.d)
  eps = BigFloat(E.d)^(1//2)
  found_pe = false
    
  while !found_pe
    count = 0
    while enum_ctx_next(E)
      count += 1
      if count > 100
        if found_pe
          break
        else
          count = 0
        end
      end
      M = E.x
      q = dot(B, fmpz[M[1, j] for j = 1:n])
      if !_is_primitive_via_block(q, rt1, Rxy, tmp)
        continue
      end
      found_pe = true
      lq = Ec - (E.l[1] - E.C[1, 1]*(BigFloat(E.x[1,1]) + E.tail[1])^2) 
      if lq < la + eps
        if lq > la - eps
          push!(all_a, q)
        else
          a = q
          all_a = nf_elem[a]
          if lq/la < 0.8
            enum_ctx_start(E, E.x, eps = 1.01) 
            Ec = BigFloat(E.c//E.d)
          end
          la = lq
        end
      end
    end
    scale *= 2
    enum_ctx_start(E, matrix(FlintZZ, 1, n, l), eps = scale)
    Ec = BigFloat(E.c//E.d)
  end
  setprecision(BigFloat, old)

  a = all_a[1]
  I = t2(a)
  for i = 2:length(all_a)
    J = t2(all_a[i])
    if J < I
      a = all_a[i]
      I = J
    end
  end
  need_to_simplify = (a == all_a[1])
  return a, need_to_simplify
end

function enum_ctx_from_gram_canonical_simplify(G::FakeFmpqMat)
  E = enum_ctx{Int, BigFloat, BigFloat}()
  E.G = numerator(G)
  n = nrows(G)
  E.n = n 
  E.limit = nrows(G)
  E.d = denominator(G)
  E.C = pseudo_cholesky(E.G, denominator(G), TC = BigFloat, limit = E.limit)
  E.x = zero_matrix(FlintZZ, 1, n) #coeffs limit+1:n are going to be zero, always
  E.L = Vector{BigFloat}(undef, E.limit) #lower and
  E.U = Vector{BigFloat}(undef, E.limit) #upper bounds for the coordinates
  E.t_den = fmpz(1)
  E.t = identity_matrix(FlintZZ, n)

  E.l = Vector{BigFloat}(undef, E.limit) #current length
  E.tail = Vector{BigFloat}(undef, E.limit)
  d = fmpz(ceil(abs(prod(BigFloat[BigFloat(E.C[i,i]) for i=1:E.limit]))))
  ## but we don't want to overshoot too much the length of the last
  ## basis element.
  b = min((root(d, E.limit)+1)*E.limit * E.d, E.G[E.limit, E.limit]*E.limit)
  enum_ctx_start(E, b)
  return E
end

function simplified_absolute_field(L::NfRelNS; cached = false)
  OL = maximal_order(L)
  a, need_to_simplify = _find_short_primitive_element(OL)
  f = absolute_minpoly(a)
  @assert degree(f) == absolute_degree(L)
  K = number_field(f, check = false, cached = cached)[1]
  mp = hom(K, L, a)
  if need_to_simplify
    K, mK = simplify(K, cached = false, save_LLL_basis = false)
    mp = mK*mp
  end
  return K, mp
end

  



function simplified_absolute_field(L::NfRel; cached::Bool = false)
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
