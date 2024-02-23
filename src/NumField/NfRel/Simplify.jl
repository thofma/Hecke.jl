################################################################################
#
#  Simplify
#
################################################################################

function simplify(K::RelSimpleNumField; cached::Bool = true, prec::Int = 100)
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
    is_primitive = true
    for i = 2:k+1
      for j = 1:i-1
        if overlaps(c[i], c[j])
          is_primitive = false
          break
        end
      end
      if !is_primitive
        break
      end
    end
    if is_primitive
      push!(B1, x)
    end
  end
  return B1
end


function _is_primitive_via_block(a::RelSimpleNumFieldElem{AbsSimpleNumFieldElem}, rt::Dict{FqPolyRepFieldElem, Vector{FqPolyRepFieldElem}}, Fx, tmp::FpPolyRingElem)
  if iszero(a)
    return false
  end
  n = degree(parent(a))
  pol = data(a)
  conjs = Set{FqPolyRepFieldElem}()
  for (r, vr) in rt
    coeffs = Vector{FqPolyRepFieldElem}(undef, degree(pol)+1)
    for i = 0:degree(pol)
      Nemo.nf_elem_to_gfp_fmpz_poly!(tmp, coeff(pol, i))
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

function _find_prime(L::RelSimpleNumField{AbsSimpleNumFieldElem})
  p = 2^10
  K = base_field(L)
  OK = maximal_order(K)
  OL = maximal_order(L)

  n_attempts = max(5, min(degree(L), 10))
  candidates = Vector{Tuple{Int, Int}}(undef, n_attempts)
  i = 1
  f = L.pol
  threshold = degree(f)^2
  den = lcm(ZZRingElem[denominator(coeff(f, i)) for i = 0:degree(f)])
  while i < n_attempts+1
    p = next_prime(p)
    if is_index_divisor(OK, p) || is_divisible_by(absolute_discriminant(OL), p) || is_divisible_by(den, p)
      continue
    end
    lp = prime_decomposition(OK, p)
    P = lp[1][1]
    F, mF = residue_field(OK, P)
    mF1 = extend(mF, K)
    fF = map_coefficients(mF1, f, cached = false)
    if degree(fF) != degree(f) || !is_squarefree(fF)
      continue
    end
    FS = factor_shape(fF)
    d = lcm(Int[x for (x, v) in FS])*degree(P)
    acceptable = true
    for j = 2:length(lp)
      Q = lp[j][1]
      F2, mF2 = residue_field(OK, Q)
      mF3 = extend(mF2, K)
      fF2 = map_coefficients(mF3, f, cached = false)
      if degree(fF2) != degree(f) || !is_squarefree(fF2)
        acceptable = false
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


function _setup_block_system(Lrel::RelSimpleNumField{AbsSimpleNumFieldElem})
  K = base_field(Lrel)
  OK = maximal_order(K)
  Zx = ZZ["x"][1]
  n = absolute_degree(Lrel)

  pint, d = _find_prime(Lrel)
  p = ZZRingElem(pint)
  abs_deg = d
  #First, we search for elements that are primitive using block systems
  Fp = Native.GF(p, cached = false)
  Fpx = polynomial_ring(Fp, cached = false)[1]
  F = Native.finite_field(p, abs_deg, "w", cached = false)[1]
  Fx = polynomial_ring(F, cached = false)[1]
  rt_base_field = roots(F, Zx(K.pol))
  tmp = Fpx()
  g = Lrel.pol
  rt = Dict{FqPolyRepFieldElem, Vector{FqPolyRepFieldElem}}()
  nroots = 0
  roots_needed = div(n, 2)+1
  for r in rt_base_field
    coeff_gF = FqPolyRepFieldElem[]
    for i = 0:degree(g)
      Nemo.nf_elem_to_gfp_fmpz_poly!(tmp, coeff(g, i))
      push!(coeff_gF, evaluate(tmp, r))
    end
    gF = Fx(coeff_gF)
    rt[r] = roots(gF)
    nroots += length(roots(gF))
    if nroots >= roots_needed
      break
    end
  end
  return rt, Fx, tmp
end


function _find_prime(L::RelNonSimpleNumField{AbsSimpleNumFieldElem})
  p = 2^10
  K = base_field(L)
  OK = maximal_order(K)
  OL = maximal_order(L)
  dL = numerator(discriminant(L, FlintQQ))

  n_attempts = min(degree(L), 10)
  candidates = Vector{Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}}(undef, n_attempts)
  i = 1
  pols = L.pol
  threshold = max(absolute_degree(L)^2, 2)
  polsR = Vector{FqPolyRingElem}(undef, length(pols))
  while i < n_attempts+1
    p = next_prime(p)
    if is_index_divisor(OK, p) || is_divisible_by(dL, p)
      continue
    end
    lp = prime_decomposition(OK, p)
    P = lp[1][1]
    @assert !is_index_divisor(OL, P)
    F, mF = residue_field(OK, P)
    mF1 = extend(mF, K)
    Fx, _ = polynomial_ring(F, "x", cached = false)
    is_proj = true
    for j = 1:length(pols)
      fF = to_univariate(Fx, map_coefficients(mF1, pols[j], cached = false))
      if degree(fF) != total_degree(pols[j]) || !is_squarefree(fF)
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
    acceptable = true
    for s = 2:length(lp)
      Q = lp[s][1]
      @assert !is_index_divisor(OL, Q)
      F, mF = residue_field(OK, Q)
      Fx, _ = polynomial_ring(F, "x", cached = false)
      mF1 = extend(mF, K)
      is_proj = true
      for j = 1:length(pols)
        fF = to_univariate(Fx, map_coefficients(mF1, pols[j], cached = false))
        if degree(fF) != total_degree(pols[j]) || !is_squarefree(fF)
          is_proj = false
          break
        end
        polsR[j] = fF
      end
      if !is_proj
        acceptable = false
        break
      end
      for j = 1:length(polsR)
        FS = factor_shape(polsR[j])
        d1 = lcm(Int[x for (x, v) in FS])*degree(Q)
        d = lcm(d, d1)
      end
    end
    if !acceptable
      continue
    end
    if d*degree(P) < threshold
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


function _setup_block_system(Lrel::RelNonSimpleNumField{AbsSimpleNumFieldElem})
  K = base_field(Lrel)
  OK = maximal_order(K)
  Zx = ZZ["x"][1]

  n = absolute_degree(Lrel)

  P, d = _find_prime(Lrel)
  p = minimum(P, copy = false)
  abs_deg = d*degree(P)
  #First, we search for elements that are primitive using block systems
  Fp = Native.GF(p, cached = false)
  Fpx = polynomial_ring(Fp, cached = false)[1]
  F = Native.finite_field(p, abs_deg, "w", cached = false)[1]
  Fx = polynomial_ring(F, cached = false)[1]
  rt_base_field = roots(F, Zx(K.pol))
  rt = Dict{FqPolyRepFieldElem, Vector{Vector{FqPolyRepFieldElem}}}()
  Rxy = polynomial_ring(F, ngens(Lrel), cached = false)[1]
  tmp = Fpx()
  Kx, _ = polynomial_ring(K, "x", cached = false)
  for r in rt_base_field
    vr = Vector{Vector{FqPolyRepFieldElem}}()
    for f in Lrel.pol
      g = to_univariate(Kx, f)
      coeff_gF = FqPolyRepFieldElem[]
      for i = 0:degree(g)
        Nemo.nf_elem_to_gfp_fmpz_poly!(tmp, coeff(g, i))
        push!(coeff_gF, evaluate(tmp, r))
      end
      gF = Fx(coeff_gF)
      push!(vr, roots(gF))
    end
    rt[r] = vr
  end
  rt1 = Dict{FqPolyRepFieldElem, Vector{Vector{FqPolyRepFieldElem}}}()
  ind = 1
  nconjs_needed = div(n, 2)+1
  for (r, v) in rt
    rtv = Vector{Vector{FqPolyRepFieldElem}}()
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
  @assert ind > nconjs_needed
  return rt1, Rxy, tmp
end

function _sieve_primitive_elements(B::Vector{T}; parameter::Int = div(absolute_degree(parent(B[1])), 2)) where T <: Union{RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}, RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}
  Lrel = parent(B[1])
  #First, we choose the candidates
  ape = absolute_primitive_element(Lrel)
  B_test = vcat(B, T[ape])
  Bnew = typeof(B)()
  nrep = min(parameter, absolute_degree(Lrel))
  for i = 1:length(B_test)
    push!(Bnew, B_test[i])
    for j = 1:nrep
      if i != j
        push!(Bnew, B_test[i]+B_test[j])
        push!(Bnew, B_test[i]-B_test[j])
      end
    end
  end
  #Now, we test for primitiveness.
  rt1, Rxy, tmp = _setup_block_system(Lrel)
  indices = Int[]
  for i = 1:length(Bnew)
    if _is_primitive_via_block(Bnew[i], rt1, Rxy, tmp)
      push!(indices, i)
    end
  end
  return Bnew[indices]
end

function _is_primitive_via_block(a::RelNonSimpleNumFieldElem{AbsSimpleNumFieldElem}, rt::Dict{FqPolyRepFieldElem, Vector{Vector{FqPolyRepFieldElem}}}, Rxy, tmp)
  if length(vars(a.data)) < ngens(parent(a))
    return false
  end
  n = degree(parent(a))
  pol = data(a)
  conjs = Set{FqPolyRepFieldElem}()
  for (r, vr) in rt
    ctx = MPolyBuildCtx(Rxy)
    for (c, v) in zip(coefficients(pol), exponent_vectors(pol))
      Nemo.nf_elem_to_gfp_fmpz_poly!(tmp, c)
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

function _find_short_primitive_element(L::RelNonSimpleNumField)
  B = lll_basis(maximal_order(L))
  parameter = div(absolute_degree(L), 2)
  B1 = _sieve_primitive_elements(B, parameter = parameter)
  while isempty(B1)
    parameter += 1
    B1 = _sieve_primitive_elements(B, parameter = parameter)
  end
  a = B1[1]
  I = t2(a)
  for i = 2:length(B1)
    J = t2(B1[i])
    if J < I
      a = B1[i]
      I = J
    end
  end
  return a
end

function simplified_absolute_field(L::RelNonSimpleNumField; cached = false)
  a = _find_short_primitive_element(L)
  f = absolute_minpoly(a)
  @assert degree(f) == absolute_degree(L)
  local K::AbsSimpleNumField
  K = number_field(f, check = false, cached = cached)[1]
  mp = hom(K, L, a)
  return K, mp
end

function simplified_absolute_field(L::RelSimpleNumField; cached::Bool = false)
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
