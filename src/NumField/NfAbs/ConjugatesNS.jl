function conjugates_data_roots(K::AbsNonSimpleNumField)
  cache = get_attribute(K, :conjugates_data_roots)
  if cache !== nothing
    return cache
  end
  pols = QQPolyRingElem[to_univariate(Globals.Qx, x) for x in K.pol]
  ctxs = acb_root_ctx[acb_root_ctx(x) for x in pols]
  set_attribute!(K, :conjugates_data_roots => ctxs)
  return ctxs
end

function conjugate_data_arb_roots(K::AbsNonSimpleNumField, p::Int; copy = true)
  cache = get_attribute(K, :conjugates_data)
  if cache !== nothing
    if haskey(cache, p)
      return cache[p]
    end
  end
  ctxs = conjugates_data_roots(K)
  acb_roots_vec = Vector{acb_roots}(undef, length(ctxs))
  for i = 1:length(ctxs)
    c = ctxs[i]
    while c.prec < p
      refine(c)
    end
    real_roots = deepcopy(c.real_roots)
    complex_roots = deepcopy(c.complex_roots)
    for z in real_roots
      expand!(z, -p)
    end
    for z in complex_roots
      expand!(z, -p)
    end
    CC = parent(c.roots[1])
    all_roots = Vector{AcbFieldElem}(undef, length(c.roots))
    for i = 1:length(real_roots)
      all_roots[i] = CC(real_roots[i])
    end
    for i = 1:length(complex_roots)
      all_roots[i+length(real_roots)] = complex_roots[i]
      all_roots[i+length(real_roots)+length(complex_roots)] = conj(complex_roots[i])
    end
    acb_roots_vec[i] = acb_roots(p, all_roots, real_roots, complex_roots)
  end
  ind_real, ind_complex = enumerate_conj_prim(acb_roots_vec)
  set_attribute!(K, :conjugates_data => Dict(p => (acb_roots_vec, ind_real, ind_complex)))
  return acb_roots_vec, ind_real, ind_complex

end

function enumerate_conj_prim(v::Vector{acb_roots})
  indices = collect(cartesian_product_iterator([1:length(v[i].roots) for i in 1:length(v)], inplace = false))
  #I have the indices, now I need to order them.
  complex_indices = Int[]
  for i = 1:length(v)
    indc = length(v[i].real_roots)+1
    push!(complex_indices, indc)
  end
  real_combinations = Int[]
  for i = 1:length(indices)
    isreal = true
    for j = 1:length(indices[i])
      if indices[i][j] >= complex_indices[j]
        isreal = false
        break
      end
    end
    if isreal
      push!(real_combinations, i)
    end
  end
  res_real = indices[real_combinations]
  res_complex = typeof(indices)()
  for i = 1:length(indices)
    if i in real_combinations
      continue
    end
    s = indices[i]
    ind_complex = Int[]
    for t = 1:length(s)
      if s[t] >= complex_indices[t]
        push!(ind_complex, t)
      end
    end
    found = false
    for t = 1:length(res_complex)
      found = _is_complex_conj(res_complex[t], s, ind_complex, v)
      if found
        break
      end
    end
    if found
      continue
    end

    push!(res_complex, indices[i])
  end
  return res_real, res_complex
end

function _is_complex_conj(v::Vector, w::Vector, pos::Vector, roots::Vector)
  i = 1
  for x in v
    if i in pos
      if v[i] <= length(roots[i].real_roots)
        return false
      end
      lc = length(roots[i].complex_roots)
      if v[i] != w[i] + lc && v[i] != w[i] - lc
        return false
      end
    elseif v[i] != w[i]
      return false
    end
    i += 1
  end
  return true
end


function conjugates_arb(a::AbsNonSimpleNumFieldElem, p::Int, work_tol::Int = p)
  K = parent(a)
  conjs, ind_real, ind_complex = conjugate_data_arb_roots(K, work_tol)
  res = Vector{AcbFieldElem}(undef, degree(K))
  pol_a = data(a)
  r, s = signature(K)
  for i = 1:r
    res[i] = _evaluate(pol_a, AcbFieldElem[conjs[j].roots[ind_real[i][j]] for j = 1:ngens(K)])
    if !isfinite(res[i]) || !radiuslttwopower(res[i], -p)
      return conjugates_arb(a, p, 2*work_tol)
    end
  end
  ind = r+1
  for i = 1:length(ind_complex)
    ev = AcbFieldElem[conjs[j].roots[ind_complex[i][j]] for j = 1:ngens(K)]
    res[ind] = _evaluate(pol_a, ev)
    if !isfinite(res[ind]) || !radiuslttwopower(res[ind], -p)
      return conjugates_arb(a, p, 2*work_tol)
    end
    res[ind+s] = conj(res[ind])
    ind += 1
  end
  return res
end

function _evaluate(f::QQMPolyRingElem, vals::Vector{AcbFieldElem})
  S = parent(vals[1])
  powers = [Dict{Int, AcbFieldElem}() for i in 1:length(vals)]
  r = AcbFieldElem[zero(S)]
  i = UInt(1)
  cvzip = zip(coefficients(f), exponent_vectors(f))
  for (c, v) in cvzip
    t = one(S)
    for j = 1:length(vals)
      exp = v[j]
      if iszero(exp)
        continue
      end
      if !haskey(powers[j], exp)
        powers[j][exp] = vals[j]^exp
      end
      mul!(t, t, powers[j][exp])
      #t = t*powers[j][exp]
    end
    push!(r, c*t)
    j = i = i + 1
    while iseven(j) && length(r) > 1
      top = pop!(r)
      r[end] = addeq!(r[end], top)
      j >>>= 1
    end
  end
  while length(r) > 1
    top = pop!(r)
    r[end] = addeq!(r[end], top)
  end
  return r[1]
end

function signature(K::AbsNonSimpleNumField)
  if K.signature[1] != -1
    return K.signature
  end
  signatures = Tuple{Int, Int}[signature(to_univariate(Globals.Qx, f)) for f in K.pol]
  r = prod(x[1] for x in signatures)
  s = div(degree(K) - r, 2)
  K.signature = (r, s)
  return (r, s)
end
