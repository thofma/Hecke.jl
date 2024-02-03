function signature(L::RelNonSimpleNumField)
  c = get_attribute(L, :signature)
  if c isa Tuple{Int, Int}
    return c::Tuple{Int, Int}
  end
  K = base_field(L)
  Kx, x = polynomial_ring(K, cached = false)
  rlp = real_embeddings(K)
  # For each real embedding of K, we look how many real embeddings of the components there are and multiply
  v = Int[1 for i in 1:length(rlp)]
  for i in 1:length(L.pol)
    fi = to_univariate(Kx, L.pol[i])
    for j in 1:length(rlp)
      v[j] = v[j] * n_real_roots(fi, rlp[j])
    end
  end

  r = sum(v)
  d = absolute_degree(L)
  s = div(d - r, 2)
  set_attribute!(L, :signature => (r, s))
  return r, s
end

function conjugates_arb(a::RelNonSimpleNumFieldElem{T}, prec::Int = 32) where {T}
  # This is very slow.

  f = data(a)
  wprec = prec
  L = parent(a)
  res = Vector{AcbFieldElem}(undef, absolute_degree(L))
  found = false
  K = base_field(L)
  plcK = complex_embeddings(K, conjugates = false)
  pols = Vector{Generic.MPoly{AcbFieldElem}}(undef, length(plcK))
  r, s = signature(L)
  while !found
    found = true
    data = _conjugates_data(L, wprec)
    prec1 = precision(parent(data[1][2][1]))
    for i = 1:length(data)
      for j = 1:length(data[i][2])
        prec1 = max(prec1, precision(parent(data[i][2][j])))
      end
    end
    CC = AcbField(prec1, cached = false)
    CCy, y = polynomial_ring(CC, ngens(L), cached = false)
    for i = 1:length(plcK)
      pols[_absolute_index(plcK[i])] = map_coefficients(x -> evaluate(x, plcK[i], wprec), f, parent = CCy)
    end
    ind = 1
    for (p, pt) in data
      fatp = pols[_absolute_index(p)]

      for c in fatp.coeffs
        c.parent = CC
      end

      for i in 1:ngens(L)
        pt[i].parent = CC
      end

      o = evaluate(fatp, pt)
      if !radiuslttwopower(o, -prec)
        wprec = 2 * wprec
        found = false
        break
      end
      if ind <= r
        res[ind] = o
      else
        res[ind] = o
        res[ind + s] = conj(o)
      end
      ind += 1
    end
  end
  return res
end

################################################################################
#
#  Conjugates data
#
################################################################################

function _conjugates_data(L::RelNonSimpleNumField{T}, p::Int) where T
  cd = get_attribute(L, :conjugates_data)
  if cd === nothing
    D = Dict{Int, Vector{Tuple{embedding_type(base_field(L)), Vector{AcbFieldElem}}}}()
    res = __conjugates_data(L, p)
    D[p] = res
    set_attribute!(L, :conjugates_data => D)
    return res
  end
  cd::Dict{Int, Vector{Tuple{embedding_type(base_field(L)), Vector{AcbFieldElem}}}}
  if haskey(cd, p)
    res = cd[p]::Vector{Tuple{embedding_type(base_field(L)), Vector{AcbFieldElem}}}
    return res
  end
  res = __conjugates_data(L, p)
  cd[p] = res
  return res
end

function __conjugates_data(L::RelNonSimpleNumField{T}, p::Int) where T
  data = [_conjugates_data(component(L, j)[1], p) for j = 1:ngens(L)]
  plcs = complex_embeddings(base_field(L), conjugates = false)
  r, s = signature(L)
  res = Vector{Tuple{embedding_type(base_field(L)), Vector{AcbFieldElem}}}(undef, r+s)
  r_cnt = 0
  c_cnt = 0
  for P in plcs
    datas = [x for y in data for x in y if x[1] == P]
    if isreal(P)
      ind_real, ind_complex = enumerate_conj_prim_rel(datas)
      for y in ind_real
        r_cnt += 1
        res[r_cnt] = (P, AcbFieldElem[datas[j][2][y[j]] for j = 1:length(y)])
      end
      for y in ind_complex
        c_cnt += 1
        res[r + c_cnt] = (P, AcbFieldElem[datas[j][2][y[j]] for j = 1:length(y)])
      end
    else
      it = cartesian_product_iterator([1:length(x[2]) for x in datas], inplace = true)
      for y in it
        c_cnt += 1
        res[r + c_cnt] = (P, AcbFieldElem[datas[j][2][y[j]] for j = 1:length(y)])
      end
    end
  end
  return res
end

function enumerate_conj_prim_rel(v::Vector)
  indices = collect(cartesian_product_iterator([1:length(v[i][2]) for i in 1:length(v)], inplace = false))
  #I have the indices, now I need to order them.
  complex_indices = Int[]
  for i = 1:length(v)
    if !isreal(v[i][1])
      push!(complex_indices, 1)
      continue
    end
    indc = length(v[i][3])+1
    push!(complex_indices, indc)
  end
  real_combinations = Int[]
  for i = 1:length(indices)
    isreal_plc = true
    for j = 1:length(indices[i])
      if indices[i][j] >= complex_indices[j]
        isreal_plc = false
        break
      end
    end
    if isreal_plc
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
      found = _is_complex_conj_rel(res_complex[t], s, ind_complex, v)
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

function _is_complex_conj_rel(v::Vector{Int}, w::Vector{Int}, pos::Vector, roots::Vector)
  i = 1
  for x in v
    if i in pos
      if v[i] <= length(roots[i][3])
        return false
      end
      lc = length(roots[i][4])
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
