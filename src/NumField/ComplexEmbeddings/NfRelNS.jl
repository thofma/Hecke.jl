mutable struct RelNonSimpleNumFieldEmbedding{S, U} <: NumFieldEmb{S}
  field::S             # Number field
  base_field_emb::U    # Embedding of base field
  data::Vector{AcbFieldElem}    # For each L = K[x]/(g_i) component a root p(g_i)
  absolute_index::Int  # Bookkeeping
  isreal::Bool         # Whether the embedding is real
  conjugate::Int       # The absolute index of the conjugate

  function RelNonSimpleNumFieldEmbedding{S, U}(field::S,
                                 base_field_emb::U,
                                 data::Vector{AcbFieldElem},
                                 absolute_index::Int,
                                 isreal::Bool,
                                 conjugate::Int) where {S,  U}
    z = new{S, U}(field, base_field_emb, data,
                  absolute_index, isreal, conjugate)
  end
end

function embedding_type(::Type{RelNonSimpleNumField{T}}) where {T}
  return RelNonSimpleNumFieldEmbedding{RelNonSimpleNumField{T}, embedding_type(parent_type(T))}
end

embedding_type(L::RelNonSimpleNumField{T}) where {T} = embedding_type(RelNonSimpleNumField{T})

isreal(P::RelNonSimpleNumFieldEmbedding) = P.isreal

is_imaginary(P::RelNonSimpleNumFieldEmbedding) = !P.isreal

number_field(f::RelNonSimpleNumFieldEmbedding) = f.field

_absolute_index(P::RelNonSimpleNumFieldEmbedding) = P.absolute_index

function conj(f::RelNonSimpleNumFieldEmbedding)
  return complex_embeddings(number_field(f))[f.conjugate]
end

function Base.show(io::IO, ::MIME"text/plain", f::RelNonSimpleNumFieldEmbedding)
  print(io, "Embedding of\n")
  println(io, number_field(f))
  print(io, "extending the \n", f.base_field_emb, "\n")
  print(io, "with roots ")
  print(io, "[ ")
  for i in 1:length(f.data)
    _print_acb_neatly(io, f.data[i])
    if i < length(f.data)
      print(io, ", ")
    end
  end
  print(io, "]")
end

function Base.show(io::IO, f::RelNonSimpleNumFieldEmbedding)
  print(io, "Embedding corresponding to (", f.base_field_emb, ") and ")
  print(io, "[ ")
  for i in 1:length(f.data)
    _print_acb_neatly(io, f.data[i])
    if i < length(f.data)
      print(io, ", ")
    end
  end
  print(io, "]")
end

function complex_embeddings(L::RelNonSimpleNumField{T}; conjugates::Bool = true) where {T}
  res = get_attribute!(L, :complex_embeddings) do
    return _complex_embeddings(L)
  end::Vector{embedding_type(L)}
  if conjugates
    return res
  else
    r, s = signature(L)
    return res[1:r + s]
  end
end

function _complex_embeddings(L::RelNonSimpleNumField{T}) where {T}
  r, s = signature(L)
  K = base_field(L)
  S = embedding_type(L)
  data = _conjugates_data_new(L, 32)
  ind = 1
  res = Vector{embedding_type(L)}(undef, r + 2*s)
  for (p, rts) in data
    res[ind] = S(L, p, rts, ind, ind <= r, ind > r ? ind + s : ind)
    if ind > r
      res[ind + s] = S(L, conj(p), conj.(rts), ind + s, false, ind)
    end
    ind += 1
  end
  return res
end

function (g::RelNonSimpleNumFieldEmbedding)(a::RelNonSimpleNumFieldElem, prec::Int = 32)
  # This is very slow.
  @req number_field(g) === parent(a) "Parent mismatch"
  f = data(a)
  wprec = prec
  L = parent(a)
  r, s = signature(L)
  # We only store data fo non-conjugated complex_embeddings
  if _absolute_index(g) > r + s
    return conj(conj(g)(a, prec))
  end
  K = base_field(L)
  plcK = complex_embeddings(K)
  pols = Vector{Generic.MPoly{AcbFieldElem}}(undef, length(plcK))
  r, s = signature(L)

  while true
    data = _conjugates_data_new(L, wprec)[_absolute_index(g)]
    p = data[1]
    prec1 = precision(parent(data[2][1]))
    for j = 1:length(data[2])
      prec1 = max(prec1, precision(parent(data[2][j])))
    end
    CC = AcbField(prec1, cached = false)
    CCy, y = polynomial_ring(CC, ngens(L), cached = false)
    fatp = map_coefficients(let wprec = wprec; x -> evaluate(x, data[1], wprec) end, f, parent = CCy)
    pt = data[2]
    for c in fatp.coeffs
      c.parent = CC
    end
    for i in 1:ngens(L)
      pt[i].parent = CC
    end

    o = evaluate(fatp, pt)
    if radiuslttwopower(o, -prec)
      return expand!(o, -prec)
    end
    wprec = 2 * wprec
  end
end

evaluate(a::RelNonSimpleNumFieldElem, g::RelNonSimpleNumFieldEmbedding, prec::Int = 32) = g(a, prec)

################################################################################
#
#  Conjugates data
#
################################################################################

function _conjugates_data_new(L::RelNonSimpleNumField{T}, p::Int) where T
  cd = get_attribute(L, :conjugates_data_new)
  if cd === nothing
    D = Dict{Int, Vector{Tuple{embedding_type(base_field(L)), Vector{AcbFieldElem}}}}()
    res = __conjugates_data_new(L, p)
    D[p] = res
    set_attribute!(L, :conjugates_data_new => D)
    return res
  end
  cd::Dict{Int, Vector{Tuple{embedding_type(base_field(L)), Vector{AcbFieldElem}}}}
  if haskey(cd, p)
    res = cd[p]::Vector{Tuple{embedding_type(base_field(L)), Vector{AcbFieldElem}}}
    return res
  end
  res = __conjugates_data_new(L, p)
  cd[p] = res
  return res::Vector{Tuple{embedding_type(base_field(L)), Vector{AcbFieldElem}}}
end

function __conjugates_data_new(L::RelNonSimpleNumField{T}, p::Int) where T
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

################################################################################
#
#  Restrict
#
################################################################################

function restrict(f::RelNonSimpleNumFieldEmbedding, K::NumField)
  if K === number_field(f)
    return f
  end
  @req _appears_as_base_field(K, number_field(f)) "Number field is not a base field"
  if K === base_field(number_field(f))
    return f.base_field_emb
  else
    return restrict(f.base_field_emb, K)
  end
end

################################################################################
#
#  Restrict from bigger field
#
################################################################################

function restrict(e::NumFieldEmb, f::NumFieldHom{<: RelNonSimpleNumField, <: Any, <: Any})
  @req number_field(e) === codomain(f) "Number fields do not match"
  L = domain(f)
  emb = complex_embeddings(L)
  # I need to find the embedding of the base_field of L
  K = base_field(L)
  # This is the natural map K -> L
  KtoL = hom(K, L)
  res_base_field = restrict(e, KtoL * f)
  cn = [ all(overlaps.(ee.data, e.(f.(gens(L))))) && ee.base_field_emb === res_base_field for ee in emb]
  @assert count(cn) == 1
  i = findfirst(cn)
  return emb[i]
end

################################################################################
#
#  Creation of complex embedding
#
################################################################################

function complex_embedding(K::RelNonSimpleNumField, e::NumFieldEmb, r::Vector{AcbFieldElem})
  @req number_field(e) === base_field(K) "Embedding must be embedding of base field"
  embs = complex_embeddings(K)
  cnt = 0
  local eee::embedding_type(K)
  for ee in embs
    if ee.base_field_emb != e
      continue
    end
    if all(x -> overlaps(x[1], x[2]), zip(ee.data, r))
      eee = ee
      cnt += 1
    end
  end
  cnt != 1 && error("Something wrong")
  return eee
end
