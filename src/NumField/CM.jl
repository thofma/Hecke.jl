export place, cm_types, cm_type

################################################################################
#
#  CM theory
#
################################################################################

# A primitive embedding type

# Alternatively, it could just be an Int + Bool
# With the Int referring to complex_places(K)[i]
mutable struct NumFieldEmbedding
  field::AnticNumberField
  plc::InfPlc
  isconj::Bool
end

Base.:(==)(f::NumFieldEmbedding, g::NumFieldEmbedding) = (f.plc == g.plc) && 
                                                         (f.isconj == g.isconj)

number_field(f::NumFieldEmbedding) = f.field

place(f::NumFieldEmbedding) = f.plc

function _print_acb_neatly(io, x::acb)
  if !_isimag(x)
    a = Float64(real(x))
    print(io, @sprintf "%.2f" a)
  end
  if !isreal(x)
    b = Float64(imag(x))
    if b > 0
      print(io, _isimag(x) ? "" : " + ", @sprintf("%.2f", b), " * i")
    else
      print(io, _isimag(x) ? @sprintf("%.2f", b) : " - " * @sprintf("%.2f", -b), " * i")
    end
  end
end

function _isimag(x::acb)
  z = arb()
  ccall((:acb_get_real, libarb), Cvoid, (Ref{arb}, Ref{acb}), z, x)
  return iszero(z)
end

function Base.show(io::IO, ::MIME"text/plain", f::NumFieldEmbedding)
  print(io, "Embedding of\n", number_field(f), "\n")
  print(io, "corresponding to ≈ ")
  _print_acb_neatly(io, f.isconj ? conj(place(f).r) : place(f).r)
end

function Base.show(io::IO, f::NumFieldEmbedding)
  print(io, "Embedding corresponding to ≈ ")
  _print_acb_neatly(io, f.isconj ? conj(place(f).r) : place(f).r)
end

function (f::NumFieldEmbedding)(x::nf_elem)
  @req number_field(f) === parent(x) "Element not in the domain of the embedding"
  xx = evaluate(x, place(f))
  return f.isconj ? conj(xx) : xx 
end

conj(E::NumFieldEmbedding) = NumFieldEmbedding(E.field, E.plc, !E.isconj)

function _complex_embeddings(K::AnticNumberField)
  cpls = get_attribute(K, :_complex_embeddings)
  if cpls !== nothing
    return cpls::Vector{NumFieldEmbedding}
  end
  res = NumFieldEmbedding[]
  for p in infinite_places(K)
    push!(res, NumFieldEmbedding(K, p, false))
    push!(res, NumFieldEmbedding(K, p, true))
  end
  set_attribute!(K, :_complex_embeddings => res)
  return res
end

################################################################################
#
#  Restriction
#
################################################################################

function restrict(E::NumFieldEmbedding, f::NfToNfMor)
  k = domain(f)
  @req is_cm_field(k)[1] "Subfield must be a CM field"
  kem = _complex_embeddings(k)
  a = gen(k)
  b = E(f(a))
  # This is not optimal, but guarded against precision issues
  cn = [overlaps(b, p(a)) for p in kem]
  @assert count(cn) == 1

  i = findfirst(cn)
  return kem[i]
end

################################################################################
#
#  CM types
#
################################################################################

# A good reference is
# [Streng2010]: Marco Streng, Complex multiplication of abelian surfaces, 2010

mutable struct CMType
  field::AnticNumberField
  embeddings::Vector{NumFieldEmbedding}

  function CMType(K::AnticNumberField, embeddings::Vector{NumFieldEmbedding})
    z = new(K, embeddings) 
    return z
  end
end

function cm_type(K::AnticNumberField, embeddings::Vector{NumFieldEmbedding})
  @req is_cm_field(K)[1] "Field must a CM field"
  @req 2 * length(embeddings) == degree(K) "Wrong number of embeddings"
  @req length(unique(map(x -> x.plc, embeddings))) == div(degree(K), 2) "Embeddings must be pairwise non-conjugated"
  return CMType(K, embeddings)
end

Base.:(==)(f::CMType, g::CMType) = (f.field === g.field) &&
                                      f.embeddings == g.embeddings

number_field(C::CMType) = C.field

embeddings(C::CMType) = C.embeddings

################################################################################
#
#  Induction
#
################################################################################

function induce(C::CMType, f::NfToNfMor)
  @assert C.field == domain(f)
  K = codomain(f)
  res = NumFieldEmbedding[]
  for E in _complex_embeddings(K)
    e = restrict(E, f)
    if e in C.embeddings
      push!(res, E)
    end
  end
  return CMType(K, res)
end

function is_induced(C::CMType, f::NfToNfMor)
  k = domain(f)
  fl, _ = Hecke.is_cm_field(k)
  for D in cm_types(k)
    if induce(D, f) == C
      return true, D
    end
  end
  return false, C
end

function is_primitive(C::CMType)
  for (k, ktoK) in subfields(C.field)
    if degree(k) == degree(C.field) || !is_cm_field(k)[1]
      continue
    end
    if is_induced(C, ktoK)[1]
      return false
    end
  end
  return true
end

function cm_types(K::AnticNumberField)
  fl, _ = is_cm_field(K)
  @assert fl
  g = div(degree(K), 2)
  cpl = complex_places(K)
  it = cartesian_product_iterator([true, false], g)
  res = CMType[]
  for x in it
    push!(res, CMType(K, [NumFieldEmbedding(K, cpl[i], x[i]) for i in 1:g]))
  end
  return res
end

function Base.:(*)(f::NfToNfMor, E::NumFieldEmbedding)
  k = domain(f)
  @assert k === codomain(f)
  @assert k === E.field
  a = gen(k)
  b = E(f(a))
  kplc = complex_places(k)
  for p in kplc
    if overlaps(b, evaluate(a, p))
      return NumFieldEmbedding(k, p, false)
    elseif overlaps(b, conj(evaluate(a, p)))
      return NumFieldEmbedding(k, p, true)
    end
  end
end

function Base.:(*)(f::NfToNfMor, C::CMType)
  return CMType(domain(f), [f * E for E in C.embeddings])
end

function reflex(c::CMType)
  K = c.field
  N, KtoN = normal_closure(K)
  cind = induce(c, KtoN)
  A = automorphisms(N)
  a = gen(N)
  cp = complex_places(N)
  P = cp[1] # lets one place of N to identify N with a subset of C
  res = NumFieldEmbedding[]

  for E in cind.embeddings
    b = E(a)
    _i = [ overlaps(evaluate(f(a), P), b) for f in A ]
    @assert count(_i) == 1
    i = findfirst(_i)
    f = A[i]
    finv = inv(f)
    c = evaluate(finv(a), P)
    _i = vcat([ overlaps(c, evaluate(a, P)) for P in cp ], [overlaps(c, conj(evaluate(a, P))) for P in cp])
    @assert count(_i) == 1
    for P in cp
      if overlaps(c, evaluate(a, P))
        push!(res, NumFieldEmbedding(N, P, false))
      elseif overlaps(c, conj(evaluate(a, P)))
        push!(res, NumFieldEmbedding(N, P, true))
      end
    end
  end
  cinv = CMType(N, res)

  for (k, ktoK) in subfields_normal(N)
    if degree(k) == degree(N) || !is_cm_field(k)[1]
      continue
    end
    fl, D = is_induced(cinv, ktoK)
    if fl
      return D
    end
  end
end
