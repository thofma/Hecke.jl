export cm_types, cm_type

################################################################################
#
#  CM theory
#
################################################################################

function _isimag(x::acb)
  z = arb()
  ccall((:acb_get_real, libarb), Cvoid, (Ref{arb}, Ref{acb}), z, x)
  return iszero(z)
end

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

################################################################################
#
#  CM types
#
################################################################################

# A good reference is
# [Streng2010]: Marco Streng, Complex multiplication of abelian surfaces, 2010

mutable struct CMType
  field::AnticNumberField
  embeddings::Vector{NumFieldEmbNfAbs}

  function CMType(K::AnticNumberField, embeddings::Vector{NumFieldEmbNfAbs})
    z = new(K, embeddings)
    return z
  end
end

function cm_type(K::AnticNumberField, embeddings::Vector{NumFieldEmbNfAbs})
  @req is_cm_field(K)[1] "Field must a CM field"
  @req 2 * length(embeddings) == degree(K) "Wrong number of embeddings"
  @req all(x -> all(y -> conj(y) != x, embeddings), embeddings) "Embeddings must be pairwise non-conjugated"
  return CMType(K, embeddings)
end

Base.:(==)(f::CMType, g::CMType) = (f.field === g.field) &&
  issetequal(f.embeddings, g.embeddings)

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
  res = embedding_type(K)[]
  for E in complex_embeddings(K)
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
  cpl = filter(is_imaginary, complex_embeddings(K))
  it = cartesian_product_iterator([true, false], g)
  res = CMType[]
  for x in it
    push!(res, CMType(K, [x[i] ? cpl[i] : conj(cpl[i]) for i in 1:g]))
  end
  return res
end

function Base.:(*)(f::NfToNfMor, C::CMType)
  return CMType(domain(f), [f * E for E in C.embeddings])
end

function reflex(c::CMType)
  K = c.field
  N, KtoN = normal_closure(K)
  cind = induce(c, KtoN)
  A = automorphism_list(N)
  a = gen(N)
  cp = complex_embeddings(N)#, conjugates = false)
  P = cp[1] # lets choose one embedding of N to identify N with a subset of C
  res = embedding_type(N)[]

  for E in cind.embeddings
    b = E(a)
    _i = [ overlaps(evaluate(f(a), P), b) for f in A ]
    @assert count(_i) == 1
    i = findfirst(_i)
    f = A[i]
    finv = inv(f)
    c = evaluate(finv(a), P)
    _i = [ overlaps(c, evaluate(a, P)) for P in cp ]
    #_i = vcat([ overlaps(c, evaluate(a, P)) for P in cp ], [overlaps(c, conj(evaluate(a, P))) for P in cp])
    @assert count(_i) == 1
    for P in cp
      if overlaps(c, evaluate(a, P))
        push!(res, P)
      end
    end
  end

  cinv = CMType(N, res)
  D = cinv
  found = false

  for (k, ktoK) in subfields_normal(N)
    if degree(k) == degree(N) || !is_cm_field(k)[1]
      continue
    end
    fl, D = is_induced(cinv, ktoK)
    if fl
      found = true
      break
    end
  end
  !found && error("Something wrong")
  return D
end
