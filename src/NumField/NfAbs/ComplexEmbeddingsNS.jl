mutable struct NumFieldEmbNfAbsNS <: NumFieldEmb{NfAbsNS}
  field::NfAbsNS
  index::Vector{Int}
  absolute_index::Int
  isreal::Bool
  roots::Vector{acb}
  conjugate::Int
end

_absolute_index(P::NumFieldEmbNfAbsNS) = P.absolute_index

number_field(P::NumFieldEmbNfAbsNS) = P.field

embedding_type(::Type{NfAbsNS}) = NumFieldEmbNfAbsNS

embedding_type(::NfAbsNS) = NumFieldEmbNfAbsNS

isreal(P::NumFieldEmbNfAbsNS) = P.isreal

is_imaginary(P::NumFieldEmbNfAbsNS) = !P.isreal

conj(P::NumFieldEmbNfAbsNS) = complex_embeddings(number_field(P))[P.conjugate]

function complex_embeddings(K::NfAbsNS; conjugates::Bool = true)
  emb = get_attribute!(K, :complex_embeddings) do
    _complex_embeddings(K)
  end::Vector{NumFieldEmbNfAbsNS}
  if conjugates
    return emb
  else
    r, s = signature(K)
    return emb[1:r + s]
  end
end

function _complex_embeddings(K::NfAbsNS)
  c = conjugate_data_arb_roots(K, 32, copy = false)

  r, s = signature(K)
  res = Vector{NumFieldEmbNfAbsNS}(undef, degree(K))

  l = ngens(K)

  j = 1

  for v in c[2]
    res[j] = NumFieldEmbNfAbsNS(K, v, j, true, acb[c[1][i].roots[v[i]] for i in 1:l], j)
    j += 1
  end

  for v in c[3]
    res[j] = NumFieldEmbNfAbsNS(K, v, j, false, acb[c[1][i].roots[v[i]] for i in 1:l], j + s)
    res[j + s] = NumFieldEmbNfAbsNS(K, v, j + s, false, acb[conj(c[1][i].roots[v[i]]) for i in 1:l], j)
    j += 1
  end

  return res
end

function Base.show(io::IO, ::MIME"text/plain", f::NumFieldEmbNfAbsNS)
  print(io, "Embedding of\n")
  print(IOContext(io, :compact => true), number_field(f))
  print(io, "\n")
  print(io, "with roots ≈ ")
  print(io, "[ ")
  for i in 1:length(f.roots)
    _print_acb_neatly(io, f.roots[i])
    if i < length(f.roots)
      print(io, ", ")
    end
  end
  print(io, "]")
end

function Base.show(io::IO, f::NumFieldEmbNfAbsNS)
  print(io, "Embedding corresponding to ≈ ")
  print(io, "[ ")
  for i in 1:length(f.roots)
    _print_acb_neatly(io, f.roots[i])
    if i < length(f.roots)
      print(io, ", ")
    end
  end
  print(io, "]")
end

function (f::NumFieldEmbNfAbsNS)(a::NfAbsNSElem, prec::Int = 32)
  K = parent(a)
  wprec = prec
  pol_a = data(a)
  r, s = signature(K)
  i = _absolute_index(f)
  if i > r + s
    return conj(conj(f)(a, prec))
  end
  while true
    conjs, ind_real, ind_complex = conjugate_data_arb_roots(K, wprec)
    if i <= r
      res = _evaluate(pol_a, acb[conjs[j].roots[ind_real[i][j]] for j = 1:ngens(K)])
    else
      i = i - r
      ev = acb[conjs[j].roots[ind_complex[i][j]] for j = 1:ngens(K)]
      res = _evaluate(pol_a, ev)
    end
    if !isfinite(res) || !radiuslttwopower(res, -prec)
      wprec = 2 * wprec
    else
      return res
    end
  end
end

function evaluate(a::NfAbsNSElem, P::NumFieldEmbNfAbsNS, prec::Int)
  return P(a, prec)
end

function restrict(e::NumFieldEmb, f::NumFieldMor{<: NfAbsNS, <: Any, <: Any})
  @req number_field(e) === codomain(f) "Number fields do not match"
  L = domain(f)
  emb = complex_embeddings(L)
  cn = Bool[ all(overlaps.(ee.roots, e.(f.(gens(L))))) for ee in emb]
  @assert count(cn) == 1
  i = findfirst(cn)
  return emb[i]
end

################################################################################
#
#  Easier creation of embeddings
#
################################################################################

function _find_nearest_embedding(K::NfAbsNS, x::Vector{<:Union{BigFloat, Float64}})
  r = real_embeddings(K)
  l = length(K.pol)
  @assert length(x) == l
  gK = gens(K)
  diffs = [[e(gK[i]) - x[i] for i in 1:l] for e in r]
  t = [maximum([abs(w) for w in z]) for z in diffs]
  _, i = findmin(t)
  return r[i]
end

function real_embedding(K::NfAbsNS, x::Vector)
  return _find_nearest_embedding(K, x)
end

function _find_nearest_embedding(K::NfAbsNS, x::Vector{<:Tuple})
  r = real_embeddings(K)
  p = 32
  gK = gens(K)
  fls = [all(_is_contained_in_interval(real(i(gK[j], p)), x[j]) for j in 1:length(gK)) for i in r]
  while count(fls) != 1
    p = 2 * p
    fls = [all(_is_contained_in_interval(real(i(gK[j], p)), x[j]) for j in 1:length(gK)) for i in r]
    if count(fls) > 1
      possible = [[ Float64(real(x)) for x in e.roots] for e in r]
      s = IOBuffer()
      for k in 1:length(possible)
        for i in 1:length(possible[k])
          @printf s "%.2f" possible[k][i]
          if i < length(possible[k])
            print(s, ", ")
          end
        end
        if k < length(possible)
          print(s, "\n")
        end
      end
      ss = String(take!(s))
      error("""Interval contains more than one root. Possible roots are:
            $ss
            """)
    end
    p > 2^8 && error("Something wrong!")
  end
  i = findfirst(fls)
  @assert i !== nothing
  return r[i]
end

function real_embedding(K::NfAbsNS, x::Vector{<:Tuple})
  return _find_nearest_embedding(K, x)
end
