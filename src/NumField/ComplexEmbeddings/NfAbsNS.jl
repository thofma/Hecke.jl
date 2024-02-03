mutable struct AbsNonSimpleNumFieldEmbedding <: NumFieldEmb{AbsNonSimpleNumField}
  field::AbsNonSimpleNumField
  index::Vector{Int}
  absolute_index::Int
  isreal::Bool
  roots::Vector{AcbFieldElem}
  conjugate::Int
end

_absolute_index(P::AbsNonSimpleNumFieldEmbedding) = P.absolute_index

number_field(P::AbsNonSimpleNumFieldEmbedding) = P.field

embedding_type(::Type{AbsNonSimpleNumField}) = AbsNonSimpleNumFieldEmbedding

embedding_type(::AbsNonSimpleNumField) = AbsNonSimpleNumFieldEmbedding

isreal(P::AbsNonSimpleNumFieldEmbedding) = P.isreal

is_imaginary(P::AbsNonSimpleNumFieldEmbedding) = !P.isreal

conj(P::AbsNonSimpleNumFieldEmbedding) = complex_embeddings(number_field(P))[P.conjugate]

function complex_embeddings(K::AbsNonSimpleNumField; conjugates::Bool = true)
  emb = get_attribute!(K, :complex_embeddings) do
    _complex_embeddings(K)
  end::Vector{AbsNonSimpleNumFieldEmbedding}
  if conjugates
    return emb
  else
    r, s = signature(K)
    return emb[1:r + s]
  end
end

function _complex_embeddings(K::AbsNonSimpleNumField)
  c = conjugate_data_arb_roots(K, 32, copy = false)

  r, s = signature(K)
  res = Vector{AbsNonSimpleNumFieldEmbedding}(undef, degree(K))

  l = ngens(K)

  j = 1

  for v in c[2]
    res[j] = AbsNonSimpleNumFieldEmbedding(K, v, j, true, AcbFieldElem[c[1][i].roots[v[i]] for i in 1:l], j)
    j += 1
  end

  for v in c[3]
    res[j] = AbsNonSimpleNumFieldEmbedding(K, v, j, false, AcbFieldElem[c[1][i].roots[v[i]] for i in 1:l], j + s)
    res[j + s] = AbsNonSimpleNumFieldEmbedding(K, v, j + s, false, AcbFieldElem[conj(c[1][i].roots[v[i]]) for i in 1:l], j)
    j += 1
  end

  return res
end

function Base.show(io::IO, ::MIME"text/plain", f::AbsNonSimpleNumFieldEmbedding)
  io = pretty(io)
  print(io, "Complex embedding ")
  print(io, "corresponding to roots ")
  print(io, "[")
  for i in 1:length(f.roots)
    _print_acb_neatly(io, f.roots[i])
    if i < length(f.roots)
      print(io, ", ")
    end
  end
  println(io, "]")
  print(io, Indent(), "of ", Lowercase())
  Base.show(io, MIME"text/plain"(), number_field(f))
end

function Base.show(io::IO, f::AbsNonSimpleNumFieldEmbedding)
  if get(io, :supercompact, false)
    print(io, "Complex embedding of number field")
  else
    print(io, "Complex embedding corresponding to ")
    print(io, "[")
    for i in 1:length(f.roots)
      _print_acb_neatly(io, f.roots[i])
      if i < length(f.roots)
        print(io, ", ")
      end
    end
    print(io, "]")
    io = pretty(io)
    print(IOContext(io, :supercompact => true), " of ", Lowercase(), number_field(f))
  end
end

function (f::AbsNonSimpleNumFieldEmbedding)(a::AbsNonSimpleNumFieldElem, prec::Int = 32)
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
      res = _evaluate(pol_a, AcbFieldElem[conjs[j].roots[ind_real[i][j]] for j = 1:ngens(K)])
    else
      i = i - r
      ev = AcbFieldElem[conjs[j].roots[ind_complex[i][j]] for j = 1:ngens(K)]
      res = _evaluate(pol_a, ev)
    end
    if !isfinite(res) || !radiuslttwopower(res, -prec)
      wprec = 2 * wprec
    else
      return res
    end
  end
end

function evaluate(a::AbsNonSimpleNumFieldElem, P::AbsNonSimpleNumFieldEmbedding, prec::Int)
  return P(a, prec)
end

function restrict(e::NumFieldEmb, f::NumFieldHom{<: AbsNonSimpleNumField, <: Any, <: Any})
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

function _find_nearest_real_embedding(K::AbsNonSimpleNumField, x::Vector{<:Union{BigFloat, Float64}})
  r = real_embeddings(K)
  l = length(K.pol)
  @assert length(x) == l
  gK = gens(K)
  diffs = [[e(gK[i]) - x[i] for i in 1:l] for e in r]
  t = [maximum([abs(w) for w in z]) for z in diffs]
  _, i = findmin(t)
  return r[i]
end

function real_embedding(K::AbsNonSimpleNumField, x::Vector)
  return _find_nearest_real_embedding(K, x)
end

function _find_nearest_real_embedding(K::AbsNonSimpleNumField, x::Vector{<:Tuple})
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

function real_embedding(K::AbsNonSimpleNumField, x::Vector{<:Tuple})
  return _find_nearest_real_embedding(K, x)
end

function _find_nearest_complex_embedding(K::AbsNonSimpleNumField, x)
  r = complex_embeddings(K)
  t = Vector{ArbFieldElem}[]
  for e in r
    embedded_gens = map(e, gens(K))
    gen_diffs = map(abs, embedded_gens - x)
    push!(t, gen_diffs)
  end

  _, i = findmin(map(y -> sum(y), t))

  check_overlaps = y -> isempty(filter(x -> !overlaps(x...), y))
  for j in 1:length(t)
    if j == i
      continue
    end
    if check_overlaps([(t[i][s], t[j][s]) for s in 1:length(gens(K))])
      embedded_roots = [e.roots for e in r]
      roots_to_tuple = x -> (Float64(real(x)), Float64(imag(x)))
      possible = [map(roots_to_tuple, roots) for roots in embedded_roots]
      s = IOBuffer()
      for k in 1:length(possible)
        for w in 1:length(possible[k])
          @printf s "%.2f + i * %.2f" possible[k][w][1] possible[k][w][2]
          if w < length(possible[k])
            print(s, ", ")
          end

        end
        if k < length(possible)
          print(s, "\n")
        end
      end
      ss = String(take!(s))
      error("""Given approximation not close enough to a vector of roots. \n 
            Possible vector of roots are:
            $ss
            """)
    end
  end
  return r[i]
end

function complex_embedding(K::AbsNonSimpleNumField, c::Vector{<: Union{Number, AcbFieldElem}})
  _find_nearest_complex_embedding(K, c)
end
