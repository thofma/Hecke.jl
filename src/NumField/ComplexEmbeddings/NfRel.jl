################################################################################
#
#  Embeddings of simple relative extensions
#
################################################################################

# If we have a relative extension L/K with defining polynomial f, we
# parametrize the complex_embeddings of L using tuples (p, a), where p is an embedding of K
# and a is a root of p(g).
#
# We store the the following data on the field L itself, which can be accessed via
# _conjugate_data_arb_new(L, prec)):
#   Vector{Tuple{Emb{base_field(L)}, Vector{acb}, Vector{arb}, Vector{acb}}
#
# We use the following ordering, which is very important and must not be changed:
# Let (p, rts, r_rts, c_rts) be such an entry.
#
# if p is real, then rts contains
#   - the real roots (isreal returning true), ordered from -oo to oo
#   - then all complex roots with positive imaginary part, order from 0 to oo
# if p is complex, then rts contains
#   - all complex roots with positive imaginary part, ordered -oo to oo
#
# For each place p of K, we have a tuple
#   (p, roots of p(g), arb[], acb[]) if p is complex, and
#   (p, roots of p(g), real roots of g(a), complex roots of g(a) (one per pair))
#   if p is real.
#
# To compute the conjugates of an element represented by g, we iterate over the
# (p, rts, r_rts, c_rts) and first add [ p(g)(r) for r in r_rts if isreal(p)]
# and then [p(g)(rts) for r in r_rts if !isreal(p)]
mutable struct NumFieldEmbNfRel{S, T} <: NumFieldEmb{T}
  field::T              # Number field.
  base_field_emb::S     # Embedding of base field.
  isreal::Bool          # Whether the embedding is real.
  i::Int                # Index of the root of p(g) to which the embedding
                        # is corresponding to.
  r::acb                # The root of p(g)
  absolute_index::Int   # Absolute index for bookkeeping.
  conjugate::Int        # Absolute index of the conjugate embedding.
end

function embedding_type(::Type{NfRel{T}}) where {T}
  return NumFieldEmbNfRel{embedding_type(parent_type(T)), NfRel{T}}
end

embedding_type(K::NfRel{T}) where {T} = embedding_type(NfRel{T})

_absolute_index(f::NumFieldEmbNfRel) = f.absolute_index

number_field(f::NumFieldEmbNfRel) = f.field

isreal(P::NumFieldEmbNfRel) = P.isreal

################################################################################
#
#  Equality
#
################################################################################

function Base.:(==)(f::NumFieldEmbNfRel, g::NumFieldEmbNfRel)
  return number_field(f) === number_field(g) &&
      _absolute_index(f) == _absolute_index(g)
end

################################################################################
#
#  Conjugate embedding
#
################################################################################

function conj(f::NumFieldEmbNfRel)
  return complex_embeddings(number_field(f))[f.conjugate]
end

################################################################################
#
#  Construction of complex_embeddings
#
################################################################################

function complex_embeddings(L::NfRel{T}; conjugates::Bool = true) where {T}
  S = embedding_type(parent_type(T))
  _res = get_attribute(L, :complex_embeddings)
  if _res !== nothing
    res = _res::Vector{embedding_type(L)}
  else
    res = _complex_embeddings(L)
    set_attribute!(L, :complex_embeddings => res)
  end
  if conjugates
    return res
  else
    r, s = signature(L)
    return res[1:(r + s)]
  end
end

# It is easier to construct all complex_embeddings at one
function _complex_embeddings(L::NfRel{T}) where {T}
  K = base_field(L)
  data = _conjugates_data(L, 32)
  r, s = signature(L)
  embs = Vector{embedding_type(L)}(undef, absolute_degree(L))
  S = embedding_type(parent_type(T))
  r_cnt = 1
  c_cnt = 1
  for (P, rts, r_rts, c_rts) in data
    if isreal(P)
      for i in 1:length(r_rts)
        embs[r_cnt] = NumFieldEmbNfRel{S, typeof(L)}(L, P, true, i,
                                                     rts[i], r_cnt, r_cnt)
        r_cnt += 1
      end
      rr = length(r_rts)
      ss = length(c_rts)
      for i in 1:length(c_rts)
        embs[r + c_cnt] =
            NumFieldEmbNfRel{S, typeof(L)}(L, P, false, rr + i, rts[rr + i],
                                           r + c_cnt, r + s + c_cnt)
        embs[r + s + c_cnt] =
            NumFieldEmbNfRel{S, typeof(L)}(L, conj(P), false, rr + ss + i,
                                           conj(rts[rr + i]), r + s + c_cnt,
                                           r + c_cnt)
        c_cnt +=1
      end
    else
      for i in 1:length(rts)
        embs[r + c_cnt] =
            NumFieldEmbNfRel{S, typeof(L)}(L, P, false, i, rts[i],
                                           r + c_cnt, r + s + c_cnt)
        embs[r + s + c_cnt] =
            NumFieldEmbNfRel{S, typeof(L)}(L, conj(P), false, i, conj(rts[i]),
                                           r + s + c_cnt, r + c_cnt)
        c_cnt += 1
      end
    end
  end
  return embs
end

################################################################################
#
#  I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain",  P::NumFieldEmbNfRel)
  print(io, "Embedding of\n")
  println(io, number_field(P))
  print(io, "extending the embedding\n", P.base_field_emb, "\n")
  print(io, "with root ≈ ")
  _print_acb_neatly(io, P.r)
end

function Base.show(io::IO, f::NumFieldEmbNfRel)
  print(io, "Embedding corresponding to (", f.base_field_emb, ") and ≈ ")
  _print_acb_neatly(io, f.r)
end

################################################################################
#
#  Evaluation
#
################################################################################

function (f::NumFieldEmbNfRel)(a::NfRelElem, prec::Int = 32)
  @req number_field(f) === parent(a) "Parent mismatch"
  r, s = signature(parent(a))
  if _absolute_index(f) > r + s
    return conj(conj(f)(a, prec))
  end

  L = parent(a)
  g = defining_polynomial(L)
  K = base_field(L)
  wprec = prec
  d = absolute_degree(L)

  while true
    data = _conjugates_data(L, wprec)

    CC = AcbField(wprec, cached = false)
    CCy, y = polynomial_ring(CC, cached = false)

    _r, _s = signature(K)
    real_cnt = 1
    compl_cnt = r + 1

    for i in 1:length(data)
      P, rts, real_rts, compl_rts = data[i]
      if P !== f.base_field_emb
        continue
      end
      a_as_poly = Hecke.data(a)
      da = degree(a_as_poly)
      poly_evaluated = map_coefficients(let wprec = wprec
                                          x -> evaluate(x, P, wprec)
                                        end,
                                        a_as_poly, parent = CCy)
      _conj = evaluate(poly_evaluated, rts[f.i])
      if radiuslttwopower(_conj, -prec)
        return expand!(_conj, -prec)
      end
    end

    wprec = 2 * wprec
  end
end

evaluate(x::NfRelElem, f::NumFieldEmbNfRel, p::Int) = f(x, p)

################################################################################
#
#  Restrict
#
################################################################################

function restrict(f::NumFieldEmbNfRel, K::NumField)
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

function restrict(e::NumFieldEmb, f::NumFieldMor{<: NfRel, <: Any, <: Any})
  @req number_field(e) === codomain(f) "Number fields do not match"
  L = domain(f)
  emb = complex_embeddings(L)
  # I need to find the embedding of the base_field of L
  K = base_field(L)
  # This is the natural map K -> L
  KtoL = hom(K, L)
  res_base_field = restrict(e, KtoL * f)
  cn = [ overlaps(ee.r, e(f(gen(L)))) && ee.base_field_emb === res_base_field for ee in emb]
  @assert count(cn) == 1
  i = findfirst(cn)
  return emb[i]
end
