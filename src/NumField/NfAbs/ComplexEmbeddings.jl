################################################################################
#
#  Type
#
################################################################################

embedding_type(::Type{AnticNumberField}) = NumFieldEmbNfAbs

embedding_type(::AnticNumberField) = embedding_type(AnticNumberField)

################################################################################
#
#  Field access
#
################################################################################

number_field(f::NumFieldEmbNfAbs) = f.K

isreal(f::NumFieldEmbNfAbs) = f.isreal

_absolute_index(f::NumFieldEmbNfAbs) = f.i

################################################################################
#
#  Construction
#
################################################################################

function complex_embeddings(K::AnticNumberField; conjugates::Bool = true)
  res = get_attribute!(K, :complex_embeddings) do
    return __complex_embeddings(K)
  end::Vector{embedding_type(K)}
  if conjugates
    return res
  else
    r, s = signature(K)
    return res[1:(r + s)]
  end
end

function complex_embedding(K::AnticNumberField, c::acb)
  res = complex_embeddings(K)
  g = gen(K)
  possible_embeddings = []
  for e in res
    if contains(c, midpoint(e(g)))
      append!(possible_embeddings, e)
    end
  end
  if length(possible_embeddings) < 1
    error("Couldn't find an Embedding")
  else if length(possible_embeddings) > 1
    possible = [ e.r for e in possible_embeddings]
    s = IOBuffer()
    for i in 1:length(possible)
      @printf s "%.2f" possible[i]
      if i < length(possible)
        print(s, ", ")
      end
    end
    ss = String(take!(s))
    error("""Given approximation not close enough to a root. Possible roots are:
                 $ss
              """)
  end
  return possible_embeddings[1]
end

function __complex_embeddings(K::AnticNumberField)
  c = conjugate_data_arb(K)
  res = Vector{embedding_type(K)}(undef, degree(K))
  for i in 1:degree(K)
    res[i] = NumFieldEmbNfAbs(K, c, i)
  end
  return res
end

################################################################################
#
#  Conjugate
#
################################################################################

function conj(f::NumFieldEmbNfAbs)
  return complex_embeddings(number_field(f))[f.conjugate]
end

################################################################################
#
#  Equality
#
################################################################################

function Base.:(==)(f::NumFieldEmbNfAbs, g::NumFieldEmbNfAbs)
  return number_field(f) === number_field(g) &&
      _absolute_index(f) == _absolute_index(g)
end

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", f::NumFieldEmbNfAbs)
  print(io, "Embedding of\n", number_field(f), "\ncorresponding to ≈ ")
  _print_acb_neatly(io, f.r)
end

function Base.show(io::IO, f::NumFieldEmbNfAbs)
  print(io, "Embedding corresponding to ≈ ")
  _print_acb_neatly(io, f.r)
end

################################################################################
#
#  Evaluation
#
################################################################################

evaluate(x::nf_elem, f::NumFieldEmbNfAbs, p::Int) = f(x, p)

function (f::NumFieldEmbNfAbs)(x::nf_elem, abs_tol::Int = 32)
  K = parent(x)
  d = degree(K)
  r1, r2 = signature(K)
  target_tol = abs_tol
  abs_tol = Int(floor(abs_tol * 1.1))

  i = f.i

  while true
    prec_too_low = false
    c = conjugate_data_arb_roots(K, abs_tol)

    abs_tol < 0 && error("Precision overflow in evaluation of embedding")

    CC = AcbField(abs_tol, cached = false)
    RR = ArbField(abs_tol, cached = false)

    xpoly = arb_poly(parent(K.pol)(x), abs_tol)

    if i <= r1
      o = RR()
      ccall((:arb_poly_evaluate, libarb), Nothing,
            (Ref{arb}, Ref{arb_poly}, Ref{arb}, Int),
             o, xpoly, c.real_roots[i], abs_tol)

      if !isfinite(o) || !radiuslttwopower(o, -target_tol)
        abs_tol = 2*abs_tol
        prec_too_low = true
      else
        cc = CC(o)
        break
      end
    else
      tacb = CC()
      j = i <= r1 + r2 ? i - r1 : i - r1 - r2
      ccall((:arb_poly_evaluate_acb, libarb), Nothing,
            (Ref{acb}, Ref{arb_poly}, Ref{acb}, Int),
             tacb, xpoly, c.complex_roots[j], abs_tol)

      if !isfinite(tacb) || !radiuslttwopower(tacb, -target_tol)
        abs_tol = 2*abs_tol
        prec_too_low = true
      else
        if i <= r1 + r2 
          cc = tacb
        else
          cc = conj(tacb)
        end
        break
      end
    end

    if prec_too_low
      continue
    end
  end

  cc = expand!(cc, -target_tol)
  return cc
end

#################################################################################
#
#  Restrict from bigger field
#
################################################################################

function restrict(e::NumFieldEmb, f::NumFieldMor{AnticNumberField, <: Any, <: Any})
  @req number_field(e) === codomain(f) "Number fields do not match"
  L = domain(f)
  emb = complex_embeddings(L)
  a = gen(L)
  # I need to find the embedding of the base_field of L
  b = e(f(a))
  cn = Bool[overlaps(b, e(a)) for e in emb]
  @assert count(cn) == 1
  i = findfirst(cn)
  return emb[i]
end

################################################################################
#
#  Easier creation of embeddings
#
################################################################################

function _find_nearest_embedding(K::AnticNumberField, x::Union{BigFloat, Float64})
  r = real_embeddings(K)
  diffs = [e(gen(K)) - x for e in r]
  t = [abs(z) for z in diffs]
  for i in 1:length(t)
    for j in (i + 1):length(t)
      if overlaps(t[i], t[j]) 
        possible = [ Float64(real(e.r)) for e in r]
        s = IOBuffer()
        for i in 1:length(possible)
          @printf s "%.2f" possible[i]
          if i < length(possible)
            print(s, ", ")
          end
        end
        ss = String(take!(s))
        error("""Given approximation not close enough to a root. Possible roots are:
                 $ss
              """)
      end
    end
  end
  _, i = findmin(t)
  return r[i]
end

function real_embedding(K::AnticNumberField, x::Union{BigFloat, Float64})
  return _find_nearest_embedding(K, x)
end

_is_contained_in_interval(x::arb, i::Tuple) = i[1] < x && x < i[2]

function _find_nearest_embedding(K::AnticNumberField, x::Tuple)
  r = real_embeddings(K)
  p = 32
  fls = [_is_contained_in_interval(real(i(gen(K), p)), x) for i in r]
  while count(fls) != 1
    p = 2 * p
    fls = [_is_contained_in_interval(real(i(gen(K), p)), x) for i in r]
    if count(fls) > 1
      possible = [ Float64(real(e.r)) for e in r]
      s = IOBuffer()
      for i in 1:length(possible)
        @printf s "%.2f" possible[i]
        if i < length(possible)
          print(s, ", ")
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

function real_embedding(K::AnticNumberField, x::Tuple)
  return _find_nearest_embedding(K, x)
end
