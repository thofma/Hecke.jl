################################################################################
#
#  Type
#
################################################################################

embedding_type(::Type{AbsSimpleNumField}) = AbsSimpleNumFieldEmbedding

################################################################################
#
#  Field access
#
################################################################################

number_field(f::AbsSimpleNumFieldEmbedding) = f.K

isreal(f::AbsSimpleNumFieldEmbedding) = f.isreal

_absolute_index(f::AbsSimpleNumFieldEmbedding) = f.i

################################################################################
#
#  Construction
#
################################################################################

function complex_embeddings(K::AbsSimpleNumField; conjugates::Bool = true)
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

function __complex_embeddings(K::AbsSimpleNumField)
  c = conjugate_data_arb_roots(K, 16)
  res = Vector{embedding_type(K)}(undef, degree(K))
  for i in 1:degree(K)
    res[i] = AbsSimpleNumFieldEmbedding(K, c, i)
  end
  return res
end

################################################################################
#
#  Conjugate
#
################################################################################

function conj(f::AbsSimpleNumFieldEmbedding)
  return complex_embeddings(number_field(f))[f.conjugate]
end

################################################################################
#
#  Equality
#
################################################################################

function Base.:(==)(f::AbsSimpleNumFieldEmbedding, g::AbsSimpleNumFieldEmbedding)
  return number_field(f) === number_field(g) &&
      _absolute_index(f) == _absolute_index(g)
end

function Base.hash(f::AbsSimpleNumFieldEmbedding, h::UInt)
  h = hash(number_field(f), h)
  h = hash(_absolute_index(f), h)
  return h
end

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", f::AbsSimpleNumFieldEmbedding)
  print(io, "Complex embedding corresponding to ")
  _print_acb_neatly(io, f.r)
  println(io)
  io = pretty(io)
  print(io, Indent(), "of ", Lowercase())
  Base.show(io, MIME"text/plain"(), number_field(f))
end

function Base.show(io::IO, f::AbsSimpleNumFieldEmbedding)
  if is_terse(io)
    print(io, "Complex embedding of number field")
  else
    print(io, "Complex embedding corresponding to ")
    _print_acb_neatly(io, f.r)
    io = pretty(io)
    print(terse(io), " of ", Lowercase(), number_field(f))
  end
end

################################################################################
#
#  Evaluation
#
################################################################################

evaluate(x::AbsSimpleNumFieldElem, f::AbsSimpleNumFieldEmbedding, p::Int = 32) = f(x, p)

function (f::AbsSimpleNumFieldEmbedding)(x::AbsSimpleNumFieldElem, abs_tol::Int = 32)
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

    xpoly = ArbPolyRingElem(parent(K.pol)(x), abs_tol)

    if i <= r1
      o = RR()
      ccall((:arb_poly_evaluate, libarb), Nothing,
            (Ref{ArbFieldElem}, Ref{ArbPolyRingElem}, Ref{ArbFieldElem}, Int),
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
            (Ref{AcbFieldElem}, Ref{ArbPolyRingElem}, Ref{AcbFieldElem}, Int),
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

function restrict(e::NumFieldEmb, f::NumFieldHom{AbsSimpleNumField, <: Any, <: Any})
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

function _find_nearest_real_embedding(K::AbsSimpleNumField, x::Union{BigFloat, Float64})
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

function real_embedding(K::AbsSimpleNumField, x::Union{BigFloat, Float64})
  return _find_nearest_real_embedding(K, x)
end

_is_contained_in_interval(x::ArbFieldElem, i::Tuple) = i[1] < x && x < i[2]

function _find_nearest_real_embedding(K::AbsSimpleNumField, x::Tuple)
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

function real_embedding(K::AbsSimpleNumField, x::Tuple)
  return _find_nearest_real_embedding(K, x)
end

function _find_nearest_complex_embedding(K::AbsSimpleNumField, x)
  r = complex_embeddings(K)
  diffs = [e(gen(K)) - x for e in r]
  t = [abs(z) for z in diffs]
  _, i = findmin(t)
  for j in 1:length(t)
    if j == i
      continue
    end
    if overlaps(t[i], t[j]) 
      possible = [ (Float64(real(e.r)), Float64(imag(e.r))) for e in r]
      s = IOBuffer()
      for i in 1:length(possible)
        @printf s "%.2f + i * %.2f" possible[i][1] possible[i][2]
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
  return r[i]
end

function complex_embedding(K::AbsSimpleNumField, c::Union{Number, AcbFieldElem})
  _find_nearest_complex_embedding(K, c)
end

################################################################################
#
#  Infinite uniformizers
#
################################################################################

@doc raw"""
    infinite_uniformizers(K::NumField) -> Dict{NumFieldEmb, NumFieldElem}

Returns a dictionary having as keys the real real embeddings of $K$ and the values
are uniformizers for the corresponding real embedding.

A uniformizer of a real embedding $e$ is an element of the field which is negative
at $e$ and positive at all the other real embeddings.
"""
function infinite_uniformizers(K::AbsSimpleNumField)
  r, s = signature(K)
  if iszero(r)
    return Dict{embedding_type(K), AbsSimpleNumFieldElem}()
  end

  return get_attribute!(K, :infinite_places_uniformizers) do
    return _infinite_uniformizers(K)
  end::Dict{embedding_type(K), AbsSimpleNumFieldElem}
end
# 

function _infinite_uniformizers(K::AbsSimpleNumField)
  p = real_embeddings(K) #Important: I assume these are ordered as the roots of the defining polynomial!
  S = abelian_group(Int[2 for i = 1:length(p)])

  s = Vector{FinGenAbGroupElem}(undef, length(p))
  g = Vector{AbsSimpleNumFieldElem}(undef, length(p))
  ind = 1
  q, mq = quo(S, FinGenAbGroupElem[], false)
  b = 10
  cnt = 0
  pr = 16
  while b > 0
    a = rand(K, collect(-b:b))
    if iszero(a)
      continue
    end
    lc = conjugates(a, pr)
    pr = 16
    done = true
    while true
      for i = 1:length(p)
        if contains(reim(lc[i])[1], 0)
          pr *= 2
          done = false
          break
        end
      end
      if !done
        lc = conjugates(a, pr)
        done = true
      else
        break
      end
    end
    ar = zeros(Int, length(p))
    for i = 1:length(p)
      if is_positive(reim(lc[i])[1])
        ar[i] = 0
      else
        ar[i] = 1
      end
    end
    t = S(ar)
    if !iszero(mq(t))
      s[ind] = t
      g[ind] = a
      ind += 1
      q, mq = quo(S, s[1:ind-1], false)
      if ind > length(p)
        break
      end
    end
    cnt += 1
    if cnt > 1000
      b *= 2
      cnt = 0
    end
    for i = 1:length(p)
      good = true
      rep = reim(lc[i])[1]
      if is_positive(rep)
        y = -ceil(ZZRingElem, BigFloat(rep))-1
      else
        y = -floor(ZZRingElem, BigFloat(rep))+1
      end
      ar = zeros(Int, length(p))
      for j = 1:length(p)
        el = reim(lc[j])[1]+y
        if !is_positive(el) && !is_negative(el)
          good = false
          break
        end
        if is_positive(reim(lc[j])[1]+y)
          ar[j] = 0
        else
          ar[j] = 1
        end
      end
      if !good
        continue
      end
      t = S(ar)
      if !iszero(mq(t))
        s[ind] = t
        g[ind] = a + y
        ind += 1
        q, mq = quo(S, s[1:ind-1], false)
        if ind > length(p)
          break
        end
      end
    end
    if ind > length(p)
      break
    end
  end
  if b <= 0
    b = 10
    cnt = 0
    lllE = lll(equation_order(K))
    bas = basis(lllE, K, copy = false)
    while true
      @assert b>0
      a = rand(bas, 1:b)
      if iszero(a)
        continue
      end
      emb = signs(a, p)
      ar = Int[0 for i = 1:length(p)]
      for i=1:length(p)
        if emb[p[i]] == -1
          ar[i] = 1
        end
      end
      t = S(ar)
      if !iszero(mq(t))
        s[ind] = t
        g[ind] = a
        ind += 1
        q, mq = quo(S, s[1:ind-1], false)
        if ind > length(p)
          break
        end
      else
        cnt += 1
        if cnt > 1000
          b *= 2
          cnt = 0
        end
      end
    end
  end
  hS = hom(S, S, s)   # Change of coordinates so that the canonical basis elements are mapped to the elements found above
  r = Vector{AbsSimpleNumFieldElem}(undef, length(p))
  hS1 = inv(hS)
  for i = 1:length(p)
    y = hS1(S[i])
    auxr = one(K)
    for w = 1:length(p)
      if !iszero(y[w])
        mul!(auxr, auxr, g[w])
      end
    end
    lc = conjugates(auxr, pr)
    while !is_negative(reim(lc[i])[1] + 1)
      auxr *= 2
      lc = conjugates(auxr, pr)
    end
    for j = 1:length(p)
      if j == i
        continue
      end
      while !is_positive(reim(lc[j])[1] - 1)
        auxr *= 2
        lc = conjugates(auxr, pr)
      end
    end
    r[i] = auxr
  end
  D = Dict{embedding_type(K), AbsSimpleNumFieldElem}()
  for i = 1:length(p)
    D[p[i]] = r[i]
    @hassert :AbsNumFieldOrder 1 sign(r[i], p[i]) == -1
    #@hassert :AbsNumFieldOrder 1 all(x -> isone(x), values(signs(r[i], [P for P in p if P != p[i]])))
  end
  return D
end

function sign_map(O::AbsSimpleNumFieldOrder, p::Vector, lying_in::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem} = 1 * O)
  K = nf(O)

  if isempty(p)
    S = abelian_group(Int[])
    local exp1
    let S = S, lying_in = lying_in, O = O
      function exp1(A::FinGenAbGroupElem)
        return O(minimum(lying_in))
      end
    end

    local log1
    let S = S
      function log1(B::T) where T <: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
        return id(S)
      end
    end
    return S, exp1, log1
  end

  D = infinite_uniformizers(K)

  S = abelian_group(Int[2 for i = 1:length(p)])

  local exp
  let S = S, D = D, p = p, O = O, lying_in = lying_in, K = K
    function exp(A::FinGenAbGroupElem)
      s = one(K)
      if iszero(A)
        return minimum(lying_in)*O(s)
      end
      for i = 1:length(p)
        if isone(A[i])
          mul!(s, s, D[p[i]])
        end
      end
      return minimum(lying_in)*O(s)
    end
  end

  local log
  let S = S, D = D, p = p
    function log(B::T) where T <: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}
      emb = signs(B, p)
      res = zeros(Int, length(p))
      for i=1:length(p)
        if emb[p[i]] == -1
          res[i] = 1
        end
      end
      return S(res)
    end
  end

  return S, exp, log
end


