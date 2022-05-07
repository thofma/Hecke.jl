# If we have a relative extension L/K with defining polynomial f, we
# parametrize the infinite places of L using tuples (p, a), where p is a place of K
# and a is a root of p(g).
#
# We store the the following data on the field L itself, which can be accessed via
# _conjugate_data_arb(L, prec)):
#   Vector{Tuple{Vector{InfPlc{K}, Vector{acb}, Vector{arb}, Vector{acb}}
#
# We use the following ordering, which is very important and must not be changed:
# Let (p, rts, r_rts, c_rts) be such an entry.
#
# if p is real, then rts contains
#   - the real roots (isreal returning true), order from -oo to oo
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
mutable struct InfPlcNfRel{S, T}
  field::T
  base_field_place::S
  isreal::Bool
  i::Int
  r::acb
  absolute_index::Int
end

absolute_index(P::InfPlcNfRel) = P.absolute_index

number_field(P::InfPlcNfRel) = P.field

place_type(::Type{AnticNumberField}) = InfPlc

place_type(::AnticNumberField) = InfPlc

place_type(::Type{NfRel{T}}) where {T} = InfPlcNfRel{place_type(parent_type(T)), NfRel{T}}

place_type(K::NfRel{T}) where {T} = place_type(NfRel{T})

isreal(P::InfPlcNfRel) = P.isreal

sign(x::NumFieldElem, P) = _signs(x)[P.absolute_index]

function _signs(a)
  if iszero(a)
    error("element must not be zero")
  end

  p = 16
  r1, r2 = signature(parent(a))

  if r1 == 0
    return Int[]
  end

  s = Array{Int}(undef, r1)
  while true
    c = conjugates(a, p)
    done = true
    for i=1:r1
      if contains(real(c[i]), 0)
        p *= 2
        done = false
        break
      end
      s[i] = is_positive(real(c[i])) ? 1 : -1
    end
    if done
      return s
    end
  end
end

function real_places(K::NfRel)
  res = place_type(K)[]
  for p in infinite_places(K)
    if isreal(p)
      push!(res, p)
    end
  end
  return res
end

function _root(P::InfPlcNfRel)
  return P.r
end

function evaluate(a::NfRelElem, P::InfPlcNfRel, prec::Int = 32)
  r = conjugates_arb(a, prec)
  L = parent(a)
  return r[P.absolute_index]
end


function infinite_places(L::NfRel{T}) where {T}
  S = place_type(parent_type(T))
  _res = get_attribute(L, :infinite_places)
  if _res !== nothing
    return _res::Vector{InfPlcNfRel{S}}
  end
  K = base_field(L)
  data = _conjugates_data(L, 32)
  r, s = signature(L)
  plcs = Vector{InfPlcNfRel{S}}(undef, r+s)
  r_cnt = 1
  c_cnt = 1
  for (P, rts, r_rts, c_rts) in data
    if isreal(P)
      for i in 1:length(r_rts)
        plcs[r_cnt] = InfPlcNfRel{S, typeof(L)}(L, P, true, i, rts[i], r_cnt)
        r_cnt += 1
      end
      rr = length(r_rts)
      for i in 1:length(c_rts)
        plcs[r + c_cnt] = InfPlcNfRel{S, typeof(L)}(L, P, false, rr + i, rts[rr + i], r + c_cnt)
        c_cnt +=1
      end
    else
      for i in 1:length(rts)
        plcs[r + c_cnt] = InfPlcNfRel{S, typeof(L)}(L, P, false, i, rts[i], r + c_cnt)
        c_cnt += 1
      end
    end
  end
  set_attribute!(L, :infinite_places => plcs)
  return plcs
end

function Base.show(io::IOContext, P::InfPlcNfRel{S}) where {S}
  print(io, "Infinite place of\n")
  println(io, number_field(P))
  print(io, "extending the place\n", P.base_field_place, "\n")
  print(io, "with root $(_root(P))")
end

function _roots(f::PolyElem{<: NumFieldElem}, P; prec::Int = 64, sort::Bool = true)
  wprec = Int(floor(1.3 * prec))
  # We definitely want to isolate the real roots as well as identify conjugated roots
  local rts::Vector{acb}
  while true
    con = acb[evaluate(coeff(f, i), P, wprec) for i in 0:degree(f)]
    isreal(P) && @assert all(isreal, con)
    # We need a strictly real polynomial to isolate the real roots
    _wprec = maximum([precision(parent(c)) for c in con])
    CC = AcbField(wprec, cached = false)
    CCy, y = PolynomialRing(CC, cached = false)
    _f = CCy(con)
    try
      rts = roots(_f, target = prec)
      break
    catch e
      if !(isa(e, ErrorException))
        rethrow(e)
      else
        wprec = 2 * wprec
        continue
      end
    end
  end

  if isreal(P)
    r = 0
    real_rts = Vector{arb}()
    for i in 1:length(rts)
      if !isreal(rts[i])
        break
      end
      r += 1
      push!(real_rts, real(rts[i]))
    end

    # let's order the roots

    if sort
      @assert all(i -> isreal(rts[i]), 1:r)
      _rts = view(rts, (r+1):length(rts))
      # Sort the complex one from oo to -oo
      sort!(_rts, by = x -> imag(x), rev = true)
      s = div(length(rts) - r, 2)
      _rts = view(rts, (r+1):(r + s))
      # Sort the first s complex ones from 0 to oo
      sort!(_rts, by = x -> imag(x), rev = false)
    end

    compl_rts = Vector{acb}()

    s = 0

    for i in (r+1):length(rts)
      if is_positive(imag(rts[i]))
        s += 1
        push!(compl_rts, rts[i])
      end
    end
    @assert r + 2*s == degree(f)
  else
    if sort
      sort!(rts, by = x -> imag(x),  rev = false)
    end
    real_rts = arb[]
    compl_rts = acb[]
  end
  return rts, real_rts, compl_rts
end

function _conjugates_data_new(L::NfRel{T}, prec::Int) where {T}
  c = get_attribute(L, :conjugate_data_arb_new)
  S = embedding_type(parent_type(T))
  if c === nothing
    D = Dict{Int, Vector{Tuple{S, Vector{acb}, Vector{arb}, Vector{acb}}}}()
    z = _get_conjugate_data_new(L, prec)
    D[prec] = z
    set_attribute!(L, :conjugate_data_arb_new => D)
    return z
  else
    D = c
    if haskey(D, prec)
      return D[prec]::Vector{Tuple{S, Vector{acb}, Vector{arb}, Vector{acb}}}
    else
      z = _get_conjugate_data_new(L, prec)
      D[prec] = z
      return z
    end
  end
end

function _conjugates_data(L::NfRel{T}, prec::Int) where {T}
  c = get_attribute(L, :conjugate_data_arb)
  S = place_type(parent_type(T))
  if c === nothing
    D = Dict{Int, Vector{Tuple{S, Vector{acb}, Vector{arb}, Vector{acb}}}}()
    z = _get_conjugate_data(L, prec)
    D[prec] = z
    set_attribute!(L, :conjugate_data_arb => D)
    return z
  else
    D = c
    if haskey(D, prec)
      return D[prec]::Vector{Tuple{S, Vector{acb}, Vector{arb}, Vector{acb}}}
    else
      z = _get_conjugate_data(L, prec)
      D[prec] = z
      return z
    end
  end
end

function _get_conjugate_data_new(L::NfRel{T}, prec::Int) where {T}
  K = base_field(L)
  S = embedding_type(parent_type(T))
  g = defining_polynomial(L)
  pls = complex_embeddings(K, conjugates = false)
  data = Tuple{S, Vector{acb}, Vector{arb}, Vector{acb}}[]
  for p in pls
    push!(data, (p, _roots(g, p, prec = prec)...))
  end
  return data
end

function _get_conjugate_data(L::NfRel{T}, prec::Int) where {T}
  K = base_field(L)
  S = place_type(parent_type(T))
  g = defining_polynomial(L)
  pls = infinite_places(K)
  data = Tuple{S, Vector{acb}, Vector{arb}, Vector{acb}}[]
  for p in  pls
    push!(data, (p, _roots(g, p, prec = prec)...))
  end
  return data
end

function conjugates_arb(a::NfRelElem, prec::Int = 64)
  z = acb[]
  L = parent(a)
  g = defining_polynomial(L)
  K = base_field(L)
  conju = Vector{acb}(undef, absolute_degree(parent(a)))
  wprec = prec
  d = absolute_degree(L)

  while true
    data = _get_conjugate_data(L, wprec)

    CC = AcbField(wprec, cached = false)
    CCy, y = PolynomialRing(CC, cached = false)

    r, s = signature(parent(a))
    _r, _s = signature(K)
    real_cnt = 1
    compl_cnt = r + 1

    for i in 1:length(data)
      P, rts, real_rts, compl_rts = data[i]
      a_as_poly = a.data
      poly_evaluated = CCy(acb[evaluate(coeff(a_as_poly, i), P, wprec) for i in 0:degree(a_as_poly)])
      if isreal(P)
        _conjs = evaluate(poly_evaluated, rts[1:length(real_rts)])
        for rt in _conjs
          conju[real_cnt] = rt
          real_cnt += 1
        end
        _conjs = evaluate(poly_evaluated, rts[(length(real_rts) + 1):(length(real_rts) + length(compl_rts))])
        for rt in _conjs
          conju[compl_cnt] = rt
          conju[compl_cnt + s] = conj(rt)
          compl_cnt += 1
        end
      else
        _conjs = evaluate(poly_evaluated, rts)
        for rt in _conjs
          conju[compl_cnt] = rt
          conju[compl_cnt + s] = conj(rt)
          compl_cnt += 1
        end
      end
    end

    if all(x -> radiuslttwopower(x, -prec), conju)
      break
    else
      wprec = 2 * wprec
      continue
    end
  end

  for i in 1:d
    expand!(conju[i], -prec)
  end

  return conju
end

function infinite_places(L::NfRel{nf_elem}, p)
  return [P for P in infinite_places(L) if P.base_field_place == p]
end
