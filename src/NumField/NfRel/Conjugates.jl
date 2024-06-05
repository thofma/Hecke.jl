place_type(::Type{T}) where {T <: NumField} = InfPlc{T, embedding_type(T)}

place_type(K::NumField) = place_type(typeof(K))

#function _signs(a)
#  if iszero(a)
#    error("element must not be zero")
#  end
#
#  p = 16
#  r1, r2 = signature(parent(a))
#
#  if r1 == 0
#    return Int[]
#  end
#
#  s = Array{Int}(undef, r1)
#  while true
#    c = conjugates(a, p)
#    done = true
#    for i=1:r1
#      if contains(real(c[i]), 0)
#        p *= 2
#        done = false
#        break
#      end
#      s[i] = is_positive(real(c[i])) ? 1 : -1
#    end
#    if done
#      return s
#    end
#  end
#end

function _roots(f::PolyRingElem{<: NumFieldElem}, P; prec::Int = 64, sort::Bool = true)
  return _roots_squarefree(squarefree_part(f), P; prec = prec, sort = sort)
end

function _roots_squarefree(f::PolyRingElem{<: NumFieldElem}, _P; prec::Int = 64, sort::Bool = true)
  wprec = Int(floor(1.3 * prec))
  # We definitely want to isolate the real roots as well as identify conjugated roots
  local rts::Vector{AcbFieldElem}
  P = _P isa InfPlc ? _embedding(_P) : _P
  
  while true
    con = AcbFieldElem[evaluate(coeff(f, i), P, wprec) for i in 0:degree(f)]
    isreal(P) && @assert all(isreal, con)
    # We need a strictly real polynomial to isolate the real roots
    _wprec = maximum([precision(parent(c)) for c in con])
    CC = AcbField(wprec, cached = false)
    CCy, y = polynomial_ring(CC, cached = false)
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
    real_rts = Vector{ArbFieldElem}()
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

    compl_rts = Vector{AcbFieldElem}()

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
    real_rts = ArbFieldElem[]
    compl_rts = AcbFieldElem[]
  end
  return rts, real_rts, compl_rts
end

function _conjugates_data(L::RelSimpleNumField{T}, prec::Int) where {T}
  c = get_attribute(L, :conjugate_data_arb_new)
  S = embedding_type(parent_type(T))
  if c === nothing
    D = Dict{Int, Vector{Tuple{S, Vector{AcbFieldElem}, Vector{ArbFieldElem}, Vector{AcbFieldElem}}}}()
    z = _get_conjugate_data(L, prec)
    D[prec] = z
    set_attribute!(L, :conjugate_data_arb_new => D)
    return z
  else
    D = c
    if haskey(D, prec)
      return D[prec]::Vector{Tuple{S, Vector{AcbFieldElem}, Vector{ArbFieldElem}, Vector{AcbFieldElem}}}
    else
      z = _get_conjugate_data(L, prec)
      D[prec] = z
      return z
    end
  end
end

function _get_conjugate_data(L::RelSimpleNumField{T}, prec::Int) where {T}
  K = base_field(L)
  S = embedding_type(parent_type(T))
  g = defining_polynomial(L)
  pls = complex_embeddings(K, conjugates = false)
  data = Tuple{S, Vector{AcbFieldElem}, Vector{ArbFieldElem}, Vector{AcbFieldElem}}[]
  for p in pls
    push!(data, (p, _roots_squarefree(g, p, prec = prec)...))
  end
  return data
end

function conjugates_arb(a::RelSimpleNumFieldElem, prec::Int = 64)
  z = AcbFieldElem[]
  L = parent(a)
  g = defining_polynomial(L)
  K = base_field(L)
  conju = Vector{AcbFieldElem}(undef, absolute_degree(parent(a)))
  wprec = prec
  d = absolute_degree(L)

  while true
    data = _get_conjugate_data(L, wprec)

    CC = AcbField(wprec, cached = false)
    CCy, y = polynomial_ring(CC, cached = false)

    r, s = signature(parent(a))
    _r, _s = signature(K)
    real_cnt = 1
    compl_cnt = r + 1

    for i in 1:length(data)
      P, rts, real_rts, compl_rts = data[i]
      a_as_poly = a.data
      poly_evaluated = CCy(AcbFieldElem[evaluate(coeff(a_as_poly, i), P, wprec) for i in 0:degree(a_as_poly)])
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
