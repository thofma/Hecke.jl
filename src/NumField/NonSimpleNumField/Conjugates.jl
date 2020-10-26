mutable struct InfPlcNonSimple{S, T, U}
  field::S
  components::Vector{T}
  base_field_place::U
  absolute_index::Int
  isreal::Bool
end

function place_type(L::NfRelNS{T}) where {T}
  return InfPlcNonSimple{typeof(L), place_type(_ext_type(T)), place_type(parent_type(T))}
end

real_places(L::NfRelNS) = [p for p in infinite_places(L) if isreal(p)]

isreal(P::InfPlcNonSimple) = P.isreal

function signature(L::NfRelNS)
  c = get_special(L, :signature)
  if c isa Tuple{Int, Int}
    return c::Tuple{Int, Int}
  end
  K = base_field(L)
  Kx, x = PolynomialRing(K, cached = false)
  rlp = real_places(K)
  # For each real place of K, we look how many real places of the components there are and multiply
  v = Int[1 for i in 1:length(rlp)]
  for i in 1:length(L.pol)
    fi = to_univariate(Kx, L.pol[i])
    for j in 1:length(rlp)
      v[j] = v[j] * number_real_roots(fi, rlp[j])
    end
  end

  r = sum(v)
  d = absolute_degree(L)
  s = div(d - r, 2)
  set_special(L, :signature => (r, s))
  return r, s
end

function infinite_places(L::NfRelNS{T}) where {T}
  c = get_special(L, :infinite_places)
  if c !== nothing
    return c::Vector{place_type(L)}
  end
  r, s = signature(L)
  K = base_field(L)
  S = place_type(parent_type(T))
  Kx, x = PolynomialRing(K, cached = false)
  pls = infinite_places(K)
  data = Tuple{S, Vector{acb}, Vector{arb}, Vector{acb}}[]
  comps = _ext_type(T)[component(L, j)[1] for j in 1:ngens(L)]
  _res = []
  r_cnt = 0
  s_cnt = r
  l = 0
  res = Vector{place_type(L)}(undef, r + s)
  for p in pls 
    v = Tuple{Vector{place_type(_ext_type(T))}, Bool}[(collect(w), all(isreal, w)) for w in Iterators.product([infinite_places(comps[j], p) for j in 1:ngens(L)]...)]
    for (w, _isreal) in v
      if _isreal
        r_cnt += 1
        @assert !isassigned(res, r_cnt)
        res[r_cnt] = InfPlcNonSimple{typeof(L), place_type(_ext_type(T)), S}(L, w, p, l += 1, _isreal)
      else
        s_cnt += 1
        @assert !isassigned(res, s_cnt)
        res[s_cnt] = InfPlcNonSimple{typeof(L), place_type(_ext_type(T)), S}(L, w, p, l += 1, _isreal)
      end
    end
  end
  set_special(L, :infinite_places => res)
  return res
end

function conjugates_arb(a::NfRelNSElem{T}, prec::Int = 32) where {T}
  # This is very slow.

  f = data(a)
  wprec = prec
  L = parent(a)
  res = Vector{acb}(undef, absolute_degree(L))
  comp_gens = [gen(component(L, j)[1]) for j in 1:ngens(L)]
  pt = Vector{acb}(undef, ngens(L))
  found = false

  r, s = signature(L)


  r_cnt = 1
  s_cnt = 1

  IP = infinite_places(parent(a))
  
  while !found
    found = true
    r_cnt = 1
    s_cnt = 1

    for p in IP
      for i in 1:ngens(L)
        pt[i] = evaluate(comp_gens[i], p.components[i], wprec)
      end
      prec1 = maximum(x -> precision(parent(x)), pt)
      prec2 = maximum(x -> precision(parent(evaluate(x, p.base_field_place, wprec))), coeffs(f))
      prec3 = max(prec1, prec2)
      
      CC = AcbField(prec3, cached = false)
      CCy, y = PolynomialRing(CC, ngens(L), cached = false)
 
      fatp = map_coeffs(x -> evaluate(x, p.base_field_place, wprec), f, parent = CCy)

      for c in fatp.coeffs
        c.parent = CC
      end

      for i in 1:ngens(L)
        pt[i].parent = CC
      end

      o = evaluate(fatp, pt)
      if !radiuslttwopower(o, -prec)
        wprec = 2 * wprec
        found = false
        break
      end
      if isreal(p)
        res[r_cnt] = o
        r_cnt += 1
      else
        res[r + s_cnt] = o
        res[r + s + s_cnt] = conj(o)
        s_cnt += 1
      end
    end
  end
  return res
end
