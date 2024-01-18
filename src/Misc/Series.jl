@doc raw"""
    integral(f::RelPowerSeriesRingElem{T}) -> RelPowerSeriesRingElem

Return the integral of the power series $f$.
"""
function Nemo.integral(f::RelPowerSeriesRingElem{T}) where T
  g = parent(f)()
  fit!(g, precision(f)+1)
  set_precision!(g, precision(f)+1)
  v = valuation(f)
  Nemo.set_valuation!(g, v+1)
  for i=0:Nemo.pol_length(f)
    c = Nemo.polcoeff(f, i)
    if !iszero(c)
      setcoeff!(g, i, divexact(c, i+v+1))
    end
  end
  Nemo.renormalize!(g)
  return g
end

function *(f::PolyRingElem{<:SeriesElem{QadicFieldElem}}, g::PolyRingElem{<:SeriesElem{QadicFieldElem}})
  if degree(f) > 2 &&  degree(g) > 2
    fg = mymul_ks(f, g)
#    @hassert :AbsFact 2 fg == Nemo.mul_classical(f, g)
# This cannot be asserted unfortunately: mymul_ks works in the
# capped abs. prec world, while mul_classical does not:
# f = t*((p+O(p^2) + O(s))), then in the classical world
# f^2 = t^2*p^2+O(p^3), while in the capped world we get 0
# (assuming the cap is at 2)
    return fg
  else
    return Nemo.mul_classical(f, g)
  end
end

#=
function *(f::RelPowerSeriesRingElem{QadicFieldElem}, g::RelPowerSeriesRingElem{QadicFieldElem})
  return mymul_ks(f, g)
  if pol_length(f) > 2 &&  pol_length(g) > 2
    fg = mymul_ks(f, g)
#    @hassert :AbsFact 2 fg == Nemo.mul_classical(f, g)
# This cannot be asserted unfortunately: mymul_ks works in the
# capped abs. prec world, while mul_classical does not:
# f = t*((p+O(p^2) + O(s))), then in the classical world
# f^2 = t^2*p^2+O(p^3), while in the capped world we get 0
# (assuming the cap is at 2)
    return fg
  else
    return Nemo.mul_classical(f, g)
  end
end
=#


@inline function coeffraw(q::QadicFieldElem, i::Int)
  @assert i < length(q)
  return reinterpret(Ptr{ZZRingElem}, q.coeffs)+i*sizeof(Ptr{Int})
end

@inline function coeffraw(q::ZZPolyRingElem, i::Int)
  @assert i < length(q)
  return reinterpret(Ptr{ZZRingElem}, q.coeffs)+i*sizeof(Ptr{Int})
end

#=
function mul!(C::Generic.RelSeries{QadicFieldElem}, f::Generic.RelSeries{QadicFieldElem}, g::Generic.RelSeries{QadicFieldElem})
  return f*g
end
=#

function mymul_ks(f::SeriesElem{QadicFieldElem}, g::SeriesElem{QadicFieldElem})
  rf = precision(f)
  rg = precision(g)
  S = parent(f)
  Qq = base_ring(S)
  h = degree(Qq)
  mp = typemax(Int)

  #assume no denominator!!!
  F = Hecke.Globals.Zx()
  fit!(F, 1+rf*(2*h-1))
  for j=0:rf-1
    d = coeff(f, j)
    mp = min(mp, precision(d))
    v = valuation(d)
    if v > 0
      sc = prime(Qq)^v
    end
    for k=0:length(d)-1
      Base.GC.@preserve d setcoeff!(F, (j)*(2*h-1)+k, coeffraw(d, k))
      if v > 0 && length(F)-1 >= (j)*(2*h-1)+k
        #problem: if the new coeff is zero, the length isn't increased
        Base.GC.@preserve F Hecke.mul!(coeffraw(F, (j)*(2*h-1)+k), coeffraw(F, (j)*(2*h-1)+k), sc)
      end
    end
  end

  G = Hecke.Globals.Zx()
  fit!(G, 1+rg*(2*h-1))
  for j=0:rg-1
    d = coeff(g, j)
    mp = min(mp, precision(d))
    v = valuation(d)
    if v > 0
      sc = prime(Qq)^v
    end
    for k=0:length(d)-1
      Base.GC.@preserve d setcoeff!(G, (j)*(2*h-1)+k, coeffraw(d, k))
      if v > 0 && length(G)-1 >= (j)*(2*h-1)+k
        #problem: if the new coeff is zero, the length isn't increased
        Base.GC.@preserve F Hecke.mul!(coeffraw(G, (j)*(2*h-1)+k), coeffraw(G, (j)*(2*h-1)+k), sc)
      else
      end
    end
  end

#  @show density(F), density(G), mp
  FG = mullow(F, G, min(rf, rg)*(2*h-1))

  c = QadicFieldElem[]
  for j=0:min(rf,rg)-1
    H = Hecke.Globals.Zx()
    for x = 0:2*h-2
      if x + (j)*(2*h-1) < length(FG)
        Base.GC.@preserve FG, setcoeff!(H, x, coeffraw(FG, x + (j)*(2*h-1)))
      end
    end
    push!(c, Qq(H, mp))
    @assert valuation(c[end]) >= 0
  end
  while iszero(c[end]) && length(c) > 1
    pop!(c)
  end
  s = S(c, length(c), min(rf, rg), 0)
  Hecke.renormalize!(s)
  return s
end


function mymul_ks(f::PolyRingElem{<:SeriesElem{QadicFieldElem}}, g::PolyRingElem{<:SeriesElem{QadicFieldElem}})
  nf = degree(f)
  ng = degree(g)
  rf = minimum(precision, coefficients(f))
  rg = minimum(precision, coefficients(g))
  S = base_ring(f)
  Qq = base_ring(S)
  h = degree(Qq)
  mp = typemax(Int)

  #assume no denominator!!!
  nfg = nf+ng+1

  F = Hecke.Globals.Zx()
  fit!(F, 1+(rf*nfg+nf)*(2*h-1))
  for i=0:degree(f)
    c = coeff(f, i)
    for j=0:rf-1
      d = coeff(c, j)
      mp = min(mp, precision(d))
      v = valuation(d)
      if v > 0
        sc = prime(Qq)^v
      end
      for k=0:length(d)-1
        Base.GC.@preserve d setcoeff!(F, (j*nfg+i)*(2*h-1)+k, coeffraw(d, k))
        if v > 0 && length(F)-1 >= (j*nfg+i)*(2*h-1)+k
          #problem: if the new coeff is zero, the length isn't increased
          Base.GC.@preserve F Hecke.mul!(coeffraw(F, (j*nfg+i)*(2*h-1)+k), coeffraw(F, (j*nfg+i)*(2*h-1)+k), sc)
        end
      end
    end
  end
  G = Hecke.Globals.Zx()
  fit!(G, 1+(rg*nfg+ng)*(2*h-1))
  for i=0:degree(g)
    c = coeff(g, i)
    for j=0:rg-1
      d = coeff(c, j)
      mp = min(mp, precision(d))
      v = valuation(d)
      if v > 0
        sc = prime(Qq)^v
      end
      for k=0:length(d)-1
        Base.GC.@preserve d setcoeff!(G, (j*nfg+i)*(2*h-1)+k, coeffraw(d, k))
        if v > 0 && length(G)-1 >= (j*nfg+i)*(2*h-1)+k
          #problem: if the new coeff is zero, the length isn't increased
          Base.GC.@preserve F Hecke.mul!(coeffraw(G, (j*nfg+i)*(2*h-1)+k), coeffraw(d, k), sc)
        else
        end
      end
    end
  end

#  @show density(F), density(G), mp
  FG = mullow(F, G, min(rf, rg)*nfg*(2*h-1))

  fg = parent(f)()

  for i=0:degree(f)+degree(g)
    c = QadicFieldElem[]
    for j=0:min(rf,rg)-1
      H = Hecke.Globals.Zx()
      for x = 0:2*h-2
        if x + (j*nfg+i)*(2*h-1) < length(FG)
          Base.GC.@preserve FG, setcoeff!(H, x, coeffraw(FG, x + (j*nfg+i)*(2*h-1)))
        end
      end
      push!(c, Qq(H, mp))
      @assert valuation(c[end]) >= 0
    end
    while iszero(c[end]) && length(c) > 1
      pop!(c)
    end
    s = S(c, length(c), min(rf, rg), 0)
    Hecke.renormalize!(s)
    if !iszero(s)
      setcoeff!(fg, i, s)
    end
  end
  return fg
end

function Hecke.residue_field(S::SeriesRing{T}) where {T <: Nemo.RingElem} #darn zzModRingElem/gfp
  k = base_ring(S)
  return k, MapFromFunc(S, k, x -> coeff(x, 0), y -> set_precision(S(y), 1))
end

function rational_reconstruction(a::SeriesElem; parent::PolyRing = polynomial_ring(base_ring(a), cached = false)[1])
  C = base_ring(a)
  Ct = parent
  t = gen(Ct)
  b = Ct()
  v = valuation(a)
  for i=0:Nemo.pol_length(a)
    setcoeff!(b, i+v, Nemo.polcoeff(a, i))
  end
  return rational_reconstruction(b, t^precision(a))
end

function rational_reconstruction(a::PadicFieldElem)
  return rational_reconstruction(Hecke.lift(a), prime(parent(a), precision(a)))
end

Hecke.gcd_into!(a::PolyRingElem, b::PolyRingElem, c::PolyRingElem) = gcd(b, c)


function Hecke.squarefree_part(a::PolyRingElem)
  return divexact(a, gcd(a, derivative(a)))
end

