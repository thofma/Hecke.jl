Nemo.fit!(::fmpq_rel_series, Int) = nothing
Nemo.fit!(::fmpq_abs_series, Int) = nothing

@doc Markdown.doc"""
    integral(f::RelSeriesElem{T}) -> RelSeriesElem

Return the integral of the power series $f$.
"""
function Nemo.integral(f::RelSeriesElem{T}) where T
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

function *(f::PolyElem{<:SeriesElem{qadic}}, g::PolyElem{<:SeriesElem{qadic}})
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
function *(f::RelSeriesElem{qadic}, g::RelSeriesElem{qadic})
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

function Base.minimum(::typeof(precision), a::Vector{<:SeriesElem})
  return minimum(map(precision, a))
end

function Base.maximum(::typeof(precision), a::Vector{<:SeriesElem})
  return maximum(map(precision, a))
end
Base.length(a::qadic) = a.length


@inline function coeffraw(q::qadic, i::Int)
  @assert i < length(q)
  return reinterpret(Ptr{fmpz}, q.coeffs)+i*sizeof(Ptr{Int})
end

@inline function coeffraw(q::fmpz_poly, i::Int)
  @assert i < length(q)
  return reinterpret(Ptr{fmpz}, q.coeffs)+i*sizeof(Ptr{Int})
end

@inline function Hecke.setcoeff!(z::fmpz_poly, n::Int, x::Ptr{fmpz})
   ccall((:fmpz_poly_set_coeff_fmpz, Hecke.libflint), Nothing,
                    (Ref{fmpz_poly}, Int, Ptr{fmpz}), z, n, x)
   return z
end

@inline function Hecke.mul!(a::Ref{fmpz}, b::Ref{fmpz}, c::fmpz)
  ccall((:fmpz_mul, Hecke.libflint), Cvoid, (Ref{fmpz}, Ref{fmpz}, Ref{fmpz}),a, b, c)
end
@inline function Hecke.iszero(a::Ref{fmpz})
  return unsafe_load(reinterpret(Ptr{Int}, a))==0
end

#=
function mul!(C::Generic.RelSeries{qadic}, f::Generic.RelSeries{qadic}, g::Generic.RelSeries{qadic})
  return f*g
end
=#

function mymul_ks(f::SeriesElem{qadic}, g::SeriesElem{qadic})
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

  c = qadic[]
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


function mymul_ks(f::PolyElem{<:SeriesElem{qadic}}, g::PolyElem{<:SeriesElem{qadic}})
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
    c = qadic[]
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


function Nemo.canonical_unit(a::SeriesElem)
  iszero(a) && return one(parent(a))
  v = valuation(a)
  v == 0 && return a
  v > 0 && return shift_right(a, v)
  return shift_left(a, -v)
end

#TODO: this is for rings, not for fields, maybe different types?
function Base.gcd(a::T, b::T) where {T <: SeriesElem}
  iszero(a) && iszero(b) && return a
  iszero(a) && return gen(parent(a))^valuation(b)
  iszero(b) && return gen(parent(a))^valuation(a)
  return gen(parent(a))^min(valuation(a), valuation(b))
end

function Base.lcm(a::T, b::T) where {T <: SeriesElem}
  iszero(a) && iszero(b) && return a
  iszero(a) && return a
  iszero(b) && return b
  return gen(parent(a))^max(valuation(a), valuation(b))
end


function Hecke.ResidueField(S::SeriesRing{T}) where {T <: Nemo.RingElem} #darn nmod/gfp
  k = base_ring(S)
  return k, MapFromFunc(x -> coeff(x, 0), y -> set_precision(S(y), 1), S, k)
end

#TODO: in Nemo, rename to setprecision
#      fix/report series add for different length
function set_precision(a::SeriesElem, i::Int)
  b = deepcopy(a)
  set_precision!(b, i)
  return b
end

# should be Nemo/AA
# TODO: symbols vs strings
#       lift(PolyRing, Series)
#       lift(FracField, Series)
#       (to be in line with lift(ZZ, padic) and lift(QQ, padic)
#TODO: some of this would only work for Abs, not Rel, however, this should be fine here
function Hecke.map_coefficients(f, a::RelSeriesElem; parent::SeriesRing)
  c = typeof(f(coeff(a, 0)))[]
  for i=0:Nemo.pol_length(a)-1
    push!(c, f(Nemo.polcoeff(a, i)))
  end
  b = parent(c, length(c), precision(a), valuation(a))
  return b
end

#=
function Hecke.map_coefficients(f, a::RelSeriesElem)
  d = f(coeff(a, 0))
  T = parent(a)
  if parent(d) == base_ring(T)
    S = T
  else
    S = PowerSeriesRing(parent(d), max_precision(T), string(var(T)), cached = false)[1]
  end
  c = typeof(d)[d]
  for i=1:Nemo.pol_length(a)-1
    push!(c, f(Nemo.polcoeff(a, i)))
  end
  b = S(c, length(c), precision(a), valuation(a))
  return b
end
=#
function lift(R::PolyRing{S}, s::SeriesElem{S}) where {S}
  t = R()
  for x = 0:pol_length(s)
    setcoeff!(t, x, polcoeff(s, x))
  end
  return shift_left(t, valuation(s))
end

function rational_reconstruction(a::SeriesElem; parent::PolyRing = PolynomialRing(base_ring(a), cached = false)[1])
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

function rational_reconstruction(a::padic)
  return rational_reconstruction(Hecke.lift(a), prime(parent(a), precision(a)))
end

Hecke.gcd_into!(a::PolyElem, b::PolyElem, c::PolyElem) = gcd(b, c)
Base.copy(a::PolyElem) = deepcopy(a)
Base.copy(a::SeriesElem) = deepcopy(a)

function Hecke.squarefree_part(a::PolyElem)
  return divexact(a, gcd(a, derivative(a)))
end

