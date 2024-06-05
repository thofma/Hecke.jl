######################################################################
#
# pure function field
#
######################################################################
struct FFElemCoeffs{T <: RingElement}
   f::T
end

function Nemo.coefficients(f::Generic.FunctionFieldElem)
   return FFElemCoeffs(f)
end

function Base.iterate(PC::FFElemCoeffs, st::Int = -1)
   st += 1
   if st >= degree(parent(PC.f))
       return nothing
   else
       return coeff(PC.f, st), st
   end
end
Base.length(PC::FFElemCoeffs) = degree(parent(PC.f))

function representation_matrix(a::Generic.FunctionFieldElem)
  F = parent(a)
  g = gen(F)
  m = zero_matrix(base_field(F), degree(F), degree(F))
  b = a
  for i=1:degree(F)
    for j=1:degree(F)
      m[i,j] = coeff(b, j-1)
    end
    if i<degree(F)
      b *= g
    end
  end
  return m
end

"""
    hnf_modular(M::MatElem{T}, d::T, is_prime::Bool = false)

Return the `hnf` of `vcat(M, identity_matrix(parent(d), ncols(M)))`
if `is_prime` is set, then instead of an `hnf` internally a `rref` over the
residue field modulo `d` is used.
"""
function hnf_modular(M::MatElem{T}, d::T, is_prime::Bool = false) where {T}
  if is_prime
    x = residue_field(parent(d), d)
    if isa(x, Tuple)
      R, mR = x
    else
      R = x
      mR = MapFromFunc(parent(d), R, x->R(x), x->lift(x))
    end
    r, h = rref(map_entries(mR, M))
    H = map_entries(x->preimage(mR, x), h[1:r, :])
  else
    x = residue_ring(parent(d), d)
    if isa(x, Tuple)
      R, mR = x
    else
      R = x
      mR = MapFromFunc(parent(d), R, x->R(x), x->lift(x))
    end
    r, h = rref(map_entries(mR, M))
    H = map_entries(x->preimage(mR, x), hnf(map_entries(mR, M)))
  end
  H = vcat(H, d*identity_matrix(parent(d), ncols(M)))
  H = hnf(H)
  @assert iszero(H[ncols(M)+1:end, :])
  return H[1:ncols(M), :]
end

function function_field(f::PolyRingElem{<:Generic.RationalFunctionFieldElem}, s::VarName = :_a; check::Bool = true, cached::Bool = false)
  return function_field(f, s, cached = cached)
end

function extension_field(f::PolyRingElem{<:Generic.RationalFunctionFieldElem}, s::VarName = :_a; check::Bool = true, cached::Bool = false)
  return function_field(f, s, cached = cached)
end

function Hecke.basis(F::Generic.FunctionField)
  a = gen(F)
  bas = [a^0, a]
  while length(bas) < degree(F)
    push!(bas, bas[end]*a)
  end
  return bas
end

function Hecke.residue_field(R::PolyRing{T}, p::PolyRingElem{T}) where {T <: NumFieldElem}
  @assert parent(p) === R
  K, _ = number_field(p)
  return K, MapFromFunc(R, K, x -> K(x), y -> R(y))
end

function (F::Generic.FunctionField{T})(p::PolyRingElem{<:AbstractAlgebra.Generic.RationalFunctionFieldElem{T}}) where {T <: FieldElem}
  @assert parent(p) == parent(F.pol)
  @assert degree(p) < degree(F) # the reduction is not implemented
  R = parent(gen(F).num)
  S = coefficient_ring(R)
  d = reduce(lcm, map(denominator, coefficients(p)), init = one(S))
  return F(map_coefficients(S, d*p, parent = R), d)
end

function (F::Generic.FunctionField)(c::Vector{<:RingElem})
  return F(parent(F.pol)(map(base_field(F), c)))
end

(F::Generic.FunctionField)(a::GenOrdElem) = a.data

function Hecke.charpoly(a::Generic.FunctionFieldElem)
  return charpoly(representation_matrix(a))
end

function Hecke.minpoly(a::Generic.FunctionFieldElem)
  return minpoly(representation_matrix(a))
end

function Hecke.discriminant(F::Generic.FunctionField)
  return discriminant(defining_polynomial(F))
end

#######################################################################
#
# support for ZZ
#
#######################################################################

integral_split(a::QQFieldElem, ::ZZRing) = (numerator(a), denominator(a))

integral_split(a::Rational, R::ZZRing) = integral_split(QQFieldElem(a), R)

#######################################################################
#
# support for LocalizedEuclideanRing{ZZRingElem}
#
#######################################################################
function Hecke.integral_split(a::QQFieldElem, R::LocalizedEuclideanRing{ZZRingElem})
  d = denominator(a)
  p = R.prime
  q,w = Hecke.ppio(d, p)
  if R.comp # den can ONLY use prime
    return R(numerator(a)//q), R(w)
  else
    return R(numerator(a)//w), R(q)
  end
end
Hecke.denominator(a::QQFieldElem, R::LocalizedEuclideanRing{ZZRingElem}) = integral_split(a, R)[2]
Hecke.numerator(a::QQFieldElem, R::LocalizedEuclideanRing{ZZRingElem}) = integral_split(a, R)[1]
(::QQField)(a::LocalizedEuclideanRingElem{ZZRingElem}) = data(a)

function Hecke.factor(a::LocalizedEuclideanRingElem{ZZRingElem})
  c = canonical_unit(a)
  b = a*inv(c)
  L = parent(a)
  @assert isone(denominator(data(b)))
  lf = factor(numerator(data(b)))
  return Fac(c, Dict(L(p)=>v for (p,v) = lf.fac))
end

function Hecke.residue_field(R::LocalizedEuclideanRing{ZZRingElem}, p::LocalizedEuclideanRingElem{ZZRingElem})
  pp = numerator(data(p))
  @assert is_prime(pp) && isone(denominator(p))
  F = GF(pp)
  return F, MapFromFunc(R, F, x->F(data(x)), y->R(lift(ZZ, y)))
end

Hecke.is_domain_type(::Type{LocalizedEuclideanRingElem{ZZRingElem}}) = true

#######################################################################
#
# support for RationalFunctionFieldElem{T}
#
#######################################################################
# RationalFunctionFieldElem{T}, KInftyRing{T}

Base.denominator(x::AbstractAlgebra.Generic.RationalFunctionFieldElem{T}, R::KInftyRing{T}) where {T} = Hecke.integral_split(x, R)[2]

Base.numerator(x::AbstractAlgebra.Generic.RationalFunctionFieldElem{T}, R::KInftyRing{T}) where {T} = Hecke.integral_split(x, R)[1]

function Hecke.integral_split(x::AbstractAlgebra.Generic.RationalFunctionFieldElem{T}, R::KInftyRing{T}) where {T}
  if iszero(x)
    return zero(R), one(R)
  end
  a = degree(numerator(x))
  b = degree(denominator(x))
  if b >= a
    return R(x), one(R)
  end
  t = gen(parent(x))
  return R(x*t^(b-a)), R(t^(b-a))
end

(R::Generic.RationalFunctionField{T})(x::KInftyElem{T}) where {T <: FieldElem} = x.d

# RationalFunctionFieldElem{T}, PolyRing{T}
function Hecke.numerator(a::Generic.RationalFunctionFieldElem{T}, S::PolyRing{T}) where {T}
  return numerator(a)
end

function Hecke.denominator(a::Generic.RationalFunctionFieldElem{T}, S::PolyRing{T}) where {T}
  return denominator(a)
end

function Hecke.integral_split(a::Generic.RationalFunctionFieldElem{T}, S::PolyRing{T}) where {T}
  return numerator(a), denominator(a)
end

function Hecke.factor(R::S, a::Generic.RationalFunctionFieldElem{T}) where {T, S<:PolyRing{T}}
  @assert parent(numerator(a)) == R
  f1 = factor(numerator(a))
  f2 = factor(denominator(a))
  for (p,e) = f2.fac
    @assert !haskey(f1.fac, p)
    f1.fac[p] = -e
  end
  f1.unit = divexact(f1.unit, f2.unit)
  return f1
end

########################################################################
#
# Matrices
#
########################################################################

function Hecke.integral_split(M::Vector{<:AbstractAlgebra.FieldElem}, S::Generic.Ring)
  m = [zero(S) for i in 1:length(M)]
  den = one(S)
  for i=1:length(M)
      n, d = integral_split(M[i], S)
      q, r = divrem(den, d)
      if iszero(r)
        m[i] = n*q
      else
        t = lcm(den, d)
        m = divexact(t, den) .* m
        m[i] = n*divexact(t, d)
        den = t
      end
  end
  return m, den
end
function Hecke.integral_split(M::MatElem{<:AbstractAlgebra.FieldElem}, S::Generic.Ring)
  m = zero_matrix(S, nrows(M), ncols(M))
  den = one(S)
  for i=1:nrows(M)
    for j=1:ncols(M)
      n, d = integral_split(M[i,j], S)
      q, r = divrem(den, d)
      if iszero(r)
        m[i,j] = n*q
      else
        t = lcm(den, d)
        m *= divexact(t, den)
        m[i,j] = n*divexact(t, d)
        den = t
      end
    end
  end
  return m, den
end

#TODO: move elsewhere?
function Hecke.lcm(a::Vector{<:RingElem})
  if length(a) == 0
    error("don't know the ring")
  end
  return reduce(lcm, a)
end
