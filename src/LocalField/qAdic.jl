add_verbosity_scope(:qAdic)
add_assertion_scope(:qAdic)

export setprecision!, defining_polynomial

function Base.setprecision(q::qadic, N::Int)
  r = parent(q)()
  r.N = N
  ccall((:padic_poly_set, libflint), Nothing, (Ref{qadic}, Ref{qadic}, Ref{FlintQadicField}), r, q, parent(q))
  return r
end

function Base.setprecision(q::padic, N::Int)
  r = parent(q)()
  r.N = N
  ccall((:padic_set, libflint), Nothing, (Ref{padic}, Ref{padic}, Ref{FlintPadicField}), r, q, parent(q))
  return r
end

function setprecision!(q::qadic, N::Int)
  if N >= q.N
    q.N = N
  end
  q.N = N
  ccall((:qadic_reduce, libflint), Nothing, (Ref{qadic}, Ref{FlintQadicField}), q, parent(q))
#  @assert N >= q.N
  return q
end

function setprecision!(Q::FlintQadicField, n::Int)
  Q.prec_max = n
end

function setprecision!(Q::FlintPadicField, n::Int)
  Q.prec_max = n
end

function Base.setprecision(f::Generic.MPoly{qadic}, N::Int)
  return map_coefficients(x->setprecision(x, N), f, parent = parent(f))
end

function setprecision!(a::AbstractArray{qadic}, N::Int)
  for x = a
    setprecision!(x, N)
  end
end

function Base.setprecision(a::AbstractArray{qadic}, N::Int)
  return map(x->setprecision(x, N), a)
end

function setprecision!(a::Generic.MatSpaceElem{qadic}, N::Int)
  setprecision!(a.entries, N)
end

function Base.setprecision(a::Generic.MatSpaceElem{qadic}, N::Int)
  b = deepcopy(a)
  setprecision!(b, N)
  return B
end

function tr(r::qadic)
  t = coefficient_ring(parent(r))()
  ccall((:qadic_trace, libflint), Nothing, (Ref{padic}, Ref{qadic}, Ref{FlintQadicField}), t, r, parent(r))
  return t
end

function norm(r::qadic)
  t = coefficient_ring(parent(r))()
  ccall((:qadic_norm, libflint), Nothing, (Ref{padic}, Ref{qadic}, Ref{FlintQadicField}), t, r, parent(r))
  return t
end

function setcoeff!(x::fqPolyRepFieldElem, n::Int, u::UInt)
  ccall((:nmod_poly_set_coeff_ui, libflint), Nothing,
                (Ref{fqPolyRepFieldElem}, Int, UInt), x, n, u)
end

function (Rx::Generic.PolyRing{padic})(a::qadic)
  Qq = parent(a)
  #@assert Rx === parent(defining_polynomial(Qq))
  R = base_ring(Rx)
  coeffs = Vector{padic}(undef, degree(Qq))
  for i = 1:length(coeffs)
    c = R()
    ccall((:padic_poly_get_coeff_padic, libflint), Nothing,
           (Ref{padic}, Ref{qadic}, Int, Ref{FlintQadicField}), c, a, i-1, parent(a))
    coeffs[i] = c
  end
  return Rx(coeffs)
end


function coeff(x::qadic, i::Int)
  R = FlintPadicField(prime(parent(x)), parent(x).prec_max)
  c = R()
  ccall((:padic_poly_get_coeff_padic, libflint), Nothing,
           (Ref{padic}, Ref{qadic}, Int, Ref{FlintQadicField}), c, x, i, parent(x))
  return c
end

function setcoeff!(x::qadic, i::Int, y::padic)
  ccall((:padic_poly_set_coeff_padic, libflint), Nothing,
           (Ref{qadic}, Int, Ref{padic}, Ref{FlintQadicField}), x, i, y, parent(x))
end

function setcoeff!(x::qadic, i::Int, y::UInt)
  R = FlintPadicField(prime(parent(x)), parent(x).prec_max)
  Y = R(ZZRingElem(y))
  ccall((:padic_poly_set_coeff_padic, libflint), Nothing,
           (Ref{qadic}, Int, Ref{padic}, Ref{FlintQadicField}), x, i, Y, parent(x))
end

@attributes FlintQadicField

function residue_field(Q::FlintQadicField)
  z = get_attribute(Q, :ResidueFieldMap)
  if z !== nothing
    return codomain(z), z
  end
  Fp = Native.GF(Int(prime(Q)))
  Fpt = polynomial_ring(Fp, cached = false)[1]
  g = defining_polynomial(Q) #no Conway if parameters are too large!
  f = Fpt([Fp(lift(coeff(g, i))) for i=0:degree(Q)])
  k = Native.FiniteField(f, "o", cached = false)[1]
  pro = function(x::qadic)
    v = valuation(x)
    v < 0 && error("elt non integral")
    v > 0 && return k(0)
    z = k()
    for i=0:degree(Q)
      setcoeff!(z, i, UInt(lift(coeff(x, i))%prime(Q)))
    end
    return z
  end
  lif = function(x::fqPolyRepFieldElem)
    z = Q()
    for i=0:degree(Q)-1
      setcoeff!(z, i, coeff(x, i))
    end
    return z
  end
  mk = MapFromFunc(pro, lif, Q, k)
  set_attribute!(Q, :ResidueFieldMap => mk)
  return k, mk
end

function residue_field(Q::FlintPadicField)
  k = Native.GF(Int(prime(Q)))
  pro = function(x::padic)
    v = valuation(x)
    v < 0 && error("elt non integral")
    v > 0 && return k(0)
    z = k(lift(x))
    return z
  end
  lif = function(x::fpFieldElem)
    z = Q(lift(x))
    return z
  end
  return k, MapFromFunc(pro, lif, Q, k)
end

function coefficient_ring(Q::FlintQadicField)
  return FlintPadicField(prime(Q), precision(Q))
end
coefficient_field(Q::FlintQadicField) = coefficient_ring(Q)

function prime(R::PadicField, i::Int)
  p = ZZRingElem()
  ccall((:padic_ctx_pow_ui, libflint), Cvoid, (Ref{ZZRingElem}, Int, Ref{PadicField}), p, i, R)
  return p
end

function getUnit(a::padic)
  u = ZZRingElem()
  ccall((:fmpz_set, libflint), Cvoid, (Ref{ZZRingElem}, Ref{Int}), u, a.u)
  return u, a.v, a.N
end

function lift_reco(::QQField, a::padic; reco::Bool = false)
  if reco
    u, v, N = getUnit(a)
    R = parent(a)
    fl, c, d = rational_reconstruction(u, prime(R, N-v))
    !fl && return nothing

    x = FlintQQ(c, d)
    if v < 0
      return x//prime(R, -v)
    else
      return x*prime(R, v)
    end
  else
    return lift(FlintQQ, a)
  end
end

function *(A::ZZMatrix, B::MatElem{padic})
  return matrix(base_ring(B), A) * B
end

uniformizer(Q::FlintQadicField) = Q(prime(Q))
Base.precision(Q::FlintQadicField) = Q.prec_max

uniformizer(Q::FlintPadicField) = Q(prime(Q))
Base.precision(Q::FlintPadicField) = Q.prec_max

nrows(A::Matrix{T}) where {T} = size(A)[1]
ncols(A::Matrix{T}) where {T} = size(A)[2]

import Base.^
^(a::qadic, b::qadic) = exp(b*log(a))
^(a::padic, b::padic) = exp(b*log(a))

import Base.//
//(a::qadic, b::qadic) = divexact(a, b)
//(a::padic, b::qadic) = divexact(a, b)
//(a::qadic, b::padic) = divexact(a, b)

function defining_polynomial(Q::FlintQadicField, P::Ring = coefficient_ring(Q))
  Pt, t = polynomial_ring(P, cached = false)
  f = Pt()
  for i=0:Q.len-1
    j = unsafe_load(reinterpret(Ptr{Int}, Q.j), i+1)
    a = ZZRingElem()
    ccall((:fmpz_set, libflint), Nothing, (Ref{ZZRingElem}, Int64), a, Q.a+i*sizeof(Ptr))
    setcoeff!(f, j, P(a))
  end
  return f
end
