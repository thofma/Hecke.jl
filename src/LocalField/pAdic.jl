################################################################################
#
#  Lifting and residue fields
#
################################################################################

@doc Markdown.doc"""
  lift(a::padic) -> fmpz

  Returns the positive canonical representative in Z. a needs
  to be integral.
"""
function lift(a::padic)
  b = fmpz()
  R = parent(a)
  ccall((:padic_get_fmpz, :libflint), Nothing, (Ref{fmpz}, Ref{padic}, Ref{FlintPadicField}), b, a, R)
  return b
end

@doc Markdown.doc"""
    lift(a::T, K::PadicField) where T <: Union{Nemo.nmod, Generic.Res{fmpz}, gfp_elem} -> padic

Computes a lift of the element from the residue ring.
"""
function lift(a::T, K::PadicField) where T <: Union{Nemo.nmod, Generic.Res{fmpz}, gfp_elem} 
  n = modulus(parent(a))
  p = prime(K)
  v, fl = remove(n, p)
  @assert isone(fl)
  return Hecke.lift(a) + O(K, p^v)
end

@doc Markdown.doc"""
    lift(x::nmod, Q::PadicField) -> padic

Computes a lift of the element from the residue ring.
"""
function lift(x::nmod, Q::PadicField)
    z = Q()
    z.u = lift(x)
  return setprecision(z, 1)
end

#TODO: Explain why this function exists.
function lift_reco(::FlintRationalField, a::padic; reco::Bool = false)
  if reco
    u = unit_part(a)
    R = parent(a)
    fl, c, d = rational_reconstruction(u, prime_power(R, N-v))
    !fl && return nothing
    
    x = FlintQQ(c, d)
    if valuation(a) < 0
      return x//prime_power(R, -v)
    else
      return x*prime_power(R, v)
    end
  else
    return lift(FlintQQ, a)
  end
end

function ResidueField(Q::FlintPadicField)
  k = GF(Int(prime(Q)))
  pro = function(x::padic)
    v = valuation(x)
    v < 0 && error("elt non integral")
    v > 0 && return k(0)
    z = k(lift(x))
    return z
  end
  lif = function(x::gfp_elem)
    z = Q(lift(x))
    return z
  end
  return k, MapFromFunc(pro, lif, Q, k)
end

################################################################################
#
#  Precision
#
################################################################################

function Base.setprecision(f::Generic.Poly{padic}, N::Int)
  f = deepcopy(f)
  for i=1:length(f)
    f.coeffs[i].N = N
  end
  return f
end

function setprecision!(f::Generic.Poly{padic}, N::Int)
  for i=1:length(f)
    f.coeffs[i].N = N
  end
  return f
end

################################################################################
#
#  Misc
#
################################################################################

@doc Markdown.doc"""
    prime_power(R::PadicField, i::Int)
> Returns the prime of the padic field raised to the power i. Mathematically 
> equivalent to `prime(R)^i`.
"""
function prime_power(R::PadicField, i::Int)
  p = fmpz()
  ccall((:padic_ctx_pow_ui, :libflint), Cvoid, (Ref{fmpz}, Int, Ref{PadicField}), p, i, R)
  return p
end

@doc Markdown.doc"""
    unit_part(a::padic) -> fmpz, Int64, Int64
> Returns the unit part of the padic number, along with the valuation and precision.
"""
function unit_part(a::padic)
  u = fmpz()
  ccall((:fmpz_set, :libflint), Cvoid, (Ref{fmpz}, Ref{Int}), u, a.u)
  return u
end


uniformizer(Q::FlintPadicField) = Q(prime(Q))
Base.precision(Q::FlintPadicField) = Q.prec_max

^(a::padic, b::padic) = exp(b*log(a))

################################################################################
#
#  Field invariants
#
################################################################################

degree(::FlintPadicField) = 1
