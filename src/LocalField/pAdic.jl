################################################################################
#
#  Lifting methods
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
#  Field invariants
#
################################################################################

degree(::FlintPadicField) = 1
