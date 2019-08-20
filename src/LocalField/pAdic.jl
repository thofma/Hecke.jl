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


function _content(f::Generic.Poly{padic})
  K = base_ring(f)
  p = prime(K)
  v = valuation(coeff(f, 0))
  for i = 1:degree(f)
    v = min(v, valuation(coeff(f, i)))
    if iszero(v)
      break
    end
  end
  return K(p)^v
end

function fun_factor(g::Generic.Poly{padic})
  K = base_ring(g)
  Kt = parent(g)
  p = prime(K)
  R = ResidueRing(FlintZZ, p^K.prec_max, cached = false)
  Rt = PolynomialRing(R, "t", cached = false)[1]
  fR = Rt([R(lift(coeff(g, i))) for i = 0:degree(g)])
  uR, g1R = fun_factor(fR)
  return Kt(fmpz[lift(coeff(uR, i)) for i = 0:degree(uR)]), Kt(fmpz[lift(coeff(g1R, i)) for i = 0:degree(g1R)])
end


function gcd(f::Generic.Poly{padic}, g::Generic.Poly{padic})
  
  if degree(f) < degree(g)
    return gcd(g, f)
  end
  cf = _content(f)
  if !isone(cf)
    f = divexact(f, cf)
  end
  cg = _content(g)
  if !isone(cg)
    g = divexact(g, cg)
  end
  if !iszero(valuation(lead(g)))
    u, g1 = fun_factor(g)
    if iszero(valuation(lead(f)))
      return gcd(f, g1)*reverse(gcd(reverse(f), reverse(u)))
    end
    v, f1 = fun_factor(f)
    return reverse(gcd(reverse(u), reverse(u)))*gcd(f1, g1)
  end 
  f = mod(f, g)
  if degree(f) < 1
    if iszero(f)
      return g
    else
      return one(parent(f))
    end
  else
    return gcd(g, f)
  end
end

function characteristic_polynomial(f::Generic.Poly{padic}, g::Generic.Poly{padic})
  Kt = parent(f)
  Ktx, x = PolynomialRing(Kt, "x")
  fcoeffs = Generic.Poly{padic}[Kt(coeff(f, i)) for i = 0:degree(f)]
  gcoeffs = Generic.Poly{padic}[Kt(-coeff(g, i)) for i = 0:degree(g)]
  f1 = Ktx(fcoeffs)
  g1 = Ktx(gcoeffs) + gen(Kt)
  return resultant(f1, g1)
end
