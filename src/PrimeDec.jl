################################################################################
#
#  PrimeDec.jl: Prime decomposition in absolute number fields
#
################################################################################

export prime_decomposition, prime_decomposition_type

function prime_decomposition(O::PariMaximalOrder, p::Integer)
  if mod(ZZ(index(O)),p) == 0
    error("not implemented yet")
  end
  return prime_dec_nonindex(O, p)
end

function prime_dec_nonindex(O::PariMaximalOrder, p::Integer)
   f = O.pari_nf.nf.pol
   K = O.pari_nf.nf
   I = IdealSet(O)
   R = parent(f)
   Zx, x = PolynomialRing(ZZ,"x")
   Zf = Zx(f)
   fmodp = nmod_poly(UInt(p),Zf)
   fac = _factor(fmodp)
   result = Array(Tuple{typeof(I()),Int}, length(fac))
   t = fmpq_poly()
   b = K()
  
  fill!(result,(I(),0))

  for k in 1:length(fac)
    t = fmpq_poly(_lift(fac[k][1]))
    t.parent = f.parent

    b = K(t)

    ideal = I()
    ideal.gen_one = p
    ideal.gen_two = b
    ideal.is_prime = 1
    ideal.parent = I
    ideal.splitting_type = fac[k][2], degree(fac[k][1])
    ideal.norm = ZZ(p)^degree(fac[k][1])
    ideal.minimum = ZZ(p)

    # We have to do something to get 2-normal presentation:
    # if ramified or valuation val(b,P) == 1, (p,b)
    # is a P(p)-normal presentation
    # otherwise we need to take p+b
    # I SHOULD CHECK THAT THIS WORKS

    if !((mod(norm(b),(ideal.norm)^2) != 0) || (fac[k][2] > 1))
      ideal.gen_two  = K(p) + b
    end

    ideal.gens_are_normal = p
    ideal.gens_are_weakly_normal = 1

    result[k] =  (ideal, fac[k][2])
  end
  return result
end

function prime_decomposition_type(O::PariMaximalOrder, p::Int)
  f = O.pari_nf.nf.pol
  K = O.pari_nf.nf
  R = parent(f)
  Zx, x = PolynomialRing(ZZ,"x")
  Zf = Zx(f)
  fmodp = NmodPolyRing(ResidueRing(ZZ,p),:y)(Zf)
  fac = factor_shape(fmodp)
  return fac
end
