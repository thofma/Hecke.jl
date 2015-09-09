export ResidueField

function ResidueField(O::NfMaximalOrder, P::NfMaximalOrderIdeal)
  @assert has_2_elem(P) && is_prime_known(P)

  x = P.gen_two

  f = nf(O).pol
  g = parent(f)(elem_in_nf(x))

  R = ResidueRing(FlintZZ, P.gen_one)

  Zy, y = PolynomialRing(FlintZZ, "y")
  Rx, x = PolynomialRing(R, "x")

  gmodp = Rx(Zy(g))
  fmodp = Rx(Zy(f))

  h = gcd(gmodp,fmodp)

  F = FqNmodFiniteField(h, :$)

  return F, Mor(O, F, gen(F))
end

