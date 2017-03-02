export ResidueField

function ResidueField(O::NfMaxOrd, P::NfMaxOrdIdl)
  if !isindex_divisor(O, minimum(P))
    @assert has_2_elem(P) && isprime_known(P)

    gtwo = P.gen_two

    f = nf(O).pol
    g = parent(f)(elem_in_nf(gtwo))

    if nbits(P.gen_one) < 64
      R = ResidueRing(FlintZZ, P.gen_one)

      Zy, y = PolynomialRing(FlintZZ, "y")
      Rx, x = PolynomialRing(R, "x")::Tuple{NmodPolyRing, nmod_poly}

      gmodp = Rx(Zy(g))::nmod_poly
      fmodp = Rx(Zy(f))::nmod_poly

      h = gcd(gmodp,fmodp)

      F = FqNmodFiniteField(h, :$)

      #return F, Mor(O, F, gen(F))
      g = Mor(O, F, h)
      g.P = P
      return F, g
    else
      error("Not yet implemented")
    end
  else
    f = NfMaxOrdToFqNmodMor(O, P)
    return codomain(f), f
  end
end

function disc_log(x::fq_nmod, g::fq_nmod)
  F = parent(x)
  q = order(F)
  h = g
  for i in 1:Int(q)-2
    if h == x
      return i
    end
    h = h*g
  end
  return i
end

function disc_log(x::fq_nmod, g::fq_nmod, p::Int)
  F = parent(x)
  q = order(F)
  @assert mod(q - 1, p) == 0
  l = div(q - 1, p)
  x = x^l
  g = g^l
  h = deepcopy(g)
  i = 1
  while i < p + 2
    if h == x
      return i
    end
    h = h*g
    i = i + 1
  end
  error("something odd")
end

