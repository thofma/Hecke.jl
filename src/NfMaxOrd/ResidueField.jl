export ResidueField

function ResidueField(O::NfMaxOrd, P::NfMaxOrdIdl)
  @assert !is_index_divisor(O, minimum(P))
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
  #println("disc log for $x $g $p")
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
      #println("disc log is $i")
      return i
    end
    h = h*g
    i = i + 1
  end
  #println("F: $F\nx: $x\ng: $g\np: $p")
  error("something odd")
end

