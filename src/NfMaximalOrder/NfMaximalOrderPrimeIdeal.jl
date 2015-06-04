export prime_decomposition, prime_decomposition_type, prime_ideals_up_to

function prime_decomposition(O::NfMaximalOrder, p::Integer)
  if mod(ZZ(index(O)),p) == 0
    # fall back to pari
    OO = PariMaximalOrder(PariNumberField(nf(O)))
    l = prime_decomposition(OO, p)
    P = IdealSet(O)
    Q = P(l[1])
    r = Array(Tuple{typeof(Q), Int}, lg(l.data)-1)
    r[1] = (Q, Q.splitting_type[1])
    for i = 2:lg(l.data)-1
      Q = P(l[i])
      r[i] = (Q, Q.splitting_type[1])
    end
    return r
  end
  return prime_dec_nonindex(O, p)
end

function prime_dec_nonindex(O::NfMaximalOrder, p::Integer)
  K = nf(O)
  f = K.pol
  I = IdealSet(O)
  R = parent(f)
  Zx, x = PolynomialRing(ZZ,"x")
  Zf = Zx(f)
  fmodp = PolynomialRing(ResidueRing(ZZ, p), "y")[1](Zf)
  fac = factor(fmodp)
  result = Array(Tuple{typeof(I()),Int}, length(fac))
  t = fmpq_poly()
  b = K()
  
  fill!(result,(I(),0))

  for k in 1:length(fac)
    t = parent(f)(lift(Zx,fac[k][1]))

    b = K(t)

    ideal = I()
    ideal.gen_one = p
    ideal.gen_two = O(b, check = false)
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
      ideal.gen_two = ideal.gen_two + O(p)
    end

    ideal.gens_are_normal = p
    ideal.gens_are_weakly_normal = 1

    if length(fac) == 1 && ideal.splitting_type[1] == 1
      # Prime number is inert, in particular principal
      ideal.is_principal = 1
      ideal.princ_gen = O(p)
    end
    result[k] =  (ideal, fac[k][2])
  end
  return result
end

function prime_decomposition_type(O::NfMaximalOrder, p::Integer)
  K = nf(O)
  f = K.pol
  R = parent(f)
  Zx, x = PolynomialRing(ZZ,"x")
  Zf = Zx(f)
  fmodp = PolynomialRing(ResidueRing(ZZ,p), "y")(Zf)
  fac = factor_shape(fmodp)
  return fac
end

function prime_ideals_up_to(O::NfMaximalOrder, B::Int;
                            complete = true,
                            degree_limit = 5)
  p = 1
  r = NfMaximalOrderIdeal[]
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    li = prime_decomposition(O, p)
    if !complete
      for P in li
        if norm(P[1]) <= B && P[1].splitting_type[2] < degree_limit
          push!(r, P[1])
        end
      end
    else
      for P in li
        push!(r, P[1])
      end
    end
  end
  return r
end

