export dedekind_test, dedekind_poverorder, dedekind_ispmaximal

function dedekind_ispmaximal(O::NfOrder, p::fmpz)
  !isequationorder(O) && error("Order must be an equation order")
  if rem(discriminant(O), p) != 0
    return true, O
  end

  pmaximal=true

  p
  Zy, y = PolynomialRing(ZZ, "y")
  Kx, x = PolynomialRing(ResidueRing(ZZ, p), "x")

  f = nf(O).pol

  Zyf = Zy(f)

  fmodp = Kx(Zyf)
 
  fac = factor(fmodp)

  g = Zy(1)

  # first build 1/p ( f - prod_{g in fac} g^?)
  for i in 1:length(fac)
    g *= lift(Zy, fac[i][1])^fac[i][2]
  end

  g = Zyf - g

  for i in 0:degree(g)
    q,r = divrem(coeff(g,i),p)
    @assert r == 0
    setcoeff!(g,i,q)
  end

  gmodp = Kx(g)

  U = one(Kx)

  for i in 1:length(fac)
    if fac[i][2] != 1 && rem(gmodp, fac[i][1]) == zero(Kx)
      U *= fac[i][1]
      return false
    end
  end

  return true
end

function dedekind_ispmaximal(O::NfOrder, p::Integer)
  return dedekind_ispmaximal(O, ZZ(p))
end

function dedekind_poverorder(O::NfOrder, p::fmpz)
  _, O = dedekind_test(O, p)
  return O
end

function dedekind_poverorder(O::NfOrder, p::Integer)
  return dedekind_poverorder(O, ZZ(p))
end

function dedekind_test(O::NfOrder, p::fmpz)
  !isequationorder(O) && error("Order must be an equation order")
  
  if rem(discriminant(O), p) != 0
    return true, O
  end

  pmaximal=true

  p 
  
  Zy, y = PolynomialRing(ZZ, "y")
  Kx, x = PolynomialRing(ResidueRing(ZZ, p), "x")


  f = nf(O).pol

  Zyf = Zy(f)

  fmodp = Kx(Zyf)
 
  fac = factor(fmodp)


  g = Zy(1)

  # first build 1/p ( f - prod_{g in fac} g^?)
  for i in 1:length(fac)
    g *= lift(Zy, fac[i][1])^fac[i][2]
  end

  g = Zyf - g

  for i in 0:degree(g)
    q,r = divrem(coeff(g,i),p)
    @assert r == 0
    setcoeff!(g,i,q)
  end

  gmodp = Kx(g)

  U = one(Kx)

  for i in 1:length(fac)
    if fac[i][2] != 1 && rem(gmodp, fac[i][1]) == zero(Kx)
      U *= fac[i][1]
      pmaximal=false
    end
  end

  @assert rem(fmodp, U) == zero(Kx)
  U = divexact(fmodp, U)

  if pmaximal
    return true, O
  end

  @assert rem(discriminant(O),p^2) == 0

  alpha = nf(O)(parent(f)(lift(Zy,U)))

  # build the new basis matrix
  # we have to take the representation matrix of alpha!
  # concatenating the coefficient vector won't help
  n = vcat(num(basis_mat(O))*p,representation_mat(alpha))

  b = FakeFmpqMat(n,p)

  OO = Order(nf(O), sub(hnf(b),degree(O) + 1:2*degree(O), 1:degree(O)))

  OO.isequationorder = false

  OO.disc = divexact(discriminant(O),p^(2*(degree(O)-degree(U))))

  return false, OO
end

function dedekind_test(O::NfOrder, p::Integer)
  return dedekind_test(O, ZZ(p))
end
