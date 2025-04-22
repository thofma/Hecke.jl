function monic_randpoly(S::PolyRing, dmin::Int, dmax::Int, n::Int)
  r = S()
  R = base_ring(S)
  d = rand(dmin:dmax)
  for i = 0:d - 1
    setcoeff!(r, i, R(rand(-n:n)))
  end
  setcoeff!(r, d, R(1))
  return r
end

@testset "Relative maximal orders of simple extensions" begin
  Qx, x = QQ["x"]
  f = x^2 + 36*x + 16
  K, a = number_field(f, "a", cached = false)
  Ky, y = K["y"]
  g = y^3 - 51*y^2 + 30*y - 28
  L, b = number_field(g, "b", cached = false)
  Orel = maximal_order(L)
  Oabs = Hecke.maximal_order_via_absolute(L)
  Brel = Hecke.basis_pmatrix(Orel, copy = false)
  Babs = Hecke.basis_pmatrix(Oabs, copy = false)
  @test Hecke._spans_subset_of_pseudohnf(Brel, Babs; shape = :lowerleft)
  @test Hecke._spans_subset_of_pseudohnf(Babs, Brel; shape = :lowerleft)

  for i = 1:1
    f = monic_randpoly(Qx, 2, 3, 10)
    while !is_irreducible(f)
      f = monic_randpoly(Qx, 2, 3, 10)
    end
    K, a = number_field(f, "a", cached = false)

    Ky, y = K["y"]
    g = monic_randpoly(Ky, 2, 2, 10)
    while !is_irreducible(g)
      g = monic_randpoly(Ky, 2, 2, 10)
    end
    L, b = number_field(g, "b", cached = false)

    Orel = maximal_order(L)
    Oabs = Hecke.maximal_order_via_absolute(L)
    Brel = Hecke.basis_pmatrix(Orel, copy = false)
    Babs = Hecke.basis_pmatrix(Oabs, copy = false)
    @test Hecke._spans_subset_of_pseudohnf(Brel, Babs; shape = :lowerleft)
    @test Hecke._spans_subset_of_pseudohnf(Babs, Brel; shape = :lowerleft)
  end

  f = x^4 - 2*x^3 - 353*x^2 + 354*x + 24014;
  K, _a = number_field(f, "a", cached = false);
  Kt, t = polynomial_ring(K, "x");
  g = t^4 + (56//27*_a^3 - 208//9*_a^2 - 19216//27*_a +
      272764//27)*t^2 - 1384442//621*_a^3 + 8616181//207*_a^2 +
      92116642//621*_a - 1987471894//621;
  L, b = number_field(g, cached = false);
  OL = maximal_order(L);
  @test absolute_discriminant(OL) == ZZRingElem(137541748061317337716214471065600000000)

  K, a = number_field(x, "a")
  Ky, y = K["y"]
  for i = 1:1
    f = monic_randpoly(Ky, 5, 5, 10)
    while !is_irreducible(f)
      f = monic_randpoly(Ky, 5, 5, 10)
    end
    L, b = number_field(f, "b", cached = false)

    Orel = maximal_order(L)
    Oabs = Hecke.maximal_order_via_absolute(L)
    Brel = Hecke.basis_pmatrix(Orel, copy = false)
    Babs = Hecke.basis_pmatrix(Oabs, copy = false)
    @test Hecke._spans_subset_of_pseudohnf(Brel, Babs; shape = :lowerleft)
    @test Hecke._spans_subset_of_pseudohnf(Babs, Brel; shape = :lowerleft)
  end
end


@testset "Relative maximal orders of non-simple extensions" begin
  Qx, x = QQ["x"]

  K, a = number_field(x, "a")
  OK = maximal_order(K)
  Ky, y = K["y"]

  L, b = number_field([y^3 - 51*y^2 + 30*y - 28, y^4 + 1], "b", cached = false)
  Ons = maximal_order(L)
  Bns = Hecke.basis_pmatrix(Ons, copy = false)

  Ms = identity_matrix(K, 12)
  Cs = [ ideal(OK, K(1)) for i = 1:12 ]
  for i in [3, 6, 9, 12]
    Ms[i, i - 1] = K(1)
    Cs[i] = ideal(OK, K(QQFieldElem(1, 2)))
  end
  Bs = Hecke.pseudo_matrix(Ms, Cs)
  @test Hecke._spans_subset_of_pseudohnf(Bns, Bs; shape = :lowerleft)
  @test Hecke._spans_subset_of_pseudohnf(Bs, Bns; shape = :lowerleft)

  K, a = number_field(x^2 - 2*x + 38, "a", cached = false)
  OK = maximal_order(K)
  Ky, y = K["y"]

  L, b = number_field([y^2 + 87*y + 74, y^2 + 91*y - 73, y^2 - 30*y - 51], "b", cached = false)
  Ons = maximal_order(L)
  Bns = Hecke.basis_pmatrix(Ons, copy = false)

  Ms = identity_matrix(K, 8)
  Cs = [ ideal(OK, K(1)) for i = 1:8 ]
  for i = 5:8
    Ms[i, i - 4] = K(3)
    Cs[i] = ideal(OK, K(QQFieldElem(1, 4)))
  end
  Bs = Hecke.pseudo_matrix(Ms, Cs)
  @test Hecke._spans_subset_of_pseudohnf(Bns, Bs; shape = :lowerleft)
  @test Hecke._spans_subset_of_pseudohnf(Bs, Bns; shape = :lowerleft)

  for i = 1:1
    f = monic_randpoly(Qx, 2, 2, 10)
    while !is_irreducible(f)
      f = monic_randpoly(Qx, 2, 2, 10)
    end
    K, a = number_field(f, "a")

    Ky, y = K["y"]
    g = Vector{Generic.Poly{AbsSimpleNumFieldElem}}()
    h = monic_randpoly(Ky, 2, 2, 10)
    while !is_irreducible(h)
      h = monic_randpoly(Ky, 2, 2, 10)
    end
    push!(g, h)
    gg = monic_randpoly(Ky, 3, 3, 10) # Must be coprime to 2
    while gg == g[1] || !is_irreducible(gg) || is_isomorphic(number_field(g[1], cached = false)[1], number_field(gg, cached = false)[1])
      gg = monic_randpoly(Ky, 3, 3, 10) # Must be coprime to 2
    end
    push!(g, gg)
    L, b = number_field(g, "b", cached = false)

    Ons = maximal_order(L)
    Os = Hecke.maximal_order_via_simple(L)
    Bns = Hecke.basis_pmatrix(Ons, copy = false)
    Bs = Hecke.basis_pmatrix(Os, copy = false)
    @test Hecke._spans_subset_of_pseudohnf(Bns, Bs; shape = :lowerleft)
    @test Hecke._spans_subset_of_pseudohnf(Bs, Bns; shape = :lowerleft)
  end
end

@testset "Field towers" begin
   Qx, x = QQ["x"]

  Q1, q1 = number_field(x, "q1", cached = false)
  Z1 = maximal_order(Q1)
  Qx1, x1 = Q1["x1"]
  f1 = x1^2 + 28x1 + 36
   K1, a1 = number_field(f1, "a1", cached = false)
  OK1 = maximal_order(K1)
  PM1 = pseudo_matrix(matrix(Q1, [1 0; 2 1]), [ Q1(1)*Z1, Q1(QQFieldElem(1, 4))*Z1 ])
  @test basis_pmatrix(OK1, copy = false) == PM1

  Q2, q2 = number_field(x1, "q2", cached = false)
  Z2 = maximal_order(Q2)
  Qx2, x2 = Q2["x2"]
  f2 = x2^2 + 28x2 + 36
   K2, a2 = number_field(f2, "a2", cached = false)
  OK2 = maximal_order(K2)
  PM2 = pseudo_matrix(matrix(Q2, [1 0; 2 1]), [ Q2(1)*Z2, Q2(QQFieldElem(1, 4))*Z2 ])
  @test basis_pmatrix(OK2, copy = false) == PM2

  #Q3, q3 = number_field(x2, "q3")
  #Z3 = maximal_order(Q3)
  #Qx3, x3 = Q3["x3"]
  #f3 = x3^2 + 28x3 + 36
  # K3, a3 = number_field(f3, "a3")
  #OK3 = maximal_order(K3)
  #PM3 = pseudo_matrix(matrix(Q3, [1 0; 2 1]), [ Q3(1)*Z3, Q3(QQFieldElem(1, 4))*Z3 ])
  #@test basis_pmatrix(OK3, copy = false) == PM3
end

@testset "Different/codifferent" begin
  Qx, x = polynomial_ring(QQ, "x", cached = false)
  f = x^2 - 2
  K, a = number_field(f, "a", cached = false)
  Kt, t = K["t"]
  g = t^2 + 1
  E, b = number_field(g, "b", cached = false)
  OE = maximal_order(E)
  p = prime_decomposition(maximal_order(K), 2)[1][1]
  Q = prime_decomposition(OE, p)[1][1]
  @assert ramification_index(Q) == 2
  D = @inferred different(OE)
  @test valuation(D, Q) == 2
end

@testset "rand" begin
  Qx, x = QQ["x"]
  f = x^2 + 36*x + 16
  K, a = number_field(f, "a")
  Ky, y = K["y"]
  g = y^3 - 51*y^2 + 30*y - 28
  L, b = number_field(g, "b")
  Orel = maximal_order(L)

  m = make(Orel, 3)
  for x in (rand(Orel, 3), rand(rng, Orel, 3), rand(m), rand(rng, m))
    @test x isa elem_type(Orel)
  end
  @test rand(m, 3) isa Vector{elem_type(Orel)}
  @test reproducible(Orel, 3)
  @test reproducible(m)
end

# extend not implemented yet
K, a = quadratic_field(5)
Kt, t = K["t"]
L, b = number_field(polynomial(K, [-2, 0, 0, 1]), "b");
@test_throws Hecke.NotImplemented extend(equation_order(L), [b])

# Towards non-nice equations

begin
  Qx, x = QQ["x"]
  K, a = number_field(x - 1)
  Kt, t = K["t"]
  L, b = number_field(t^2 + 1//2)
  c = Hecke._integral_multiplicator(b)
  @test is_integral(c * b)
  O = any_order(L)
  @test Hecke.nf(O) === L
  L, b = number_field([t^2 + 1//2])
  O = any_order(L)
  @test Hecke.nf(O) === L
end

# hash
let
  Qx, x = QQ["x"]
  f = x^2 + 36*x + 16
  K, a = number_field(f, "a", cached = false)
  Ky, y = K["y"]
  g = y^3 - 51*y^2 + 30*y - 28
  L, b = number_field(g, "b", cached = false)
  P = pseudo_matrix(identity_matrix(K, 3))
  @test order(L, P) == order(L, P)
  @test order(L, P) !== order(L, P)
  @test hash(order(L, P)) == hash(order(L, P))
end
