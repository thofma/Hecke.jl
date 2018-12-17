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

function isirreducible(f::PolyElem)
  fac = factor(f)
  if length(fac) != 1
    return false
  end
  if first(values(fac.fac)) != 1
    return false
  end
  return true
end

@testset "Relative maximal orders of simple extensions" begin
   Qx, x = FlintQQ["x"]
  f = x^2 + 36*x + 16
  K, a = NumberField(f, "a")
  Ky, y = K["y"]
  g = y^3 - 51*y^2 + 30*y - 28
  L, b = number_field(g, "b")
  Orel = maximal_order(L)
  Oabs = Hecke.maximal_order_via_absolute(L)
  Brel = Hecke.basis_pmat(Orel, Val{false})
  Babs = Hecke.basis_pmat(Oabs, Val{false})
  @test Hecke._spans_subset_of_pseudohnf(Brel, Babs, :lowerleft)
  @test Hecke._spans_subset_of_pseudohnf(Babs, Brel, :lowerleft)

  for i = 1:1
    f = monic_randpoly(Qx, 2, 3, 100)
    while !isirreducible(f)
      f = monic_randpoly(Qx, 2, 3, 100)
    end
    K, a = NumberField(f, "a")

    Ky, y = K["y"]
    g = monic_randpoly(Ky, 2, 3, 100)
    while !isirreducible(g)
      g = monic_randpoly(Ky, 2, 3, 100)
    end
    L, b = number_field(g, "b")

    Orel = maximal_order(L)
    Oabs = Hecke.maximal_order_via_absolute(L)
    Brel = Hecke.basis_pmat(Orel, Val{false})
    Babs = Hecke.basis_pmat(Oabs, Val{false})
    @test Hecke._spans_subset_of_pseudohnf(Brel, Babs, :lowerleft)
    @test Hecke._spans_subset_of_pseudohnf(Babs, Brel, :lowerleft)
  end

  K, a = NumberField(x, "a")
  Ky, y = K["y"]
  for i = 1:1
    f = monic_randpoly(Ky, 8, 10, 100)
    while !isirreducible(f)
      f = monic_randpoly(Ky, 8, 10, 100)
    end
    L, b = number_field(f, "b")

    Orel = maximal_order(L)
    Oabs = Hecke.maximal_order_via_absolute(L)
    Brel = Hecke.basis_pmat(Orel, Val{false})
    Babs = Hecke.basis_pmat(Oabs, Val{false})
    @test Hecke._spans_subset_of_pseudohnf(Brel, Babs, :lowerleft)
    @test Hecke._spans_subset_of_pseudohnf(Babs, Brel, :lowerleft)
  end
end


@testset "Relative maximal orders of non-simple extensions" begin
  Qx, x = FlintQQ["x"]

  K, a = NumberField(x, "a")
  OK = maximal_order(K)
  Ky, y = K["y"]

  L, b = number_field([y^3 - 51*y^2 + 30*y - 28, y^4 + 1], "b")
  Ons = maximal_order(L)
  Bns = Hecke.basis_pmat(Ons, Val{false})

  Ms = identity_matrix(K, 12)
  Cs = [ ideal(OK, K(1)) for i = 1:12 ]
  for i in [3, 6, 9, 12]
    Ms[i, i - 1] = K(1)
    Cs[i] = ideal(OK, K(fmpq(1, 2)))
  end
  Bs = Hecke.PseudoMatrix(Ms, Cs)
  @test Hecke._spans_subset_of_pseudohnf(Bns, Bs, :lowerleft)
  @test Hecke._spans_subset_of_pseudohnf(Bs, Bns, :lowerleft)

  K, a = NumberField(x^2 - 2*x + 38, "a")
  OK = maximal_order(K)
  Ky, y = K["y"]

  L, b = number_field([y^2 + 87*y + 74, y^2 + 91*y - 73, y^2 - 30*y - 51], "b")
  Ons = maximal_order(L)
  Bns = Hecke.basis_pmat(Ons, Val{false})

  Ms = identity_matrix(K, 8)
  Cs = [ ideal(OK, K(1)) for i = 1:8 ]
  for i = 5:8
    Ms[i, i - 4] = K(3)
    Cs[i] = ideal(OK, K(fmpq(1, 4)))
  end
  Bs = Hecke.PseudoMatrix(Ms, Cs)
  @test Hecke._spans_subset_of_pseudohnf(Bns, Bs, :lowerleft)
  @test Hecke._spans_subset_of_pseudohnf(Bs, Bns, :lowerleft)

  for i = 1:1
    f = monic_randpoly(Qx, 2, 2, 100)
    while !isirreducible(f)
      f = monic_randpoly(Qx, 2, 2, 100)
    end
    K, a = NumberField(f, "a")

    Ky, y = K["y"]
    g = Vector{Generic.Poly{nf_elem}}()
    gg = monic_randpoly(Ky, 2, 2, 100)
    while !isirreducible(gg)
      gg = monic_randpoly(Ky, 2, 2, 100)
    end
    push!(g, gg)
    gg = monic_randpoly(Ky, 2, 2, 100)
    while gg == g[1] || !isirreducible(gg)
      gg = monic_randpoly(Ky, 2, 2, 100)
    end
    push!(g, gg)
    L, b = number_field(g, "b")

    Ons = maximal_order(L)
    Os = Hecke.maximal_order_via_simple(L)
    Bns = Hecke.basis_pmat(Ons, Val{false})
    Bs = Hecke.basis_pmat(Os, Val{false})
    @test Hecke._spans_subset_of_pseudohnf(Bns, Bs, :lowerleft)
    @test Hecke._spans_subset_of_pseudohnf(Bs, Bns, :lowerleft)
  end
end

@testset "Field towers" begin
   Qx, x = FlintQQ["x"]

  Q1, q1 = number_field(x, "q1")
  Z1 = maximal_order(Q1)
  Qx1, x1 = Q1["x1"]
  f1 = x1^2 + 28x1 + 36
   K1, a1 = number_field(f1, "a1")
  OK1 = maximal_order(K1)
  PM1 = PseudoMatrix(matrix(Q1, [1 0; 2 1]), [ Q1(1)*Z1, Q1(fmpq(1, 4))*Z1 ])
  @test basis_pmat(OK1, Val{false}) == PM1

  Q2, q2 = number_field(x1, "q2")
  Z2 = maximal_order(Q2)
  Qx2, x2 = Q2["x2"]
  f2 = x2^2 + 28x2 + 36
   K2, a2 = number_field(f2, "a2")
  OK2 = maximal_order(K2)
  PM2 = PseudoMatrix(matrix(Q2, [1 0; 2 1]), [ Q2(1)*Z2, Q2(fmpq(1, 4))*Z2 ])
  @test basis_pmat(OK2, Val{false}) == PM2

  Q3, q3 = number_field(x2, "q3")
  Z3 = maximal_order(Q3)
  Qx3, x3 = Q3["x3"]
  f3 = x3^2 + 28x3 + 36
   K3, a3 = number_field(f3, "a3")
  OK3 = maximal_order(K3)
  PM3 = PseudoMatrix(matrix(Q3, [1 0; 2 1]), [ Q3(1)*Z3, Q3(fmpq(1, 4))*Z3 ])
  @test basis_pmat(OK3, Val{false}) == PM3
end
