@testset "Maximal ideals over a polynomial PID" begin
  K, t = rational_function_field(GF(3))
  R = parent(numerator(t))
  G = small_group(2, 1)
  A = K[G]
  O = Hecke.new_order(A, R, identity_matrix(K, 2))
  p = gen(R)
  pO = p*O

  B = basis(O)
  BB = deepcopy(B)
  @test all(x -> parent(x) === O, BB)
  @test elem_in_algebra.(BB) == elem_in_algebra.(B)
  @test coordinates.(BB) == coordinates.(B)

  ideals = Hecke._maximal_ideals(O, pO, p)
  @test length(ideals) == 2
  @test ideals[1] != ideals[2]
  @test all(I -> Hecke.is_left_ideal(I) && Hecke.is_right_ideal(I), ideals)
  @test all(I -> issubset(pO, I), ideals)
  @test all(I -> issubset(Hecke.lattice(I), Hecke.lattice(O)), ideals)

  expected = [K[p 0; 1 1], K[p 0; 2 1]]
  actual = basis_matrix.(ideals)
  @test all(B -> any(==(B), actual), expected)
end

@testset "Maximal order computation" begin
  G = small_group(10, 1)
  QG = QQ[G]
  ZG = Hecke.new_order(QG, ZZ, basis(QG))
  O = maximal_order(ZG)
  @test discriminant(O) == 625

  G = small_group(2, 1)
  k, t = rational_function_field(GF(3), :t)
  kt = parent(numerator(t))
  QG = k[G]
  ktG = Hecke.new_order(QG, kt, basis(QG))
  R = Hecke.new_order(QG, kt, k[1 0; 0 t*(t + 1)])
  @test maximal_order(R) == ktG
end
