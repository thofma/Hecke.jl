@testset "elements and coordinates" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])

  a = Hecke._element_from_ambient_coordinates(M, QQFieldElem[4, 6])
  @test elem_type(M) == typeof(a)
  @test parent(a) === M
  @test coordinates(a) == ZZRingElem[2, 2]
  @test_throws ArgumentError Hecke._element_from_ambient_coordinates(M,
                                                                      QQFieldElem[1, 0])

  alazy = Hecke._element_from_ambient_coordinates(M, QQFieldElem[4, 6];
                                                   check = false)
  @test coordinates(alazy) == ZZRingElem[2, 2]
  @test coordinates(alazy; copy = false) === coordinates(alazy; copy = false)

  abad = Hecke._element_from_ambient_coordinates(M, QQFieldElem[1, 0];
                                                  check = false)
  @test_throws ErrorException coordinates(abad)

  b = Hecke._element_from_coordinates(M, ZZRingElem[2, -1])
  c = Hecke._element_from_coordinates(M, ZZ[3 4])
  @test parent(b) === M
  @test coordinates(b) == ZZRingElem[2, -1]
  @test coordinates(c) == ZZRingElem[3, 4]
  @test_throws AssertionError Hecke._element_from_ambient_coordinates(M,
                                                                      ZZRingElem[4, 6])
  @test_throws AssertionError Hecke._element_from_coordinates(M,
                                                               QQFieldElem[1, 0])
end

@testset "pseudo elements and Dedekind domains" begin
  p = Hecke._pseudo_element(QQ(2), ZZ)
  q = Hecke._pseudo_element(QQ(3), ZZ)
  pq = p*q
  @test Hecke.element(pq) == QQ(6)
  @test Hecke.fractional_ideal(pq) === nothing

  p_with_ideal = Hecke._pseudo_element(QQ(1), ZZ)
  @test Hecke.element(p_with_ideal) == QQ(1)
  @test Hecke.fractional_ideal(p_with_ideal) === nothing

  MZZ = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
  @test Hecke._pseudo_element(QQFieldElem[2, 3], ZZ) in MZZ

  K, = quadratic_field(5)
  O = maximal_order(K)
  M = Hecke.embedded_module(O, K, pseudo_matrix(identity_matrix(K, 2)))
  v = elem_type(K)[K(1), K(0)]
  w = elem_type(K)[K(1)//2, K(0)]

  @test Hecke.ambient_rank(M) == 2
  @test nrows(matrix(basis_matrix(M))) == 2
  @test Hecke._pseudo_element(v, O) in M
  @test !(Hecke._pseudo_element(w, O) in M)

  N = Hecke.embedded_module(O, K, 2*basis_matrix(M))
  @test M + N == M
  @test intersect(M, N) == N

  ambient = Ref(:ambient)
  I = fractional_ideal(O, one(O))
  Z = Hecke.embedded_module(O, K,
                            pseudo_matrix(O, zero_matrix(K, 0, 2), typeof(I)[]);
                            overstructure = ambient)
  M1 = Hecke.embedded_module(O, K, pseudo_matrix(O, K[1 0], [I]);
                             overstructure = ambient, is_basis_matrix = true)
  M2 = Hecke.embedded_module(O, K, pseudo_matrix(O, identity_matrix(K, 2), [I, I]);
                             overstructure = ambient, is_basis_matrix = true)

  @test intersect(Z, M2) == Z
  @test intersect(M1, M2) == M1
end
