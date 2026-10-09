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

@testset "element validation and arithmetic" begin
  M = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
  from_coords(c) = Hecke._element_from_coordinates(M, ZZRingElem[c...])
  from_ambient(v) = Hecke._element_from_ambient_coordinates(M,
                                       QQFieldElem[v...]; check = false)
  both(c, v) = Hecke._element_from_coordinates_and_ambient_coordinates(M,
                            ZZRingElem[c...], QQFieldElem[v...]; check = false)

  @test_throws ArgumentError from_coords([1])
  @test_throws ArgumentError from_ambient([2])
  @test_throws ArgumentError both([1], [2, 3])
  @test_throws ArgumentError both([1, 1], [2])
  @test_throws ArgumentError Hecke._element_from_coordinates(M, ZZ[1 0; 0 1])
  @test_throws ArgumentError Hecke._element_from_coordinates_and_ambient_coordinates(
                                            M, ZZRingElem[1, 0], QQFieldElem[1, 0])

  for make_x in (from_coords, c -> from_ambient([2*c[1], 3*c[2]]),
                 c -> both(c, [2*c[1], 3*c[2]]))
    for make_y in (from_coords, c -> from_ambient([2*c[1], 3*c[2]]),
                   c -> both(c, [2*c[1], 3*c[2]]))
      x = make_x([2, -1])
      y = make_y([3, 4])
      z = x + y
      @test coordinates(z) == ZZRingElem[5, 3]
      @test Hecke.ambient_coordinates(z) == QQFieldElem[10, 9]
      @test coordinates(x) == ZZRingElem[2, -1]
      @test coordinates(y) == ZZRingElem[3, 4]
      @test x - y == from_coords([-1, -5])
      @test -x == from_coords([-2, 1])
      @test 3*x == x*ZZ(3) == from_coords([6, -3])
    end
  end

  x = from_coords([2, -1])
  y = from_ambient([4, -3])
  @test x == y
  @test hash(x) == hash(y)
  @test sprint(show, x) == sprint(show, y)
  @test iszero(zero(M))
  @test iszero(0*x)
  @test !iszero(x)
  N = Hecke.embedded_module(ZZ, QQ, QQ[2 0; 0 3])
  @test x != Hecke._element_from_coordinates(N, ZZRingElem[2, -1])
  @test_throws ArgumentError x + zero(N)
end

@testset "scalar embedding in function fields" begin
  K, x = rational_function_field(QQ, "x")
  R = parent(numerator(x))
  Rinf = localization(K, degree)
  for (S, t) in ((R, numerator(x)), (Rinf, Rinf(inv(x))))
    M = Hecke.embedded_module(S, K, K[1//x 0; 0 x])
    c = elem_type(S)[t, one(S)]
    v = typeof(x)[image(Hecke.fraction_map(M), t)//x, x]
    a = Hecke._element_from_coordinates(M, c)
    b = Hecke._element_from_ambient_coordinates(M, v; check = false)
    d = Hecke._element_from_coordinates_and_ambient_coordinates(M, c, v)
    for y in (a, b, d)
      z = t*y
      @test parent(z) === M
      @test eltype(coordinates(z)) == elem_type(S)
      @test coordinates(z) == t .* c
      @test Hecke.ambient_coordinates(z) == image(Hecke.fraction_map(M), t) .* v
      @test z == y*t
    end
  end
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

  ambient = nothing
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
