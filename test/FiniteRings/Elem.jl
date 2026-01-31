@testset "FiniteRing/Elem" begin
  mats = [[1 0 0 0; 0 0 0 0; 0 0 1 0; 0 0 0 0], [0 1 0 0; 0 0 0 0; 0 0 0 1; 0 0 0 0], [0 0 0 0; 1 0 0 0; 0 0 0 0; 0 0 1 0], [0 0 0 0; 0 1 0 0; 0 0 0 0; 0 0 0 1]]
  R = finite_ring([2, 2, 2, 2], matrix.(Ref(ZZ), mats)) # M_2(F_2)

  @test R isa NCRing
  @test is_exact_type(R)

  z = R()
  @test parent(z) === R
  @test R(z) === z

  for T in (Int, ZZ, BigInt)
    @test is_zero(R(zero(T)))
    @test is_zero(R(T(2)))
    @test is_one(R(T(1)))
  end

  z = zero(R)
  o = one(R)
  o = one(R) # twice to check caching
  m = R([1, 1, 0, 1])
  n = R([1, 0, 0, 0])
  p = rand(R)

  for x in [z, o, m, n, p]
    @test parent(x) === R
    @test z + m == m + z
    @test z - m == -(m - z)
    @test o * m == m == o * m
  end

  fl, mm = is_invertible(n)
  @test !fl
  @test !is_unit(n)

  fl, mm = is_invertible(m)
  @test fl
  @test is_unit(m)
  @test mm * m == mm * m == o
  mm = inv(m)
  @test m * mm == mm * m == o

  for x in [z, o, m, n, p]
    @test x^0 == o
    @test x^1 == x
    @test x^3 == x * x * x
    @test 1*x == x * 1 == x
    @test ZZ(1)*x == x * ZZ(1) == x
    @test ZZ(0)*x == x * ZZ(0) == z
  end

  @test m^-1 == inv(m)
  @test m^-3 == inv(m) * inv(m) * inv(m)

  @test sprint(show, z) isa String
  @test sprint(show, "text/plain", z) isa String
  @test sprint(show, "text/plain", zero_matrix(R, 2, 2)) isa String

  # conformance tests
  Hecke.AbstractAlgebra.ConformanceTests.test_NCRing_interface(R)

  R = finite_ring([1], [zero_matrix(ZZ, 1, 1)])
  Hecke.AbstractAlgebra.ConformanceTests.test_NCRing_interface(R)
end
