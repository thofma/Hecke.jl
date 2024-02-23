@testset "Elements in algebras" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 1
  A = StructureConstantAlgebra(f)

  @testset "Is integral" begin
    @test Hecke.is_integral(A[1]) == true
    @test Hecke.is_integral(QQFieldElem(1, 2)*A[1]) == false

    B = group_algebra(FlintQQ, small_group(2, 1))
    @test Hecke.is_integral(B[1]) == true
    @test Hecke.is_integral(QQFieldElem(1, 2)*B[1]) == false

    C = matrix_algebra(FlintQQ, B, 2)
    @test Hecke.is_integral(C[1]) == true
    @test Hecke.is_integral(QQFieldElem(1, 2)*C[1]) == false
  end

  @testset "Characteristic polynomial" begin
    K, a = number_field(f, "a")

    b = rand(K, -10:10)
    c = A(coefficients(b))

    cpb = charpoly(b)
    cpc = charpoly(c)
    rcpc = reduced_charpoly(c)

    # We have to compare the polynomials by hand as they live in "different" polynomial rings...
    for p in [ cpc, rcpc ]
      for i = 0:2
        @test coeff(p, i) == coeff(cpb, i)
      end
    end

    mpb = minpoly(b)
    mpc = minpoly(c)

    @test degree(mpb) == degree(mpc)
    for i = 0:2
      @test coeff(mpb, i) == coeff(mpc, i)
    end
  end

  # Fix reduced char poly
  A = Hecke.QuaternionAlgebra(QQ, QQ(-1), QQ(-1))
  M = matrix_algebra(QQ, A, 2)
  a = A(QQFieldElem[0, -2, -1, 1])
  b = A(QQFieldElem[0, 1, -2, -1//2])
  m = M(matrix(A, 2, 2, [a, 0, 0, b]))
  @test normred(m) == 63//2
  @test normred(m) == normred(a * b) == normred(a) * normred(b)

  g = reduced_charpoly(m)
  x = gen(parent(g))
  @test g == x^4 + 45//4 * x^2 + 63//2

  # mul! for matrix algebra elements
  A = matrix_algebra(QQ, 2)
  @test isone(mul!(zero(A), one(A), ZZRingElem(1)))
end
