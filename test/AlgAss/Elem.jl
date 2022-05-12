@testset "Elements in algebras" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 1
  A = AlgAss(f)

  @testset "Is integral" begin
    @test Hecke.is_integral(A[1]) == true
    @test Hecke.is_integral(fmpq(1, 2)*A[1]) == false

    B = group_algebra(FlintQQ, small_group(2, 1))
    @test Hecke.is_integral(B[1]) == true
    @test Hecke.is_integral(fmpq(1, 2)*B[1]) == false

    C = matrix_algebra(FlintQQ, B, 2)
    @test Hecke.is_integral(C[1]) == true
    @test Hecke.is_integral(fmpq(1, 2)*C[1]) == false
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

end
