@testset "NfAbsNS" begin

  Qx, x = FlintQQ["x"]
  K, (a, b) = @inferred number_field([x^2 - 2, x^3 - 3])

  @test K isa NfAbsNS
  @test elem_type(NfAbsNS) == NfAbsNSElem
  @test parent_type(NfAbsNSElem) == NfAbsNS
  @test show_minus_one(NfAbsNSElem) isa Bool
  @test !issimple(K)
  @test !issimple(NfAbsNS)

  @testset "Basics" begin
    @test FlintQQ == @inferred base_ring(K)
    @test 6 == @inferred degree(K)
    @test [2, 3] == @inferred degrees(K)
    @test 2 == @inferred ngens(K)
    @test [a, b] == @inferred gens(K)
    @test [one(K), a, b, a * b, b^2, a * b^2] == @inferred basis(K)
    @test string(K) isa String
    @test string(a) isa String
  end

  @testset "Elements" begin
    c = @inferred deepcopy(a)
    @test parent(c) === K
    d = @inferred rand(K, -10:10)
    @test parent(d) === K
    e = @inferred zero(K)
    @test @inferred iszero(e)
    e = @inferred one(K)
    @test @inferred isone(e)

    for i in 1:10
      z = @inferred rand(K, -10:10)
      @test z == @inferred K(data(z))
    end

    for i in 1:10
      z = rand(K, -10:10)

      @test @inferred ==(z, z)
      @test !(@inferred ==(z, z + 1))

      zm = @inferred -z
      @test iszero(zm + z)

      y = rand(K, -10:10)
      w = rand(K, -10:10)
      @test z * y + w * y == @inferred (z + w) *y

      while iszero(z)
        z = rand(K, -10:10)
      end
      zinv = @inferred inv(z)
      @test isone(@inferred z * zinv)

      for T in [Int, BigInt, fmpq, fmpz]
        u = rand(-10:10)
        while iszero(u)
          u = rand(-10:10)
        end
        @test y + u == y + u
        @test y - u == -(u - y)
        @test y * u == u * y
        @test y//u == inv(K(u)//y)
      end

      u = rand(-10:10)
      @test @inferred z^u == @inferred z^fmpz(u)

      M = zero_matrix(FlintQQ, 1, 6)
      Hecke.elem_to_mat_row!(M, 1, z)
      @test z == sum(M[1, j] * basis(K)[j] for j in 1:6)
      M = matrix(FlintQQ, 1, 6, [rand(-10:10) for j in 1:6])
      zz = Hecke.elem_from_mat_row(K, M, 1)
      @test zz == sum(M[1, j] * basis(K)[j] for j in 1:6)

      f = @inferred minpoly(z)
      @test length(factor(f)) == 1 && first(factor(f))[2] == 1
      @test ismonic(f)
      @test iszero(f(z))

      f = @inferred Hecke.minpoly_sparse(z)
      @test length(factor(f)) == 1 && first(factor(f))[2] == 1
      @test ismonic(f)
      @test iszero(f(z))

      f = @inferred Hecke.minpoly_dense(z)
      @test length(factor(f)) == 1 && first(factor(f))[2] == 1
      @test ismonic(f)
      @test iszero(f(z))

      f = @inferred charpoly(z)
      @test length(factor(f)) == 1
      @test ismonic(f)
      @test iszero(f(z))
      @test degree(f) == 6

      M = @inferred representation_matrix(z)
      for i in 1:nrows(M)
        @test Hecke.elem_from_mat_row(K, M, i) == z * basis(K)[i]
      end

      n = @inferred norm(z)
      @test n == det(M)
      t = @inferred tr(z)
      @test t == tr(M)
    end
  end

  @testset "Morphisms" begin
    L, m = @inferred simple_extension(K)
    LL,  = number_field(x^6-6*x^4-6*x^3+12*x^2-36*x+1)
    @test isisomorphic(L, LL)[1]
    for i in 1:100
      z = rand(L, -10:10)
      zz = rand(L, -10:10)
      while iszero(z)
        z = rand(L, -10:10)
      end

      @test @inferred m(z + zz) == m(z) + m(zz)
      @test @inferred m(z * zz) == m(z) * m(zz)
      @test @inferred m(-z) == -m(z)
      @test @inferred m(inv(z)) == inv(m(z))
      @test m\m(z) == z
    end

    for i in 1:100
      z = rand(K, -10:10)
      zz = rand(K, -10:10)
      while iszero(z)
        z = rand(K, -10:10)
      end

      @test @inferred m\(z + zz) == m\(z) + m\(zz)
      @test @inferred m\(z * zz) == m\(z) * (m\(zz))
      @test @inferred m\(-z) == -(m\(z))
      @test @inferred m\(inv(z)) == inv(m\z)
      @test m(m\z) == z
    end
  end

  @testset "Maximal order" begin
    K2,  = @inferred number_field([x^2 - 50, x^3 - 3])
    O = EquationOrder(K2)
    Omax = @inferred MaximalOrder(O)
    @test discriminant(Omax) == FlintZZ(30233088)
  end

  @testset "rand" begin
    m = make(K, 1:3)
    for x in (rand(K, 1:3), rand(rng, K, 1:3), rand(m), rand(rng, m))
      @test x isa NfAbsNSElem
    end
    @test rand(m, 3) isa Vector{NfAbsNSElem}
    @test reproducible(m)
    @test reproducible(K, 1:3)
  end
end
