@testset "AbsNonSimpleNumField" begin

  Qx, x = FlintQQ["x"]
  K, (a, b) = @inferred number_field([x^2 - 2, x^3 - 3])

  @test K isa AbsNonSimpleNumField
  @test elem_type(AbsNonSimpleNumField) == AbsNonSimpleNumFieldElem
  @test parent_type(AbsNonSimpleNumFieldElem) == AbsNonSimpleNumField
  @test !is_simple(K)
  @test !is_simple(AbsNonSimpleNumField)

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

      for T in [Int, BigInt, QQFieldElem, ZZRingElem]
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
      @test @inferred z^u == @inferred z^ZZRingElem(u)

      M = zero_matrix(FlintQQ, 1, 6)
      Hecke.elem_to_mat_row!(M, 1, z)
      @test z == sum(M[1, j] * basis(K)[j] for j in 1:6)
      M = matrix(FlintQQ, 1, 6, [rand(-10:10) for j in 1:6])
      zz = Hecke.elem_from_mat_row(K, M, 1)
      @test zz == sum(M[1, j] * basis(K)[j] for j in 1:6)

      f = @inferred minpoly(z)
      @test length(factor(f)) == 1 && first(factor(f))[2] == 1
      @test is_monic(f)
      @test iszero(f(z))

      f = @inferred Hecke.minpoly_sparse(z)
      @test length(factor(f)) == 1 && first(factor(f))[2] == 1
      @test is_monic(f)
      @test iszero(f(z))

      f = @inferred Hecke.minpoly_dense(z)
      @test length(factor(f)) == 1 && first(factor(f))[2] == 1
      @test is_monic(f)
      @test iszero(f(z))

      f = @inferred charpoly(z)
      @test length(factor(f)) == 1
      @test is_monic(f)
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
    @test is_isomorphic(L, LL)
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
    OO = EquationOrder(K2)
    Omax = @inferred MaximalOrder(OO)
    @test discriminant(Omax) == FlintZZ(30233088)

    lp = prime_decomposition(Omax, 101)
    @test length(lp) == 3
  end

  @testset "rand" begin
    m = make(K, 1:3)
    for x in (rand(K, 1:3), rand(rng, K, 1:3), rand(m), rand(rng, m))
      @test x isa AbsNonSimpleNumFieldElem
    end
    @test rand(m, 3) isa Vector{AbsNonSimpleNumFieldElem}
    @test reproducible(m)
    @test reproducible(K, 1:3)
  end

  @testset "To Non Simple" begin
    f = x^6 - 3*x^5 - 2*x^4 + 9*x^3 - 5*x + 1
    K, a = number_field(f)
    lp = Hecke.non_simple_extension(K)
    Kns, gKns = number_field(lp)
    L, mL = simple_extension(Kns)
    @test is_isomorphic(L, K)
  end

  @testset "coercion" begin
    Qx, x = FlintQQ["x"]
    K, (a, b) = number_field([x^2 - 2, x^3 - 3])
    @test (@inferred QQ(2*a^0)) == 2*one(QQ)
    @test @inferred is_rational(2*a^0)
    @test_throws ArgumentError QQ(a)
    @test @inferred !is_rational(a)
  end

  K, (a,) = @inferred number_field([x])
  @test tr(a) == 0
  @test tr(one(K)) == 1
  K, (a, b) = @inferred number_field([x - 1, x])
  @test tr(a) == 1

  R, x = polynomial_ring(QQ)
  K, _ =   number_field([x])
  KK, f = absolute_simple_field(K)
  @test domain(f) === KK
  @test codomain(f) === K
  @test degree(KK) == 1

  let
    Qx, x = QQ["x"]
    K, (sqrt2, sqrt5) = number_field([x^2 - 2, x^2 - 5], ["sqrt2", "sqrt5"])
    Kt, t = polynomial_ring(K, :t)
    f = (20*sqrt2*sqrt5 - 70) * (t + 2) * (t - 2) * t^2 * (t - 1) * (t + 1)
    fa = factor(f)
    @test length(fa) == 5
    @test f == unit(fa) * prod(p^e for (p, e) in fa)
  end
end
