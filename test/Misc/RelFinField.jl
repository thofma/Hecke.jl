@testset "RelFinField" begin

  @testset "Basic properties" begin
    F = Native.finite_field(3, 3, cached = false)[1]
    x = polynomial_ring(F, "x", cached = false)[2]
    K, gK = @inferred Native.finite_field(x^2+1, "a")
    dp = @inferred defining_polynomial(K)
    @test dp == x^2+1
    @test degree(K) == 2
    bK = @inferred base_field(K)
    @test bK == F
    o = @inferred order(K)
    @test o == 27^2
    @test absolute_degree(K) == 6
  end

  @testset "Promote rule" begin
    F, gF = Native.finite_field(3, 3, cached = false)
    x = polynomial_ring(F, "x", cached = false)[2]
    K, gK = Native.finite_field(x^2+1, "a")
    Kt, t = K["t"]
    L, gL = @inferred Native.finite_field(t^5+t^4+t^2+1, "b")
    dp = @inferred defining_polynomial(L)
    el = @inferred gL + gK
    @test parent(el) == L
    el1 = @inferred gL + gK
    @test parent(el1) == L
    @test iszero(dp(gL))
  end

  @testset "Basic operations" begin
    F, gF = Native.finite_field(3, 3, cached = false)
    x = polynomial_ring(F, "x", cached = false)[2]
    K, gK = Native.finite_field(x^2+1, "a")
    Kt, t = K["t"]
    L, gL = Native.finite_field(t^5+t^4+t^2+1, "b")
    @inferred gL + gL
    @inferred gL - gL
    @inferred gL*gL
    el = @inferred inv(gL)
    @test el == -(gL^4+gL^3+gL)
    @inferred div(gL, gL)
    @test iszero(gL + gL + gL)
    @test iszero(3*gL)
    @test gL^3 == gL*gL*gL
    @test gL^5 == 2*(gL^4+gL^2+1)
    @test isone(-gL^5-gL^4-gL^2)
  end

  @testset "Norm, Trace, Minpoly" begin
    F, gF = Native.finite_field(3, 3, cached = false)
    x = polynomial_ring(F, "x", cached = false)[2]
    K, gK = Native.finite_field(x^2+1, "a")
    Kt, t = K["t"]
    L, gL = Native.finite_field(t^5+t^4+t^2+1, "b")
    el = @inferred absolute_norm(gL)
    @test isone(el)
    el1 = @inferred absolute_tr(gL)
    @test iszero(el1)
    @test isone(-tr(gL))
    @test isone(-norm(gL))
    f = @inferred Hecke.absolute_minpoly(gL)
    Fx = parent(f)
    x = gen(Fx)
    @test f == x^5+x^4+x^2+1
    g = @inferred minpoly(gL+1)
    @test iszero(g(gL+1))
    Rx = parent(g)
    y = gen(Rx)
    @test g(y+1) == y^5+y^4+y^2+1

    f, o = Native.finite_field(7, 2, "o");
    fx, x = f["x"];
    F, u = Native.finite_field(x^3 + o + 4, "u");
    c = 3*u + 5*o + 1;
    @test norm(c) == 2*o
    @test Hecke.norm_via_powering(c) == 2*o
  end

  @testset "Absolute basis and coordinates" begin
    F, gF = Native.finite_field(3, 3, cached = false)
    x = polynomial_ring(F, "x", cached = false)[2]
    K, gK = Native.finite_field(x^2+1, "a")
    Kt, t = K["t"]
    L, gL = Native.finite_field(t^5+t^4+t^2+1, "b")
    B = absolute_basis(L)
    for i = 1:length(B)
      v = absolute_coordinates(B[i])
      for j = 1:length(v)
        if i == j
          @test isone(v[j])
        else
          @test iszero(v[j])
        end
      end
    end

    F = GF(3^3, cached = false)
    x = polynomial_ring(F, "x", cached = false)[2]
    K, gK = Hecke.Nemo._residue_field(x^2+1, "a")
    Kt, t = K["t"]
    L, gL = Hecke.Nemo._residue_field(t^5+t^4+t^2+1, "b")
    B = absolute_basis(L)
    for i = 1:length(B)
      v = absolute_coordinates(B[i])
      for j = 1:length(v)
        if i == j
          @test isone(v[j])
        else
          @test iszero(v[j])
        end
      end
    end

    for i in 1:100
      z = rand(L)
      @test dot(absolute_coordinates(z), absolute_basis(L)) == z
    end

  end

  @testset "Polynomials" begin
    F, gF = Native.finite_field(3, 3, cached = false)
    x = polynomial_ring(F, "x", cached = false)[2]
    K, gK = Native.finite_field(x^2+1, "a")
    Kt, t = K["t"]
    L, gL = Native.finite_field(t^5+t^4+t^2+1, "b")
    Ly, y = L["y"]
    @test is_irreducible(y^13+2*y+1)
  end

  @testset "Random" begin
    F, gF = Native.finite_field(3, 3, cached = false)
    x = polynomial_ring(F, "x", cached = false)[2]
    K, gK = Native.finite_field(x^2+1, "a")
    a = @inferred rand(K)
    @test parent(a) === K
  end
end
