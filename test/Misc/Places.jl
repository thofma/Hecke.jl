@testset "Places" begin
   Qx, x = FlintQQ["x"]
   K1, a1 = NumberField(x^5 + 2, "a1")
   K2, a2 = NumberField(x^9 + 1*x^4 + 14*x^3 - 14*x^2 + 14*x - 14, "a2")
   K3, a3 = NumberField(x^6 - 2, "a3")

  @testset "Construction" begin

    S = infinite_places(K1)
    @test length(S) == 3

    SR = real_places(K1)
    @test length(SR) == 1
    @test all(isreal, SR)

    SC = complex_places(K1)
    @test length(SC) == 2
    @test all(is_complex, SC)

    r = conjugates_arb(a1)
    @test overlaps(r[1], SR[1].r)
    @test overlaps(r[2], SC[1].r) && overlaps(r[3], SC[2].r)

    P = infinite_place(K1, 1)
    @test P == S[1]
    @test overlaps(P.r, r[1])

    P = infinite_place(K1, 2)
    @test P == S[2]
    @test overlaps(P.r, r[2])

    @test S[1] == S[1]
    @test S[1] != S[2]

    string(S[1]); # Just check that it does not error

    S = infinite_places(K2)
    @test length(S) == 5

    SR = real_places(K2)
    @test length(SR) == 1
    @test all(isreal, SR)

    SC = complex_places(K2)
    @test length(SC) == 4
    @test all(is_complex, SC)

    r = conjugates_arb(a2)
    @test overlaps(r[1], SR[1].r)
    @test overlaps(r[2], SC[1].r) && overlaps(r[3], SC[2].r) && overlaps(r[4], SC[3].r) && overlaps(r[5], SC[4].r)

    P = infinite_place(K2, 1)
    @test P == S[1]
    @test overlaps(P.r, r[1])

    P = infinite_place(K2, 2)
    @test P == S[2]
    @test overlaps(P.r, r[2])

    @test S[1] == S[1]
    @test S[1] != S[2]

    string(S[1]); # Just check that it does not error
  end

  @testset "Signs and Positivity" begin
    b = a1
    P = real_places(K1)[1]
    C = complex_places(K1)[1]

    for b in [b, FacElem(b), maximal_order(K1)(b)]
      sb = signs(b)
      @test sb == Dict(P => -1)
      @test sign(b, P) == -1
      @test_throws ErrorException sign(b, C)
      @test signs(b, infinite_places(K1)) == Dict(P => -1)
      @test signs(b, [P]) == Dict(P => -1)
      @test signs(b, complex_places(K1)) == Dict{InfPlc, Int}()
      @test !is_positive(b, P)
      @test_throws ErrorException is_positive(b, C)
      @test !is_positive(b, [P])
      @test !is_positive(b, infinite_places(K1))
      @test is_positive(b, [C])
      @test !is_totally_positive(b)

      c = b^10*b^2
      sc = signs(c)
      @test sc == Dict(P => 1)
      @test sign(c, P) == 1
      @test_throws ErrorException sign(c, C)
      @test signs(c, infinite_places(K1)) == Dict(P => 1)
      @test signs(c, [P]) == Dict(P => 1)
      @test signs(c, complex_places(K1)) == Dict{InfPlc, Int}()
      @test is_positive(c, P)
      @test_throws ErrorException is_positive(c, C)
      @test is_positive(c, [P])
      @test is_positive(c, [C])
      @test is_positive(c, infinite_places(K1))
      @test is_totally_positive(c)
    end

    b = a3
    P = real_places(K3)[1]
    P2 = real_places(K3)[2]
    C = complex_places(K3)[1]

    for b in [b, FacElem(b), maximal_order(K3)(b)]
      @test signs(b) == Dict(P => -1, P2 => 1)
      @test sign(b, P) == -1
      @test_throws ErrorException sign(b, C)
      @test signs(b, infinite_places(K3)) == Dict(P => -1, P2 => 1)
      @test signs(b, [P]) == Dict(P => -1)
      @test signs(b, complex_places(K3)) == Dict{InfPlc, Int}()
      @test is_positive(b, P2)
      @test !is_positive(b, P)
      @test_throws ErrorException is_positive(b, C)
      @test is_positive(b, [P2])
      @test is_positive(b, [P2, C])
      @test !is_positive(b, [P])
      @test !is_positive(b, [P, C])
      @test !is_positive(b, infinite_places(K3))
      @test !is_totally_positive(b)

      c = b^10*b^2
      @test signs(c) == Dict(P => 1, P2 => 1)
      @test sign(c, P) == 1
      @test_throws ErrorException sign(c, C)
      @test signs(c, infinite_places(K3)) == Dict(P => 1, P2 => 1)
      @test signs(c, [P]) == Dict(P => 1)
      @test signs(c, complex_places(K3)) == Dict{InfPlc, Int}()
      @test is_positive(c, P)
      @test is_positive(c, P2)
      @test_throws ErrorException is_positive(c, C)
      @test is_positive(c, [P])
      @test is_positive(c, [P, C])
      @test is_positive(c, infinite_places(K3))
      @test is_totally_positive(c)
    end
  end
end
