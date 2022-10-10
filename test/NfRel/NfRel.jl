@testset "NfRel" begin
  @testset "is_subfield" begin
    Qx, x = FlintQQ["x"]
    f = x^2 + 12x - 92
    K, a = NumberField(f, "a")
    Ky, y = K["y"]

    L, b = NumberField(y^2 + y + 1, "b")
    M, c = NumberField(y^6 + y^3 + 1, "c")

    d, LtoM = Hecke.is_subfield(L, M)

    @test d == true
    @test parent(LtoM(b)) == M
  end



  @testset "is_isomorphic" begin
    Qx, x = FlintQQ["x"]
    f = x^2 + 12x - 92
    K, a = NumberField(f, "a")
    Ky, y = K["y"]

    g = y^5 - 5
    L, b = NumberField(g, "b")
    bb = 5*b - 2
    h = minpoly(bb)
    L2, b2 = NumberField(h, "b2")

    c, LtoL2 = is_isomorphic_with_map(L, L2)
    @test c == true
    @test parent(LtoL2(b)) == L2

    #i = g - 1
    #L3, b3 = NumberField(i, "b3")
    #d, LtoL3 = is_isomorphic_with_map(L, L3)
    #@test d == false
  end

  @testset "signature" begin
    Qx, x = FlintQQ["x"]
    f = x^2 + 12x - 92
    K, a = NumberField(f, "a")
    Ky, y = K["y"]

    g = y^5 - 5
    L, b = NumberField(g, "b")
    @test signature(L) == (2, 4)

    Qx, x = FlintQQ["x"]
    f = x^2 + 12x - 92
    K, a = NumberField(f, "a")
    Ky, y = K["y"]

    L, b = NumberField(y^2 + y + 1, "b")
    @test signature(L) == (0, 2)
  end

  @testset "rand" begin
    Qx, x = FlintQQ["x"]
    f = x^2 + 12x - 92
    K, a = NumberField(f, "a")
    Ky, y = K["y"]

    L, b = NumberField(y^2 + y + 1, "b")

    m = make(L, 1:3)
    for x in (rand(L, 1:3), rand(rng, L, 1:3), rand(m), rand(rng, m))
      @test x isa Hecke.NfRelElem{nf_elem}
    end
    @test rand(m, 3) isa Vector{Hecke.NfRelElem{nf_elem}}
    @test reproducible(m)
    @test reproducible(L, 1:3)
  end

  @testset "norm" begin
    K, a = Hecke.rationals_as_number_field()
    Kt, t = K["t"]
    L, b = NumberField(t - 1, "b")
    Lt, t = L["t"]
    M, o = NumberField(t^3 + 2, "o")
    @test -1 == @inferred norm(o + 1)

    K, a = Hecke.rationals_as_number_field()
    Kt, t = K["t"]
    L, b = NumberField(t^3 + 2, "b")
    @test -1 == @inferred norm(b + 1, true)
  end

  @testset "relative cyclotomic field" begin
    E,b = @inferred cyclotomic_field_as_cm_extension(15, cached=false)
    phi = absolute_minpoly(b)
    R = parent(phi)
    x = gen(R)
    @test phi == x^8-x^7+x^5-x^4+x^3-x+1
    @test b^15 == one(E)
    Eabs, _ = Hecke.absolute_simple_field(E)
    @test Hecke.is_cm_field(Eabs)[1]
    @test Hecke.is_cyclotomic_type(E)[1]
    K = base_field(E)
    a = gen(K)
    @test a == b+inv(b)

    for p in Hecke.primes_up_to(50)[2:end]
      _,b = @inferred cyclotomic_field_as_cm_extension(p, cached=false)
      chip = absolute_minpoly(b)
      R = parent(chip) 
      x = gen(R)
      @test chip == sum([x^i for i=0:p-1])
    end
  end
end
