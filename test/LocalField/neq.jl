@testset "Unramified extension" begin
    Qx,x = FlintQQ["x"]
    f = Qx([1, 8, -40, -46, 110, 71, -113, -43, 54, 11, -12, -1, 1])
    L = number_field(f)[1]
    P = prime_decomposition(maximal_order(L),7)[1][1]
    lp, mp = Hecke.completion(L,P, 128) # the default of 6 is too small
    Qy,y = polynomial_ring(lp,"y")
    f, mf = residue_field(lp)
    N = Hecke.unramified_extension(y^3+preimage(mf,(gen(f)))+4)[1]
    F, mF = residue_field(N)
    @test order(F) == 7^6
    G, mG = automorphism_group(N)
    @test order(G) == 3
    @test mG(G[1]^2) == mG(G[1])^2
    b = rand(f)
    @test norm(Hecke.norm_equation(F, b)) == b
    for i = 1:3
        c = 1+uniformizer(lp)^i
        chk = norm(Hecke.norm_equation_unramified(N, c))*c^-1 -1
        @test iszero(chk) || Int(ee*valuation(chk)) >= precision(c)
    end
    n = Int(ceil(absolute_ramification_index(lp)//(Int(prime(lp))-1)))+1
    l = base_field(lp)
    ee = absolute_ramification_index(l)
    for i = n:n+2
        c = 1+uniformizer(l)^i
        chk = norm(Hecke.norm_equation(lp, c))*c^-1 -1
        @test iszero(chk) || Int(ee*valuation(chk)) >= precision(c)
    end

end

@testset "AutomorphismGroup" begin
  Qx, x = QQ["x"]
  k, a = number_field(x^6+108)
  l2 = prime_decomposition(maximal_order(k), 2)
  k2, _ = Hecke.completion(k, l2[1][1], 120)

  G, mG = automorphism_group(k2, Hecke.absolute_base_field(k2))
  @test all([mG(x*y) == mG(x) * mG(y) for x = G for y = G])

end

@testset "LocalFundamentalClass Serre" begin
  Qx, x = QQ["x"]
  k, a = number_field(x^6+108)
  l2 = prime_decomposition(maximal_order(k), 2)
  k2, _ = Hecke.completion(k, l2[1][1], 120)

  G, mG = automorphism_group(k2, Hecke.absolute_base_field((k2)))

  z = Hecke.local_fundamental_class_serre(k2, Hecke.absolute_base_field((k2)))
  for g = G 
    for h = G 
      for k = G 
        a = z(mG(g), mG(h*k))*z(mG(h), mG(k)) - mG(k)(z(mG(g), mG(h)))*z(mG(g*h), mG(k))
         @test iszero(a) || valuation(a) > 20
       end
     end
   end
end

@testset "UnitGroup" begin
  Qx, x = QQ["x"]
  k, a = number_field(x^6+108)
  l2 = prime_decomposition(maximal_order(k), 2)
  k2, _ = Hecke.completion(k, l2[1][1], 120)

  U, mU = unit_group(k2)

  for i=1:10
    #numerical problems with gen[1] : there is valuation...
    u = sum(rand(-10:10)*x for x = gens(U)[2:end]) 
    @test u == preimage(mU, mU(u))  
  end

  l5 = prime_decomposition(maximal_order(k), 5)
  k2, _ = Hecke.completion(k, l5[1][1], 12)

  U, mU = unit_group(k2)

  for i=1:10
    #numerical problems with gen[1] : there is valuation...
    u = sum(rand(-10:10)*x for x = gens(U)[2:end]) 
    @test u == preimage(mU, mU(u))  
  end

end


@testset "Misc FinField" begin
  k = GF(3)
  kt, t = k["t"]
  K = GF(3, 2)
  @test length(roots(K, t^2+t+2)) == 2
  @test length(basis(K, k)) == 2

  #= RelFinField seems to be a tad broken...
  E = Hecke.RelFinField(t^2+t+2, :a)
  @test length(roots(E, t^2+2*t+2)) == 2

  any_root(E, t^2+2*t+2)
  =#

  Hecke.frobenius_equation(1, gen(K)^2)
  Hecke.frobenius_equation(Hecke.ArtinSchreierSolveCtx(K, 1), gen(K)^2)
  c = gen(K)
  c = frobenius(c)-c
  Hecke.artin_schreier_equation(1, c)
  Hecke.artin_schreier_equation(Hecke.ArtinSchreierSolveCtx(K, 1), c)
end

@testset "Misc LocalField" begin
  K = qadic_field(3, 5, precision = 10)[1]
  k = padic_field(3, precision = 10)
  @test is_norm(K, k(3)) == false
  @test is_norm(K, k(3)^5) == true

  @test length(coordinates(gen(K)^10, k)) == 5
end

@testset "LocalNorm" begin
  k, a = wildanger_field(3, 13)
  @test is_local_norm(k, norm(a+1)) == true

  K, b = radical_extension(2, a+1)
  @test is_local_norm(K, norm(b+a)) == true
end

