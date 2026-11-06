@testset "gcd_sircana" begin
    R = residue_ring(ZZ,9)[1]
    S, x = R[:x]
    f = x^2
    g = x^2-5*x+6

    a, u, v = Hecke.gcd_sircana(f,g)
    d = u*f + v*g
    @test is_zero(rem(d, a))

    F, = residue_ring(ZZ, 12); x = F[:x][2]
    d, u, v = Hecke.gcd_sircana((x+7)*(x+1), (x+7)*(2*x+1))
    @test d == x + 7

    F, = residue_ring(ZZ, 210); x = F[:x][2]
    d, u, v = Hecke.gcd_sircana(x^2+1, x+1)
    @test d*u == x^2+1
    @test d*v == x+1

    F, = residue_ring(ZZ, 12); x = F[:x][2]
    d, u, v = Hecke.gcd_sircana(x^2+1, x+1)
    @test d*u == x^2+1
    @test d*v == x+1

    F, = residue_ring(ZZ, 9); x = F[:x][2]
    d, u, v = Hecke.gcd_sircana(x^2, x*(x^2-5*x+6))
    @test d == x

#=
    g *= x
    a, u, v = Hecke.gcd_sircana(f,g)
    d = u*f + v*g
    @test is_zero(rem(d, a))
=#
end

@testset "Composite modulus resultants" begin
  Zx, x = polynomial_ring(ZZ, :x)
  f = 2*x^2 + x + 1
  g = 3*x + 1
  for m in (6, 12, 36, 45), modulus in (m, ZZ(m))
    R, _ = residue_ring(ZZ, modulus)
    Rt, t = polynomial_ring(R, :t)
    fm = change_base_ring(R, f; parent = Rt)
    gm = change_base_ring(R, g; parent = Rt)
    @test Hecke.resultant_sircana(fm, gm) == R(resultant(f, g))
    @test Hecke.resultant_sircana(gm, fm) == R(resultant(g, f))
  end
end

@testset "euler_phi and carmichael_lambda" begin
  # compare with the unit group of F_q[x]/(f), computed by brute force
  for F in [Native.GF(2), Native.GF(3), Native.GF(ZZ(3)),
            Native.finite_field(2, 2, :a)[1],
            Native.finite_field(3, 2, :a)[1]]
    Fx, x = F[:x]
    for f in [x^3, x^4, (x + 1)^2 * (x^2 + x + 1), x^3 + x^2 + 1]
      n = degree(f)
      cs = Iterators.product(fill(collect(F), n)...)
      U = [g for g in (Fx(collect(c)) for c in cs) if isone(gcd(g, f))]
      ord(g) = findfirst(k -> isone(powermod(g, k, f)), 1:length(U))
      @test euler_phi(f) == length(U)
      @test carmichael_lambda(f) == reduce(lcm, ord.(U))
    end
  end
end

@testset "carmichael_lambda at characteristic powers" begin
  # Check exact characteristic powers and neighboring factor multiplicities.
  for p in (2, 3, 5)
    for F in (Native.GF(p), Native.GF(ZZ(p)),
              Native.finite_field(p, 2, :a)[1])
      Fx, x = F[:x]
      q = size(F)
      @test carmichael_lambda(one(Fx)) == 1
      for (k, u) in ((1, 1), (p - 1, p == 2 ? 1 : p), (p, p),
                     (p + 1, p^2), (p^2 - 1, p^2), (p^2, p^2),
                     (p^2 + 1, p^3))
        @test carmichael_lambda(x^k) == (q - 1)*u
      end
    end
  end
end
