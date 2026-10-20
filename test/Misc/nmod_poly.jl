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
