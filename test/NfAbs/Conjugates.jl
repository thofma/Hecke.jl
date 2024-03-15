@testset "NfAbs/Conjugates" begin
Qx, x = FlintQQ["x"]
K1, a1 = number_field(x^6 - x^5 + x^4 - x^3 + x^2 - x + 1, "a") # totally complex
K2, a2 = number_field(x^6 - x^5 - 7*x^4 + 2*x^3 + 7*x^2 - 2*x - 1, "a") # totally real
K3, a3 = number_field(x^6 - x^5 - x^4 + 4*x^3 + 3*x^2 - 1, "a") # signature (2, 2)

@testset "Totally real/complex" begin
  @test @inferred is_totally_complex(K1)
  @test @inferred !is_totally_complex(K2)
  @test @inferred !is_totally_complex(K3)

  @test @inferred !is_totally_real(K1)
  @test @inferred is_totally_real(K2)
  @test @inferred !is_totally_real(K3)
end

@testset "conjugates_arb" begin
  CC = AcbField(64)

  co = @inferred conjugates(10001 * a1 + 1, 256)

  @test overlaps(co[1], CC("[9011.589647892093681 +/- 9.30e-16]", "[4339.271274914698763 +/- 9.19e-16]"))
  @test Hecke.radiuslttwopower(co[1], -256)
  @test overlaps(co[2], CC("[-6234.521508389194039 +/- 8.09e-16]", "[7819.096656162766117 +/- 5.63e-16]"))
  @test Hecke.radiuslttwopower(co[2], -256)
  @test overlaps(co[3], CC("[2226.431860497100357 +/- 4.55e-16]", "[9750.25404973041789 +/- 4.36e-15]"))
  @test Hecke.radiuslttwopower(co[3], -256)
  @test overlaps(co[4], CC("[9011.589647892093681 +/- 9.30e-16]", "[-4339.271274914698763 +/- 9.19e-16]"))
  @test Hecke.radiuslttwopower(co[4], -256)
  @test overlaps(co[5], CC("[-6234.521508389194039 +/- 8.09e-16]", "[-7819.096656162766117 +/- 5.63e-16]"))
  @test Hecke.radiuslttwopower(co[5], -256)
  @test overlaps(co[6], CC("[2226.431860497100357 +/- 4.55e-16]", "[-9750.25404973041789 +/- 4.36e-15]"))
  @test Hecke.radiuslttwopower(co[6], -256)

  RR = ArbField(64)

  co = @inferred conjugates_real(a3, 32)
  @test length(co) == 2

  @test Hecke.radiuslttwopower(co[1], -32)
  @test Hecke.overlaps(co[1], RR("[-1.221417721 +/- 5.71e-10]"))
  @test Hecke.radiuslttwopower(co[2], -32)
  @test Hecke.overlaps(co[2], RR("[0.4665 +/- 4.52e-5]"))

  co = @inferred conjugates_complex(a3, 32)
  @test length(co) == 2
  @test Hecke.radiuslttwopower(co[1], -32)
  @test Hecke.overlaps(co[1], CC("[-0.542287022 +/- 3.58e-10]", "[0.460349889 +/- 4.60e-10]" ))
  @test Hecke.radiuslttwopower(co[2], -32)
  @test Hecke.overlaps(co[2], CC("[1.419725855 +/- 5.85e-10]", "[1.205211655 +/- 7.03e-10]"))

  colog = @inferred conjugates_log(a1, 16)
  @test length(colog) == 3
  @test contains(colog[1], 0)
  @test contains(colog[2], 0)
  @test contains(colog[3], 0)

  mink = @inferred minkowski_map(a3, 32)
  @test length(mink) == 6
  co = conjugates(a3, 32)
  sqrt2 = sqrt(RR(2))
  @test overlaps(mink[1], real(co[1]))
  @test overlaps(mink[2], real(co[2]))
  @test overlaps(mink[3], sqrt2 * real(co[3]))
  @test overlaps(mink[4], sqrt2 * imag(co[3]))
  @test overlaps(mink[5], sqrt2 * real(co[4]))
  @test overlaps(mink[6], sqrt2 * imag(co[4]))
end

@testset "T2" begin
  t = @inferred t2(a1, 64)
  @test contains(t, 6)
  @test Hecke.radiuslttwopower(t, -64)

  t = @inferred t2(a3^2, 128)
  @test overlaps(t, parent(t)("[26.8413130281669208224194865303660830716653210471312375675880809411649241305119684287180747356640152133866595977425833731119286780918091464992340699076157 +/- 6.82e-152]"))

  k, z = cyclotomic_field(2)
  @test isone(t2(z))

  k, z = cyclotomic_field(1)
  @test isone(t2(z))
end

@testset "signs" begin
  s = @inferred Hecke._signs(a3)
  @test s == Int[-1, 1]

  s = @inferred Hecke._signs(a3^2)
  @test s == Int[1, 1]

  s = @inferred Hecke._signs(a1)
  @test s == Int[]

  s = @inferred Hecke._signs(a2)
  @test s == Int[-1, -1, -1, 1, 1, 1]

  @test_throws ErrorException Hecke._signs(0*a1)
end

@testset "complex_conjugation" begin
  K, a = cyclotomic_field(5)
  aut = @inferred complex_conjugation(K)
  @test aut(a) == a^-1

  K, a = cyclotomic_field(29)
  aut = @inferred complex_conjugation(K)
  @test aut(a) == a^-1

  K, a = cyclotomic_field(13)
  aut = @inferred complex_conjugation(K)
  @test aut(a) == a^-1
  K, a = quadratic_field(5)
  aut = @inferred complex_conjugation(K)
  @test aut(a) == a
end

@testset "Bad example" begin
  Zx, x = polynomial_ring(FlintZZ)
  f = swinnerton_dyer(3, x)
  g = swinnerton_dyer(8, x)
  k, a = number_field(f, cached = false)
  s = @inferred t2(k(coeff(g, 0)), 512)
  @test contains(s, degree(k) * coeff(g, 0)^2)
  @test Hecke.radiuslttwopower(s, -512)
end

@testset "Kluners example" begin
  k, a = quadratic_field(-3364)
  z = minkowski_map(a, 64)
  @test Hecke.radiuslttwopower(z[1], -64)
  @test Hecke.radiuslttwopower(z[2], -64)
  @test contains(z[1], 0)
end

@testset "Another bad example" begin
  Qx, x = polynomial_ring(FlintQQ)
  f = x^12-3502319*x^10-3032677266943*x^8+17220065055936439179*x^6+26436504739687580368857995*x^4+12508949875084010197801010438203*x^2+1495531630727918278288148065057756816
  K, a = number_field(f, "a")
  @test 19619386 >= t2(a) >= 19619385
end

end
