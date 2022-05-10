@testset "Frobenius extensions" begin
  # S3 on 3 points
  # Data taken from Cohen & Diaz y Diaz & Olivier, Counting discriminants of number fields
  flds = Hecke.primitive_frobenius_extensions(QQ, (6, 1), fmpz(10)^2)
  @test length(flds) == 7
  flds = Hecke.primitive_frobenius_extensions(QQ, (6, 1), fmpz(10)^3, only_real = true)
  @test length(flds) == 22
  @test all(count(L -> is_isomorphic(L, K), flds) == 1 for K in flds)
  flds = Hecke.primitive_frobenius_extensions(QQ, (6, 1), fmpz(10)^3, only_non_real = true)
  @test length(flds) == 127
  flds = Hecke.primitive_frobenius_extensions(QQ, (6, 1), fmpz(10)^3)
  @test length(flds) == 149

  QQx, x = QQ["x"]

  # D5 on 5 points, according to Malle-Klüners
  flds = Hecke.primitive_frobenius_extensions(QQ, (10, 1), fmpz(2208), only_non_real = true)
  @test length(flds) == 0
  flds = Hecke.primitive_frobenius_extensions(QQ, (10, 1), fmpz(2209), only_non_real = true)
  @test length(flds) == 1
  @test is_isomorphic(flds[1], number_field(x^5 - 2*x^4 + 2*x^3 - x^2 + 1)[1])

  flds = Hecke.primitive_frobenius_extensions(QQ, (10, 1), fmpz(106800), only_real = true)
  @test length(flds) == 0
  flds = Hecke.primitive_frobenius_extensions(QQ, (10, 1), fmpz(160801), only_real = true)
  @test length(flds) == 1
  @test is_isomorphic(flds[1], number_field(x^5 - x^4 - 5*x^3 + 4*x^2 + 3*x - 1)[1])

  @test_throws ArgumentError Hecke.primitive_frobenius_extensions(QQ, (1, 1), fmpz(10))
  @test_throws ArgumentError Hecke.primitive_frobenius_extensions(QQ, (10, 1), fmpz(160801), only_real = true, only_non_real = true)
end
