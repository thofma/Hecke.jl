@testset "G1 Models" begin

  R, (x,z) = polynomial_ring(QQ, 2)
  P = x^2 + 10*x*z - 5*z^2
  Q = x^4 - 3*x^2*z^2 + x*z^3 - 2*z^4

  @test c_invariants(Hecke.g1_model_d2(Q, P)) == (QQ(12864), QQ(-1623672))

  R, (x, y, z) = polynomial_ring(QQ, 3)
  C = x^3 + 14*x*y*z - 5*z^2*y + y^3 +3*z^3

  @test c_invariants(Hecke.g1_model_d3(C)) == (QQ(29344), QQ(-12030328))

  R, (x, y, z, w) = polynomial_ring(QQ, 4)

  P1 = x^2 + y^2 + 3*y*w + 10*x*z - 5*z^2 -w^2
  P2 = x*w + 2*y^2 + 2*z*w + 45*y*z - 2*z^2 + w^2

  @test c_invariants(Hecke.g1_model_d4(P1, P2)) == (QQ(70876192), QQ(-1845203945336))

end

