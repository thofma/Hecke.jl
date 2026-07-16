
@testset "G4 Invariants and reconstruction" begin


  K, (x,y,z,w) = polynomial_ring(QQ, [:x,:y,:z,:w])
  conic = 8*x^2 + x*y + 6*x*z + 6*x*w + y^2 + 10*y*z + 10*y*w + 5*z^2 + 9*z*w + 4*w^2
  cubic = 7*x^3 + 3*x^2*y + 8*x^2*z + 5*x^2*w + 4*x*y^2 + 7*x*y*z + 6*x*y*w + 2*x*z^2 + 
    9*x*z*w + 8*x*w^2 + 4*y^3 + 3*y^2*z + 2*y^2*w + 8*y*z^2 + 4*y*z*w + 9*y*w^2 + 4*z^2*w + 8*z*w^2 + w^3   
  invs, ws = g4_invariants(conic, cubic)
  conic2, cubic2 = reconstruct_from_g4_invs(invs)
  invs2, ws = g4_invariants(conic2, cubic2)
  @test weighted_equality(invs, invs2, ws)

  K, (x,y,z,w) = polynomial_ring(QQ, [:x,:y,:z,:w])
  conic = x^2 -x*y +7*z^2 - 3*w*z - w^2
  cubic = 100*x^3 -5*x^2*y +3*x*z^2 -y^3 -4*z^3 - w*x*z +w^2*z

  invs, ws = g4_invariants(conic, cubic)
  conic2, cubic2 = reconstruct_from_g4_invs(invs)
  invs2, ws = g4_invariants(conic2, cubic2)
  @test weighted_equality(invs, invs2, ws)


  K, (x,y,z,w) = polynomial_ring(GF(37), [:x,:y,:z,:w])
  conic = x^2 -5*x*y +7*z^2 - 3*w*z - 20*w^2
  cubic = 15*x^3 -3*x^2*y +7*x*z^2 -y^3 -4*z^3 + w*x*z +w^2*z

  invs, ws = g4_invariants(conic, cubic)
  conic2, cubic2 = reconstruct_from_g4_invs(invs)
  invs2, ws = g4_invariants(conic2, cubic2)
  @test weighted_equality(invs, invs2, ws)


end
