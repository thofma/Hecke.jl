@testset "Residue ring multiplicative group" begin
  Qx, x = FlintQQ["x"]
  A = AlgAss(x^2 - 5)
  O = Order(A, basis(A))
  Q, = quo(O, 2 * O)
  U, = unit_group(Q)
  @test order(U) == 2
  # this is (Z[sqrt(5)]/2*Z[sqrt(5)])^*
end
