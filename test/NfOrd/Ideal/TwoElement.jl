@testset "Two-element ideals" begin
  # Minimum for non-simple
  Qx, x = QQ["x"]
  f = x - 1
  K, a = number_field([f], "a")
  O = maximal_order(K)
  I = Hecke.ideal(O, 2, O(2))
  @test (@inferred minimum(I)) == 2

  f = x^2 - 2
  K, a = number_field([f], "a")
  O = maximal_order(K)
  I = ideal(O, 2 * identity_matrix(ZZ, 2))
  Hecke.assure_2_normal(I)
  @test isdefined(I, :gen_two)
end
