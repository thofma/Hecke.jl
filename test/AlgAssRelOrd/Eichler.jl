@with_polymake @testset "Eichler" begin
  K, a = Hecke.rationals_as_number_field()
  A = Hecke.AlgQuat(K, K(1), K(1))
  A = Hecke.AlgAss(K, A.mult_table)
  OA = maximal_order(A)
  b = @inferred Hecke.principal_generator_eichler(2 * OA)
  @test b * OA == 2 * OA
end
