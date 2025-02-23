@testset "Semilinar" begin
  k, o = finite_field(9)
  kt, t = rational_function_field(k, "t")
  A = matrix(kt, 2, 1, [o*(1 + t), t^3 + t^6])
  @test nrows(Hecke._semilinear_kernel(A, 3)) == 0
  A = matrix(kt, 2, 1, [o*(1 + t), t^3 + t^4])
  K = Hecke._semilinear_kernel(A, 3)
  @test nrows(K) == 1
  @test K .^3 * A == 0
end
