@testset "PIP" begin
  G = small_group(8, 3) # D_4
  QG = QQ[G]
  ZG = Order(QG, basis(QG))
  I = 1 * ZG
  Hecke._assert_has_refined_wedderburn_decomposition(QG)
  fl, a = Hecke.is_principal_with_data(I, ZG, side = :right)
  @test fl
  @test a * ZG == I
  fl, a = Hecke._is_principal_with_data_bj(I, ZG, side = :right)
  @test fl
  @test a * ZG == I

  G = small_group(8, 4) # Q_8
  QG = QQ[G]
  ZG = Order(QG, basis(QG))
  I = 1 * ZG
  Hecke._assert_has_refined_wedderburn_decomposition(QG)
  fl, a = Hecke._is_principal_with_data_bj(I, ZG, side = :right)
  @test fl
  @test a * ZG == I

  G = small_group(16, 9) # Q_16
  QG = QQ[G]
  ZG = Order(QG, basis(QG))
  I = 1 * ZG
  Hecke._assert_has_refined_wedderburn_decomposition(QG)
  fl, a = Hecke._is_principal_with_data_bj(I, ZG, side = :right)
  @test fl
  @test a * ZG == I

  N = Hecke.swan_module(ZG, 3)
  fl, a = Hecke._is_principal_with_data_bj(N, ZG, side = :right)
  @test !fl

  # Issue #834
  Qx, x = QQ["x"]
  K, _a = number_field(x^2 + 15)
  OK = maximal_order(K)
  N = matrix(OK, 3, 3, OK.([1//2*_a + 1//2, 0, 1,
                            1//2*_a + 3//2, 1//2*_a + 3//2, 1//2*_a + 1//2,
                            0, 1, 1//2*_a + 1//2]))

  I = 2 * OK
  R, = quo(OK, I)
  mats = Hecke._write_as_product_of_elementary_matrices(N, R)
  @test map_entries(R, reduce(*, mats)) == map_entries(R, N)

  # zero algebra
  A = zero_algebra(QQ)
  M = maximal_order(A)
  F = 1 * M
  reps = Hecke.__unit_reps_simple(M, F)
  @test length(reps) <= 1
  reps = Hecke._unit_group_generators_maximal_simple(M)
  @test length(reps) <= 1

  include("PIP/unit_group_generators.jl")
end
