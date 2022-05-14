@testset "PIP" begin
  G = small_group(8, 3) # D_4
  QG = QQ[G]
  ZG = Order(QG, basis(QG))
  I = 1 * ZG
  Hecke._assert_has_refined_wedderburn_decomposition(QG)
  fl, a = Hecke._isprincipal(I, ZG, :right)
  @test fl
  @test a * ZG == I
  fl, a = Hecke.__isprincipal(ZG, I, :right)
  @test fl
  @test a * ZG == I

  G = small_group(8, 5) # Q_8
  QG = QQ[G]
  ZG = Order(QG, basis(QG))
  I = 1 * ZG
  Hecke._assert_has_refined_wedderburn_decomposition(QG)
  fl, a = Hecke.__isprincipal(ZG, I, :right)
  @test fl
  @test a * ZG == I

  G = small_group(16, 9) # Q_16
  QG = QQ[G]
  ZG = Order(QG, basis(QG))
  I = 1 * ZG
  Hecke._assert_has_refined_wedderburn_decomposition(QG)
  fl, a = Hecke.__isprincipal(ZG, I, :right)
  @test fl
  @test a * ZG == I

  N = Hecke.swan_module(ZG, 3)
  fl, a = Hecke.__isprincipal(ZG, N, :right)
  @test !fl
end
