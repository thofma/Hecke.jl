@testset "Spaces" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - 2, "a1")
  Kt, t = K["t"]

  E, b = NumberField(t^2 + 3)

  F = GF(3)

  Hecke.change_base_ring(::Hecke.NfRel, ::Hecke.gfp_mat) = error("asd")
  @test_throws ErrorException hermitian_space(E, F[1 2; 2 1])

  Hecke.change_base_ring(::Hecke.NfRel, x::Hecke.gfp_mat) = x
  @test_throws ErrorException hermitian_space(E, F[1 2; 2 1])

  V = @inferred hermitian_space(E, FlintQQ[1 2; 2 1])
  @test V === hermitian_space(E, FlintQQ[1 2; 2 1])
  @test V !== hermitian_space(E, FlintQQ[1 2; 2 1], cached = false)
  @test V isa Hecke.HermSpace
end
