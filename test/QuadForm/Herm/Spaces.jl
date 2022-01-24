@testset "Spaces" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - 2, "a1")
  OK = maximal_order(K)
  p = 3*OK
  Kt, t = K["t"]

  E, b = NumberField(t^2 + 3)
  s = involution(E)

  F = GF(3)

  Hecke.change_base_ring(::Hecke.NfRel, ::Hecke.gfp_mat) = error("asd")
  @test_throws ErrorException hermitian_space(E, F[1 2; 2 1])

  Hecke.change_base_ring(::Hecke.NfRel, x::Hecke.gfp_mat) = x
  @test_throws ErrorException hermitian_space(E, F[1 2; 2 1])

  V = @inferred hermitian_space(E, 3)
  @test fixed_field(V) == base_field(E)
  @test sprint(show, V) isa String
  @test !isquadratic(V)
  @test ispositive_definite(V)
  @test gram_matrix(V) == identity_matrix(E,3)
  @test V !== hermitian_space(E, 3, cached = false)

  @test_throws ArgumentError hermitian_space(E, E[1 b; b 1])
  @test_throws ArgumentError hermitian_space(E, FlintQQ[1 0, 1 1])

  V = @inferred hermitian_space(E, FlintQQ[1 2; 2 1])
  @test V === hermitian_space(E, FlintQQ[1 2; 2 1])
  @test V !== hermitian_space(E, FlintQQ[1 2; 2 1], cached = false)
  @test ishermitian(V)
  @test !isdefinite(V)
  @test involution(V) == s
  @test det(V) == -discriminant(V)

  U = hermitian_space(E, E[a 1; 1 1])
  V = hermitian_space(E, E[0 1; 1 0])
  W = hermitian_space(E, E[0 1 0; 1 0 0; 0 0 1])
  @test !islocally_hyperbolic(U,p)
  @test !isisotropic(U,p)
  @test islocally_hyperbolic(V,p)
  @test isisotropic(V,p)
  @test !islocally_hyperbolic(W,p)
  @test isisotropic(W,p)
  @test_throws AssertionError islocally_hyperbolic(V, 2*OK)

  K, a = rationals_as_number_field()
  OK = maximal_order(K)
  Kt, t = K["t"]

  E, b = NumberField(t^2+17)

  p = 2*OK
  q = 17*ok

  V = hermitian_space(E, E[102 b; -b 0])
  H = hermitian_space(E, E[0 1; 1 0])
  W = hermitian_space(E, E[1 1 2; 1 2 3; 2 3 1])
  for r in [2,17]
    @test isisometric(V,H,r)
  end
  for r in [p,q]
    @test islocally_represented_by(V,H,r)
  end
  @test isrepresented_by(V,H)
  @test !islocally_representeded_by(W,V,p)
  @test !represented_by(W,V)

end
