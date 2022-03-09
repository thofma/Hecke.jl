@testset "Spaces" begin
  Qx, x = PolynomialRing(FlintQQ, "x")
  K, a = NumberField(x^2 - 2, "a1")
  OK = maximal_order(K)
  p = 3*OK
  Kt, t = K["t"]

  infp = infinite_places(K)

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
  @test_throws ArgumentError hermitian_space(E, FlintQQ[1 0; 1 1])

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
  @test !Hecke.islocally_hyperbolic(U,p)
  @test !Hecke.isisotropic(U,p)
  @test Hecke.islocally_hyperbolic(V,p)
  @test Hecke.isisotropic(V,p)
  @test all(v -> Hecke.isisotropic(V, v), infp)
  @test !Hecke.islocally_hyperbolic(W,p)
  @test Hecke.isisotropic(W,p)
  @test_throws AssertionError Hecke.islocally_hyperbolic(V, 2*OK)


  Qx, x = PolynomialRing(FlintQQ, "x")
  f = x^2-3
  K, a = NumberField(f, "a", cached = false)
  Kt, t = PolynomialRing(K, "t")
  g = t^2+(1)
  E, b = NumberField(g, "b", cached = false)
  D = matrix(E, 3, 3, [(a), 0, 0, 0, (2 * a), 0, 0, 0, (a + 5)])
  V = hermitian_space(E, D)
  DD = matrix(E, 2, 2, [a + 3, 0, 0, (a + 2)])
  W = hermitian_space(E, DD)
  @test @inferred Hecke.isrepresented_by(W, V)
  @test @inferred Hecke.isrepresented_by(V, V)
  DD = E(a) * identity_matrix(E, 5)
  W = hermitian_space(E, DD)
  @test @inferred Hecke.isrepresented_by(V, W)

  # they are not isometric at some dyadic prime ideal:
  DD = identity_matrix(E, 4)
  W = hermitian_space(E, DD)
  @test !(@inferred Hecke.isrepresented_by(W, V))


  K, a = rationals_as_number_field()
  OK = maximal_order(K)
  Kt, t = K["t"]

  E, b = NumberField(t^2+17)

  p = 2*OK
  q = 17*OK

  V = hermitian_space(E, E[102 b; -b 0])
  H = hermitian_space(E, E[0 1; 1 0])
  W = hermitian_space(E, E[1 1 2; 1 2 3; 2 3 1])
  
  @test_throws ErrorException hasse_invariant(V, p)
  @test_throws ErrorException witt_invariant(W, q)

  for r in [p,q]
    @test Hecke.islocally_represented_by(V,H,r)
  end
  @test Hecke.isrepresented_by(V,H)
  @test !Hecke.islocally_represented_by(W,V,p)
  @test Hecke.islocally_represented_by(V, W, p)
  @test !Hecke.isrepresented_by(W,V)
  
  @test !isisometric(V, W, ZZ(2))
  @test all(p -> isisometric(V, H, ZZ(p)), PrimesSet(1, 20))


  Qx, x = QQ["x"]
  K, a = number_field(x^3+3, "a")
  Kt, t = K["t"]
  E, b = number_field(t^2-2, "b")

  U = hermitian_space(E, E[1 1;1 1])
  V1 = hermitian_space(E, E[102 b; -b 0])
  V2 = hermitian_space(E, E[1 0;0 1])
  H = hermitian_space(E, E[0 1; 1 0])
  W = hermitian_space(E, E[1 1 2; 1 2 3; 2 3 1])

  infp = infinite_places(K)

  @test_throws ArgumentError isisometric(U, V)  # U is not regular
  @test isisometric(V1, V1, infp[1]) 
  @test !isisometric(V1, W, infp[2]) # infp[2] is complex but V and W don't have same rank
  @test count(v -> isisometric(V1, H, v), infp) == 1 # V1 and H are not everywhere locally isometric
  @test !isisometric(V1, H)
  @test isisometric(V1, V2)

end
