@testset "Spaces" begin
  Qx, x = polynomial_ring(QQ, "x")
  K, a = number_field(x^2 - 2, "a1")
  OK = maximal_order(K)
  p = 3*OK
  Kt, t = K["t"]

  infp = infinite_places(K)

  E, b = number_field(t^2 + 3)
  s = involution(E)

  F = GF(3)

  V = @inferred hermitian_space(E, E[1 1; 1 1;])
  @test 0 in diagonal(V)

  V = @inferred hermitian_space(E, 3)
  @test fixed_field(V) == base_field(E)
  @test sprint(show, V) isa String
  @test !is_quadratic(V)
  @test is_positive_definite(V)
  @test gram_matrix(V) == identity_matrix(E,3)
  @test V !== hermitian_space(E, 3, cached = false)
  v = matrix(E,1,3,[1,1,1])
  @test inner_product(V, v, v) == matrix(E,1,1,[3])

  @test_throws ArgumentError hermitian_space(E, E[1 b; b 1])
  @test_throws ArgumentError hermitian_space(E, QQ[1 0; 1 1])

  V = @inferred hermitian_space(E, QQ[1 2; 2 1])
  @test V === hermitian_space(E, QQ[1 2; 2 1])
  @test V !== hermitian_space(E, QQ[1 2; 2 1], cached = false)
  @test is_hermitian(V)
  @test !is_definite(V)
  @test involution(V) == s
  @test det(V) == -discriminant(V)

  U = hermitian_space(E, E[a 1; 1 1])
  V = hermitian_space(E, E[0 1; 1 0])
  W = hermitian_space(E, E[0 1 0; 1 0 0; 0 0 1])
  @test !Hecke.is_locally_hyperbolic(U,p)
  @test !Hecke.is_isotropic(U,p)
  @test Hecke.is_locally_hyperbolic(V,p)
  @test Hecke.is_isotropic(V,p)
  @test all(v -> Hecke.is_isotropic(V, v), infp)
  @test !Hecke.is_locally_hyperbolic(W,p)
  @test Hecke.is_isotropic(W,p)
  @test_throws AssertionError Hecke.is_locally_hyperbolic(V, 2*OK)

  @inferred rescale(V, -1)
  Vm = rescale(V, -1)
  @test gram_matrix(Vm) == -gram_matrix(V)


  Qx, x = polynomial_ring(QQ, "x")
  f = x^2-3
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2+(1)
  E, b = number_field(g, "b", cached = false)
  D = matrix(E, 3, 3, [(a), 0, 0, 0, (2 * a), 0, 0, 0, (a + 5)])
  V = hermitian_space(E, D)
  DD = matrix(E, 2, 2, [a + 3, 0, 0, (a + 2)])
  W = hermitian_space(E, DD)
  @test @inferred Hecke.is_represented_by(W, V)
  @test @inferred Hecke.is_represented_by(V, V)
  DD = E(a) * identity_matrix(E, 5)
  W = hermitian_space(E, DD)
  @test @inferred Hecke.is_represented_by(V, W)

  # they are not isometric at some dyadic prime ideal:
  DD = identity_matrix(E, 4)
  W = hermitian_space(E, DD)
  @test !(@inferred Hecke.is_represented_by(W, V))


  K, a = rationals_as_number_field()
  OK = maximal_order(K)
  Kt, t = K["t"]

  E, b = number_field(t^2+17)

  p = 2*OK
  q = 17*OK

  V = hermitian_space(E, E[102 b; -b 0])
  H = hermitian_space(E, E[0 1; 1 0])
  W = hermitian_space(E, E[1 1 2; 1 2 3; 2 3 1])

  @test_throws ErrorException hasse_invariant(V, p)
  @test_throws ErrorException witt_invariant(W, q)

  for r in [p,q]
    @test Hecke.is_locally_represented_by(V,H,r)
  end
  @test Hecke.is_represented_by(V,H)
  @test !Hecke.is_locally_represented_by(W,V,p)
  @test Hecke.is_locally_represented_by(V, W, p)
  @test !Hecke.is_represented_by(W,V)

  @test !is_isometric(V, W, ZZ(2))
  @test all(p -> is_isometric(V, H, ZZ(p)), PrimesSet(1, 20))


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

  @test_throws ArgumentError is_isometric(U, V)  # U is not regular
  @test is_isometric(V1, V1, infp[1])
  @test !is_isometric(V1, W, infp[2]) # infp[2] is complex but V and W don't have same rank
  @test count(v -> is_isometric(V1, H, v), infp) == 1 # V1 and H are not everywhere locally isometric
  @test !is_isometric(V1, H)
  @test is_isometric(V1, V2)

end

@testset "diagonal with transform" begin
  E, b = cyclotomic_field_as_cm_extension(3)
  K = base_field(E)
  s = involution(E)
  Vh = hermitian_space(E, E[1 b 1; s(b) 4 s(b); 1 b 1])
  diag, U = @inferred diagonal_with_transform(Vh)
  @test diagonal(map_entries(K, U*gram_matrix(Vh)*map_entries(s, transpose(U)))) == diag
end
