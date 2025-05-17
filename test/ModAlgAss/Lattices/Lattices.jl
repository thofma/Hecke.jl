begin
  Qx, x = QQ["x"];
  K, a = number_field(x^4 - x^3 + x^2 - x + 1, "a");
  V, f = galois_module(K); OK = ring_of_integers(K); M = f(OK);
  fl, c = is_free_with_basis(M); # the elements of c are a basis; @show fl
  for i in 1:5
    @test fl
    @test lattice(V, integral_group_ring(algebra(V)), c) == M
  end

  # from the oscar book
  K, a = number_field(x^4 + 4*x^2 + 2, "a");
  V, f = galois_module(K); OK = ring_of_integers(K); M = f(OK);
  @test !is_free(M)
end

let
  Qx, x = QQ["x"]
  K, a = number_field(x^8 + 105*x^6 + 3465*x^4 + 44100*x^2 + 176400, "a")
  V, f = galois_module(K)
  OK = ring_of_integers(K)
  M = f(OK)
  @test !is_free(M)
end

let
  Qx, x = QQ["x"]
  K, a = number_field(x^4 - x^3 + x^2 - x + 1, "a")
  V, f = galois_module(K)
  OK = ring_of_integers(K)
  M = f(OK)
  N = f(OK)
  @test M == N
  @test hash(M) == hash(N)
end

