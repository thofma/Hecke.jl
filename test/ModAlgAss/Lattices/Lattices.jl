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
