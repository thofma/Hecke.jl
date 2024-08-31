let
  K = algebraic_closure(QQ)
  Kx, x = polynomial_ring(K; cached = false)
  f = 2*(x^3 + sqrt(K(2)))^2
  fa = factor(f)
  @test f == unit(fa) * prod(g^e for (g, e) in fa)
  @test all(degree(g) == 1 for (g, e) in fa)

  rts = @inferred roots(f)
  @test length(rts) == 3
  @test all(r -> is_zero(f(r)), rts)
end
