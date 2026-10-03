# Reconstruction of random genus 4 curves (generic, one vanishing theta null,
# hyperelliptic) from their small period matrices, compared with the original
# curves (Bouchet's invariants resp. the branch points), the point check of a
# non-hyperelliptic reconstruction, and the model over QQ resp. Q(sqrt 2) from
# the big period matrix (checked exactly). The curves are random, so the seed
# is fixed.
@testset "Reconstruction genus 4" begin
  Hecke.Random.seed!(4711)
  ok(results) = all(r -> r.result.ok == true, results)
  n = riesrf_long_tests() ? 5 : 2
  for kind in (:generic, :theta_null, :hyperelliptic)
    @test ok(RSM.random_g4_reconstruction_tests(n; kind = kind, prec = 300))
  end

  # the quadric and the cubic vanish at points of the curve
  f = RSM._random_g4_curve(:generic)
  while RSM.genus(RSM.riemann_surface(f, 64)) != 4
    f = RSM._random_g4_curve(:generic)
  end
  check = RSM.check_g4_reconstruction(f, 300)
  @test check.case === :generic
  @test check.log2_residual < -150

  # the model over QQ resp. Q(sqrt 2) from the big period matrix
  verified(results) = all(r -> r.ok, results)
  @test verified(RSM.random_rational_g4_reconstruction_tests(1; kind = :generic))
  @test verified(RSM.random_rational_g4_reconstruction_tests(1; kind = :theta_null))
  if riesrf_long_tests()
    Qx, x = polynomial_ring(QQ, :x)
    K, _ = number_field(x^2 - 2, :a)
    @test verified(RSM.random_rational_g4_reconstruction_tests(2; field = K, all_places = true))
  end
end
