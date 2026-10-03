# Reconstruction of random curves of genus 1, 2 and 3 from their small period
# matrices, compared with the original curves by their invariants
# (random_reconstruction_tests; ok: agreement to half the precision). The
# curves are random, so the seed is fixed.
@testset "Reconstruction genus 1-3" begin
  Hecke.Random.seed!(4711)
  ok(results) = all(r -> r.result.ok == true, results)
  n = riesrf_long_tests() ? 5 : 2
  @test ok(RSM.random_reconstruction_tests(n; genus = 1, prec = 200))
  @test ok(RSM.random_reconstruction_tests(n; genus = 2, prec = 200))
  @test ok(RSM.random_reconstruction_tests(n; genus = 3, hyperelliptic = true, prec = 300))
  @test ok(RSM.random_reconstruction_tests(n; genus = 3, prec = 400))
end
