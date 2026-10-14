################################################################################
#
#  Diagnostics of the genus 4 reconstruction (not part of the test run).
#  Needs the setup of the reconstruction tests:
#
#    include("test/RieSrf/Reconstruction/setup_tests.jl")
#    include("test/RieSrfDiagnostics/ReconstructG4Diagnostics.jl")
#    g4_invariant_diagnostics(_random_g4_curve(:generic), 300)
#
################################################################################

# Where the precision is lost: (1) the numerical invariants of the exact
# canonical model (the invariant code alone), (2) those of the reconstruction,
# (3) the point check of the reconstruction (independent of the invariants).
function g4_invariant_diagnostics(f::MPolyRingElem, prec::Int = 300)
  Q0, Gamma0, t = _g4_canonical_model(f)
  Iex, ws = Hecke.g4_invariants(Q0, Gamma0)
  Iex = QQFieldElem[QQ(a) for a in Iex]
  CC = AcbField(prec)
  R, _ = polynomial_ring(CC, [:x1, :x2, :x3, :x4]; cached = false)
  toCC(p) = map_coefficients(CC, p; parent = R)
  I1, _ = _g4_invariants_numerical(toCC(Q0), toCC(Gamma0), t)
  exact_model = compare_invariants(Iex, AcbFieldElem[CC(a) for a in I1], ws).log2_diff
  # the exact model in random coordinates (like the reconstruction), without
  # and with relative noise 2^-noise_bits on the coefficients
  ys = gens(R)
  A = matrix(CC, 4, 4, [CC(rand() - 0.5, rand() - 0.5) for _ in 1:16])
  move(p) = evaluate(toCC(p), [sum(A[i, j] * ys[j] for j in 1:4) for i in 1:4])
  noise_bits = 200
  function noisy(p)
    s = maximum(RSM._abs64, coefficients(p))
    ctx = MPolyBuildCtx(R)
    for (c, e) in zip(coefficients(p), exponent_vectors(p))
      push_term!(ctx, c + CC(rand() - 0.5, rand() - 0.5) * s * CC(2)^(-noise_bits), e)
    end
    return finish(ctx)
  end
  Qm, Gm = move(Q0), move(Gamma0)
  I2, _, cond_moved = _g4_invariants_numerical(Qm, Gm, t)
  moved = compare_invariants(Iex, AcbFieldElem[CC(a) for a in I2], ws).log2_diff
  I3, _ = _g4_invariants_numerical(noisy(Qm), noisy(Gm), t)
  moved_noise = compare_invariants(Iex, AcbFieldElem[CC(a) for a in I3], ws).log2_diff
  RS = RSM.riemann_surface(f, prec; superelliptic = false, model = :original)
  reconstruction = _compare_with_original_g4(f, RS, false)
  data = RSM.reconstruct_curve_g4_data(RSM.small_period_matrix(RS))
  points = _g4_residual_on_points(RS, data, 4)
  _, _, cond_rec = _g4_invariants_numerical(_mpoly_midpoint(data.curve[1]), _mpoly_midpoint(data.curve[2]), t)
  radius = maximum(RSM._safe_log2(Float64(Hecke.radius(real(c))) + Float64(Hecke.radius(imag(c))))
                   for c in vcat(collect(coefficients(data.curve[1])), collect(coefficients(data.curve[2]))))
  return (exact_model = exact_model, moved = moved, moved_noise200 = moved_noise,
          reconstruction = reconstruction.log2_diff, points = points,
          normalization_moved = cond_moved, normalization_reconstruction = cond_rec,
          log2_max_radius = radius,
          info = data.info)
end

