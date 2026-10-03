@testset "NumericalKernel" begin
  CC = AcbField(1024)
  RR = ArbField(1024)
  NK = RSM.numerical_kernel

  # deterministic small integers in -5:5 (xorshift64; no RNG dependency)
  state = Ref{Int64}(88172645463325252)
  function nextint()
    x = state[]
    x = xor(x, x << 13); x = xor(x, x >>> 7); x = xor(x, x << 17)
    state[] = x
    return Int(mod(x, 11)) - 5
  end

  # ---- 1 & 2: known rank, certified enclosure of an exact kernel ----
  m, r0, n = 40, 17, 30
  G = [nextint() for i in 1:m, j in 1:r0]
  H = [nextint() for i in 1:r0, j in 1:n]
  P = G * H                                         # rank r0 over ZZ
  @test rank(matrix(ZZ, P)) == r0                   # validate the seed
  Acc = matrix(CC, m, n, [CC(P[i, j]) for i in 1:m for j in 1:n])
  N, r, resb = NK(Acc)
  @test r == r0
  @test (nrows(N), ncols(N)) == (n, n - r0)
  @test resb < RR(2)^(-900)
  Res = Acc * N            # exact entries times enclosures: must contain 0
  @test all(contains_zero(Res[i, j]) for i in 1:m, j in 1:(n - r0))

  # ---- 3: wide, huge nullity (the G5 line-99 shape), nullity kwarg ----
  Q2 = [nextint() for i in 1:10, j in 1:120]
  @test rank(matrix(ZZ, Q2)) == 10                  # validate the seed
  A2 = matrix(CC, 10, 120, [CC(Q2[i, j]) for i in 1:10 for j in 1:120])
  N2, r2, resb2 = NK(A2; nullity = 110)
  @test r2 == 10 && ncols(N2) == 110
  @test resb2 < RR(2)^(-900)

  # ---- 4: column permutation invariance of the span ----
  perm = vcat(2:2:n, 1:2:n)
  Ap = matrix(CC, m, n, [CC(P[i, perm[j]]) for i in 1:m for j in 1:n])
  Np, rp, _ = NK(Ap)
  @test rp == r0
  Nun = zero_matrix(CC, n, n - r0)
  for j in 1:n, t in 1:(n - r0)
    Nun[perm[j], t] = Np[j, t]
  end
  ResP = Acc * Nun
  @test all(contains_zero(ResP[i, j]) for i in 1:m, j in 1:(n - r0))

  # ---- 5: dynamic range far beyond Float64 (row scaling must save it) ----
  ks = [-600 + 150 * ((i - 1) % 9) for i in 1:m]    # exponents -600..600
  A3 = matrix(CC, m, n,
              [CC(QQFieldElem(2)^ks[i] * P[i, j]) for i in 1:m for j in 1:n])
  N3, r3, _ = NK(A3)
  @test r3 == r0
  Res3 = A3 * N3
  @test all(contains_zero(Res3[i, j]) for i in 1:m, j in 1:(n - r0))

  # ---- trivial kernel ----
  N6, r6, resb6 = NK(identity_matrix(CC, 5))
  @test r6 == 5 && ncols(N6) == 0
  @test iszero(resb6)

  # ---- 6: ambiguous rank gap must error, not answer ----
  # singular values exactly 1, 1e-9, 5e-11 at rtol 1e-10: kept/dropped
  # ratio ~20 < gap.  The bad scales must sit in the COLUMN geometry with
  # balanced rows (row scaling would repair a bad diagonal, correctly), so
  # conjugate the diagonal by an exact rational orthogonal matrix.
  O3 = matrix(QQ, 3, 3, [2, -1, 2, 2, 2, -1, -1, 2, 2]) * QQFieldElem(1, 3)
  @test O3 * transpose(O3) == identity_matrix(QQ, 3)
  D3 = diagonal_matrix([QQ(1), QQFieldElem(1, 10)^9,
                        QQFieldElem(1, 2) * QQFieldElem(1, 10)^10])
  A4Q = O3 * D3 * transpose(O3)
  A4 = matrix(CC, 3, 3, [CC(A4Q[i, j]) for i in 1:3 for j in 1:3])
  @test_throws ErrorException NK(A4)

  # ---- 7: pivot block not certifiably invertible must error ----
  A5 = matrix(CC, 2, 3, [CC(1), CC(1), CC(0), CC(1), CC(1), CC(0)])
  @test_throws ErrorException NK(A5; nullity = 1)

  # ---- argument validation ----
  @test_throws ArgumentError NK(Acc; nullity = -1)
  @test_throws ArgumentError NK(Acc; nullity = n + 1)
  @test_throws ArgumentError NK(A2; nullity = 100)   # rank 20 > min(m, n)
  @test_throws ArgumentError NK(Acc; rtol = 0.0)
  A7 = matrix(CC, 1, 1, [CC(1) / CC(0)])
  @test_throws ArgumentError NK(A7)

  # ---- pivots (_numerical_kernel_data) and the midpoint residual ----
  data = RSM._numerical_kernel_data(Acc)
  @test data.rank == r0 && length(data.pivot_columns) == r0 && length(data.pivot_rows) == r0
  @test rank(matrix(ZZ, P[data.pivot_rows, data.pivot_columns])) == r0
  @test RSM._log2_relative_residual(Acc, data.kernel) < -900
  data0 = RSM._numerical_kernel_data(Acc[1:m, data.pivot_columns]; nullity = 0)
  @test ncols(data0.kernel) == 0 && length(data0.pivot_rows) == r0
  @test rank(matrix(ZZ, P[data0.pivot_rows, data.pivot_columns])) == r0

  # ---- Vector-of-rows convenience method ----
  vv = [[CC(P[i, j]) for j in 1:n] for i in 1:m]
  Nv, rv, _ = NK(vv)
  @test rv == r0 && (nrows(Nv), ncols(Nv)) == (n, n - r0)
end
