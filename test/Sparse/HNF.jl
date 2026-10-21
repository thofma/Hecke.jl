@testset "Hermite normal form" begin
  for i in 1:10
    r = 20
    c = 10
    A = matrix(ZZ, rand([0,0,0,0,0,0,0,0,0,0,1], r, c))
    As = sparse_matrix(A)
    @test hnf(A) == ZZMatrix(hnf(As))

    H, T = Hecke.hnf_kannan_bachem(As, Val(true))
    B = deepcopy(As)

    for t in T
      Hecke.apply_left!(B, t)
    end

    @test ZZMatrix(B) == hnf(A)
  end

  p = 23
  m = matrix(ZZ, 30, 20, [powermod(i, j, p) for i=1:30 for j=1:20])
  hm = hnf(m)
  sm = sparse_matrix(m)
  @test hm == matrix(hnf(sm))
  @test hm == matrix(hnf(sm; auto = true))
  h = hnf(hcat(sm, identity_matrix(SMat, ZZ, 30)); limit = 20, auto = true)
  @test matrix(sub(h, 1:30, 1:20)) == hm
  @test abs(det(sub(h, 1:30, 21:50))) == 1

  @test elementary_divisors(hm) == elementary_divisors(sm)

  let # nnz issues
    A1 = matrix(ZZ, [1 1 ; 0 1])
    A2 = matrix(ZZ, [7  5  9; 3 8 3; -4 -4 3])
    A3 = matrix(ZZ, [1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 1; 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0; 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2 0 0; 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 1 0; 0 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 2 1 0; 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 1 1 1; 0 0 0 0 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 3 0; 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 1 0 0; 0 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 1 1 0; 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 1 0 1 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 1 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2 0 0 0 0 0; 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 2 0; 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 1; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 2 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 1 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 0 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 2; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 1; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2 1 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0; 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0])
    for A in [A1, A2, A3]
      @test nnz(sparse_matrix(hnf(A))) == nnz(hnf(sparse_matrix(A)))
      @test nnz(sparse_matrix(hnf(A))) == nnz(Hecke.hnf_kannan_bachem(sparse_matrix(A), Val(true))[1])
    end
  end
end



@testset "Field row reduction preserves its inputs" begin
  # Compute the leading-pivot remainder independently using dense vectors.
  function dense_remainder(R, M, v)
    B = deepcopy(map(R, M))
    w = deepcopy(map(R, v))
    pivots = [findfirst(x -> !iszero(x), B[i, :]) for i in axes(B, 1)]
    for c in eachindex(w)
      iszero(w[c]) && continue
      i = findfirst(==(c), pivots)
      i === nothing && break
      p = w[c]
      w = [w[j] - p * B[i, j] for j in eachindex(w)]
    end
    c = findfirst(x -> !iszero(x), w)
    if c !== nothing
      p = inv(w[c])
      w = [p * x for x in w]
    end
    return w
  end

  function check_reduction(R, M, v; new_g = false, row_alias = false,
                           coefficient_alias = false)
    A = sparse_matrix(matrix(R, M))
    g = row_alias ? A[1] : sparse_row(matrix(R, 1, length(v), v))
    if coefficient_alias
      # In QQ this is the same mutable coefficient object, not just an equal
      # coefficient. Mutating the working row must not change either owner.
      g.values[1] = A[1].values[2]
      @test g.values[1] === A[1].values[2]
    end
    A_before = deepcopy(A)
    g_before = deepcopy(g)
    expected = dense_remainder(R, M, v)

    r = Hecke.reduce(A, g; new_g)
    @test Vector(r, length(v)) == expected
    @test A == A_before
    @test g == g_before
    @test r !== g
    @test r.pos !== g.pos
    @test r.values !== g.values
    for a in A.rows
      @test r.pos !== a.pos
      @test r.values !== a.values
    end

    # Test ownership of coefficient objects as well as of the two arrays.
    if !isempty(r.values)
      r.values[1] = add!(r.values[1], r.values[1], one(R))
      @test A == A_before
      @test g == g_before
    end
    push!(r.pos, length(v) + 1)
    push!(r.values, one(R))
    @test A == A_before
    @test g == g_before
  end

  M = [1 2 0 0 3 0 0; 0 1 4 0 0 5 0; 0 0 1 0 0 0 6]
  gap = [1 0 2 0 1 0 0; 0 0 1 2 0 0 3; 0 0 0 0 1 4 5]
  square = [1 2 3; 0 1 4; 0 0 1]
  cases = ((M, [2, 3, 1, 0, 5, 7, 2]), # several pivots and fill-in
           (M, [2, 3, -8, 0, 6, -5, -24]), # a linear combination of basis rows
           (M, zeros(Int, 7)),
           (gap, [2, 3, 1, 0, 5, 7, 2]), # stop at the first missing pivot
           (gap, [0, 3, 1, 0, 5, 7, 2]), # normalize without any reduction
           (zeros(Int, 0, 7), [2, 3, 1, 0, 5, 7, 2]),
           (square, [2, 3, 1]))

  F4 = GF(2, 2)
  rings = (QQ, GF(101), residue_ring(ZZ, 101)[1], GF(2), F4)
  @testset "R = $R, new_g = $new_g" for R in rings, new_g in (false, true)
    for (B, v) in cases
      check_reduction(R, B, v; new_g)
    end
    check_reduction(R, M, collect(M[1, :]); new_g, row_alias = true)
    check_reduction(R, M, [2, 3, 1, 0, 5, 7, 2];
                    new_g, coefficient_alias = true)
  end

  # Use non-prime-field coefficients too, including p == -p in characteristic 2.
  a = gen(F4)
  M4 = [F4(1) a F4(1) F4(0); F4(0) F4(1) a F4(1)]
  for new_g in (false, true)
    check_reduction(F4, M4, [a, F4(1), a + 1, F4(1)]; new_g)
  end
end
