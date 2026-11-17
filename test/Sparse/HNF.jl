@testset "Hermite normal form" begin
  @testset "pivot search with trailing zero rows" begin
    for rank in 0:5, zero_rows in 0:5
      A = sparse_matrix(ZZ, 0, 12)
      pivots = collect(2:2:2rank)
      for p in pivots
        push!(A, sparse_row(ZZ, [(p, ZZ(1))]))
      end
      for _ in 1:zero_rows
        push!(A, sparse_row(ZZ))
      end
      for p in 1:12
        @test Hecke.find_row_starting_with(A, p) == searchsortedfirst(pivots, p)
        for start in 1:nrows(A) + 1
          @test Hecke.find_row_starting_with(A, p, start) ==
            max(start, searchsortedfirst(pivots, p))
        end
      end
    end
  end

  @testset "forward reduction across short and long pivot gaps" begin
    columns = cumsum([1, 1, 3, 4, 5, 7, 8, 9, 15, 16, 17, 64])
    b = sparse_row(ZZ, [(p, ZZ(i)) for (i, p) in enumerate(columns)])
    for zero_rows in (0, 10), limit in (columns[8], columns[end])
      A = identity_matrix(SMat, ZZ, columns[end])
      for _ in 1:zero_rows
        push!(A, sparse_row(ZZ))
      end
      expected = sparse_row(ZZ,
        [(p, ZZ(i)) for (i, p) in enumerate(columns) if p > limit])
      for with_transform in (false, true)
        M = deepcopy(A)
        full = Hecke.reduce_full(M, b, Val(with_transform); limit = limit)
        right = Hecke.reduce_right(A, b, 1, Val(with_transform); limit = limit)
        @test full[1] == expected
        @test isempty(full[2])
        @test (with_transform ? right[1] : right) == expected
        @test M == A
        if with_transform
          for (reduced, ts) in ((full[1], full[3]), right)
            original = deepcopy(A)
            push!(original, deepcopy(b))
            for t in ts
              Hecke.apply_left!(original, t)
            end
            target = deepcopy(A)
            push!(target, deepcopy(reduced))
            @test original == target
          end
        end
      end
    end
  end

  @testset "reducers with trailing zero rows" begin
    # The old binary lookup returned empty row 6 instead of pivot row 5.
    for rank in (0, 5), zero_rows in (0, 1, 3, 10), limit in (4, 6)
      A = sparse_matrix(ZZ, 0, 6)
      for p in 1:rank
        push!(A, sparse_row(ZZ, [(p, ZZ(1))]))
      end
      for _ in 1:zero_rows
        push!(A, sparse_row(ZZ))
      end

      b = sparse_row(ZZ, [(1, ZZ(1)), (5, ZZ(2)), (6, ZZ(3))])
      expected = rank == 0 ? b :
        limit == 4 ? sparse_row(ZZ, [(5, ZZ(2)), (6, ZZ(3))]) :
        sparse_row(ZZ, [(6, ZZ(3))])
      original = deepcopy(A)
      reduced, ts = Hecke.reduce_right(A, b, 1, Val(true); limit = limit)
      @test reduced == expected
      @test Hecke.reduce_right(A, b; limit = limit) == expected
      @test A == original
      push!(original, deepcopy(b))
      for t in ts
        Hecke.apply_left!(original, t)
      end
      @test original[nrows(original)] == expected

      # A pivot hit, a missing pivot past the nonzero prefix, and an empty row.
      for g in (sparse_row(ZZ, [(5, ZZ(-2))]), b, sparse_row(ZZ))
        expected_full = sparse_row(ZZ,
          [(p, v) for (p, v) in zip(g.pos, g.values) if p > min(rank, limit)])
        if length(expected_full) > 0 && expected_full.values[1] < 0
          Hecke.scale_row!(expected_full, -1)
        end
        M = deepcopy(A)
        reduced, pivots, ts = Hecke.reduce_full(M, g, Val(true); limit = limit)
        @test reduced == expected_full
        @test isempty(pivots)
        @test M == A
        @test Hecke.reduce_full(deepcopy(A), g; limit = limit) ==
          (expected_full, Int[])
        original = deepcopy(A)
        push!(original, deepcopy(g))
        for t in ts
          Hecke.apply_left!(original, t)
        end
        push!(M, deepcopy(reduced))
        @test original == M
      end
    end
  end

  @testset "reduction across gaps in pivot columns" begin
    A = sparse_matrix(ZZ, 0, 101)
    for j in (2, 20, 40, 60, 80, 100)
      push!(A, sparse_row(ZZ, [(j, ZZ(1))]))
    end
    b = sparse_row(ZZ,
      [(1, ZZ(7)), (2, ZZ(-3)), (41, ZZ(5)), (80, ZZ(2)), (101, ZZ(9))])
    for trailing_zero in (false, true), limit in (41, 101)
      M = deepcopy(A)
      trailing_zero && push!(M, sparse_row(ZZ))
      original = deepcopy(M)
      reduced, ts = Hecke.reduce_right(M, b, 1, Val(true); limit = limit)
      expected = limit == 41 ?
        sparse_row(ZZ, [(1, ZZ(7)), (41, ZZ(5)), (80, ZZ(2)), (101, ZZ(9))]) :
        sparse_row(ZZ, [(1, ZZ(7)), (41, ZZ(5)), (101, ZZ(9))])
      @test reduced == expected
      @test Hecke.reduce_right(M, b; limit = limit) == expected
      @test M == original
      push!(original, deepcopy(b))
      for t in ts
        Hecke.apply_left!(original, t)
      end
      @test original[nrows(original)] == expected
    end

    # Exercise both pivot searches in a rank-deficient integer lattice, with
    # nonunit pivots, negative entries, and many unused columns.
    for _ in 1:10
      dense = zero_matrix(ZZ, 12, 101)
      for i in 1:12, j in (2, 20, 40, 60, 80, 100)
        dense[i, j] = rand(-3:3)
      end
      R = sparse_matrix(dense)
      H, ts = Hecke.hnf_kannan_bachem(R, Val(true))
      @test matrix(H) == hnf(dense)
      for t in ts
        Hecke.apply_left!(R, t)
      end
      @test R == H
    end
  end

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

  # Transformations recording the sign normalization of a reduced row
  A = sparse_matrix(matrix(ZZ, [1 0 0; 0 2 0]))
  for (b, start) in [(sparse_row(ZZ, [1], [-1]), 2),
                     (sparse_row(ZZ, [3], [-2]), 1),
                     (sparse_row(ZZ, [2, 3], [-2, -1]), 1)]
    r, T = Hecke.reduce_right(A, b, start, Val(true))
    @test !is_negative(r.values[1])
    @test Hecke.reduce_right(A, b, start) == r
    B = deepcopy(A)
    push!(B, b)
    for t in T
      Hecke.apply_left!(B, t)
    end
    @test B[3] == r
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
    pivots = [findfirst(!iszero, B[i, :]) for i in axes(B, 1)]
    for c in eachindex(w)
      iszero(w[c]) && continue
      i = findfirst(==(c), pivots)
      i === nothing && break
      p = w[c]
      w = [w[j] - p * B[i, j] for j in eachindex(w)]
    end
    c = findfirst(!iszero, w)
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
