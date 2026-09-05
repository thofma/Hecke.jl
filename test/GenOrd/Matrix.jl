@testset "Modular HNF" begin
  @testset "Regression test for initial implementation" begin
    # in the initial implementation we have missed:
    # implicit row with g*e_i should be made explicit and used when merging leftovers (strong echelon)
    # related to this: zero pivot column should be handled (with the help of extra row)
    # nonsquarefree modulus must be handled (the residue ring might have zero divisors)

    M = matrix(ZZ, 3, 2, [4, 0, 0, 4, 1, 2])
    @test Hecke.hnf(M, :lowerleft) == Hecke._hnf_modular_eldiv_left_generic!(deepcopy(M), ZZ(4))

    M = matrix(ZZ, 3, 2, [4, 0, 0, 4, 2, 0])
    @test Hecke.hnf(M, :lowerleft) == Hecke._hnf_modular_eldiv_left_generic!(deepcopy(M), ZZ(4))

    R, x = polynomial_ring(GF(5), "x")
    g = x^3 + x^2
    M = vcat(matrix(R, 1, 2, [x + 2, 3*x]), g*identity_matrix(R, 2))
    @test Hecke.hnf(M, :lowerleft) == Hecke._hnf_modular_eldiv_left_generic!(deepcopy(M), g)

    kx, x = rational_function_field(QQ, :x; cached = false)
    R = localization(kx, degree; cached=false)
    M = matrix(R, 3, 2, [1//x, 0, 0, 1//x, 1, 1//x])
    @test Hecke.hnf(M, :lowerleft) == Hecke._hnf_modular_eldiv_left_generic!(deepcopy(M), R(1//x))
  end

  @testset "Random inputs" begin
    # To properly test largest elementary divisor, we will generate random matrix
    #   by starting from SNF and applying random unimodular transforms

    function _random_unimodular(R::Ring, n::Int, v...; nops::Int = 4*n)
      U = identity_matrix(R, n)
      n < 2 && return U

      for _ in 1:nops
        i, j = rand(1:n), rand(1:n - 1)
        j = j >= i ? j + 1 : j
        add_row!(U, rand(R, v...), i, j)
      end
      return U
    end

    # m x n (m >= n) of full column rank with elementary divisors exactly d[1] | ... | d[n]
    function _random_full_column_rank(R::Ring, m::Int, n::Int, d::Vector, v...)
      @assert m >= n && length(d) == n
      D = vcat(diagonal_matrix(R, d), zero_matrix(R, m - n, n))
      return _random_unimodular(R, m, v...)*D*_random_unimodular(R, n, v...)
    end

    function _test_ring(R::Ring, dv, uv)
      for _ in 1:20
        n = rand(2:5)
        m = n + rand(0:3)
        d = accumulate(*, [one(R); [rand(R, dv...) for _ in 2:n]])
        M = _random_full_column_rank(R, m, n, d, uv...)
        M_hnf = Hecke.hnf(M, :lowerleft)

        @test Hecke._hnf_modular_eldiv_left_generic!(deepcopy(M), d[n]) == M_hnf
        @test Hecke._hnf_modular_eldiv_left_generic!(deepcopy(M), prod(d)) == M_hnf
      end
    end

    _test_ring(ZZ, (2:5,), (-3:3,))

    kx, _ = polynomial_ring(GF(5), :x; cached = false)
    _test_ring(kx, (1:3,), (0:3,))

    kx, _ = polynomial_ring(GF(ZZRingElem(2)^127 + 45), :x; cached = false)
    _test_ring(kx, (1:3,), (0:3,))

    kx, _ = polynomial_ring(GF(5, 3), :x; cached = false)
    _test_ring(kx, (1:3,), (0:3,))

    kx, _ = polynomial_ring(Native.GF(5), :x; cached = false)
    _test_ring(kx, (1:3,), (0:3,))
  end
end

@testset "Weak Popov" begin
  _test_rows_content(P::MatElem) = nothing
  function _test_rows_content(P::MatElem{QQPolyRingElem})
    for i in 1:nrows(P)
      @test is_zero_row(P, i) || is_one(Hecke._row_content(P, i))
    end
  end

  function _test_output(P::MatElem, r, H)
    @test is_weak_popov(P, r)
    @test hnf(P) == H
    _test_rows_content(P)
  end

  function _test_output(P, U, r, M, H)
    _test_output(P, r, H)
    @test P == U*M
    @test is_unit(det(U))
  end

  function _test_with_input(M)
    M_hnf = hnf(M)
    M_r = rank(M)

    P = Hecke._weak_popov!(deepcopy(M))
    _test_output(P, M_r, M_hnf)

    P, U = Hecke._weak_popov_with_transform!(deepcopy(M))
    _test_output(P, U, M_r, M, M_hnf)

    PP = Hecke._weak_popov!(deepcopy(vcat(M, M)))
    _test_output(PP, M_r, vcat(M_hnf, zero_matrix(base_ring(P), nrows(M), ncols(M))))
  end

  @testset "Random inputs" begin
    function _test_ring(R::PolyRing, uv)
      for _ in 1:20
        m = rand(2:5)
        n = rand(2:5)

        M = zero_matrix(R, m, n)
        for i in 1:m, j in 1:n
          M[i, j] = rand(R, uv...)
        end

        _test_with_input(M)
      end
    end

    kx, _ = polynomial_ring(GF(5), :x; cached = false)
    _test_ring(kx, (0:3,))

    kx, _ = polynomial_ring(QQ, :x; cached = false)
    _test_ring(kx, (0:2, -3:3))
  end

  @testset "Edge cases" begin
    Qx, x = polynomial_ring(QQ, :x; cached = false)

    # check that we strip row contents even when intermediate gcd is 1
    M = matrix(Qx, 1, 4, [2*x, x, 1//2 * x, 1//4 * x])
    _test_with_input(M)

    # check that zero rows are handled
    M = matrix(Qx, 2, 2, [x^2, x + 1, 0, 0])
    _test_with_input(M)

    # check that zero columns are handled
    M = matrix(Qx, 2, 2, [x^2, 0, x + 1, 0])
    _test_with_input(M)
  end

  @testset "No mutation of aliased entries" begin
    Qx, x = polynomial_ring(QQ, :x; cached = false)

    A = matrix(Qx, 2, 2, [x^2 + 1, x, 3*x^2 + 2, 5*x + 1])
    A_orig = deepcopy(A)
    B = vcat(A, identity_matrix(Qx, 2))
    Hecke._weak_popov!(B)
    # NOTE: AbstractAlgebra.weak_popov!(B, similar(B, 0, 0), similar(B, 0, 0))
    #   would fail this test
    @test A == A_orig

    A = deepcopy(A_orig)
    B = vcat(A, identity_matrix(Qx, 2))
    Hecke._weak_popov_with_transform!(B)
    # NOTE: AbstractAlgebra.weak_popov!(B, similar(B, 0, 0), similar(B, 0, 0), false, true)
    #   would fail this test
    @test A == A_orig
  end
end
