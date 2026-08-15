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
      for tries in 1:20
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
