@testset "p-rationality" begin
  # Lim 2022, Theorem 4.6
  ell = 11
  q = 2*ell + 1
  k, = cyclotomic_field(q)
  for p in PrimesSet(3, 4*ell - 1)
    p == ell && continue
    if modord(p, ell) == ell - 1
      @test is_quasi_p_rational(k, p; GRH = true)
      @test is_p_rational(k, p; GRH = true)
      @test is_real_cyclotomic_field_p_rational(q, p)
    end
  end

  ell = 53
  q = 2*ell + 1
  k, = cyclotomic_field(q)
  for p in PrimesSet(3, 4*ell - 1)
    p == ell && continue
    if modord(p, ell) == ell - 1
      @test is_real_cyclotomic_field_p_rational(q, p)
    end
  end

  ell = 13
  S = [151,241,4325341,8292133]
  k, = cyclotomic_real_subfield(ell)
  for p in S
    @test !is_quasi_p_rational(k, p; GRH = true)
    @test !is_p_rational(k, p; GRH = true)
    @test !is_real_cyclotomic_field_p_rational(ell, p)
  end
  SS = [2, 3, 5, 7]
  for p in SS
    @test is_quasi_p_rational(k, p; GRH = true)
    @test is_p_rational(k, p; GRH = true)
    @test is_real_cyclotomic_field_p_rational(ell, p)
  end

  Qx, x = QQ[:x]
  f = x^3 - 5*x + 3
  K, = number_field(f)
  @test is_quasi_p_rational(K, 3)
  @test is_p_rational(K, 3)
  @test is_quasi_p_rational(K, 257)
  @test is_p_rational(K, 257)
  @test !is_p_rational(K, 2)

  # Benmerieme--Movahhedi 2021, Example 3.7 and Proposition 2.9
  K, = quadratic_field(35)
  @test is_p_rational(K, 5)
  K, = quadratic_field(6)
  @test !is_p_rational(K, 3)

  # Benmerieme--Movahhedi 2021, examples following Corollary 2.7
  # (the class numbers are 3 and 5, respectively)
  K, = quadratic_field(-23)
  @test is_p_rational(K, 3)
  K, = quadratic_field(-47)
  @test is_p_rational(K, 5)

  # Further low-degree examples: imaginary quadratic, real quadratic, and complex cubic
  K, = quadratic_field(-1)
  for p in [2, 3, 5, 7]
    @test is_p_rational(K, p)
  end

  K, = quadratic_field(5)
  for p in [2, 3, 5, 13]
    @test is_p_rational(K, p)
  end

  K, = number_field(x^3 - x - 1)
  for p in [5, 7, 11, 13]
    @test is_p_rational(K, p)
  end

  # corner cases
  K, = quadratic_field(17; cached = false)
  @test length(prime_ideals_over(maximal_order(K), 2)) == 2
  @test !is_quasi_p_rational(K, 2)

  K, = quadratic_field(85; cached = false)
  OK = maximal_order(K)
  @test is_divisible_by(class_number(OK), 2)
  @test is_tamely_ramified(K, 2)
  @test is_quasi_p_rational(K, 2)
  @test !is_p_rational(K, 2)
end

function _multiquadratic_field(ds)
  Qx, x = polynomial_ring(QQ, "x"; cached = false)
  K, = number_field([x^2 - d for d in ds]; cached = false)
  L, = simple_extension(K)
  return L
end

@testset "is_p_rational: test cases from literature" begin
  @testset "1. Lin-Guo real quadratic family" begin
    # Theorem 3.3: Q(sqrt(p(p + 1))) is p-rational for every odd prime p.
    # https://arxiv.org/abs/2607.21250
    for p in [3, 5, 7, 11, 37, 101]
      K, _ = quadratic_field(p * (p + 1); cached = false)
      @test is_p_rational(K, p)
    end
  end

  @testset "2. Benmerieme-Movahhedi biquadratic families" begin
    # Propositions 4.2 and 4.4, for primes p > 3.
    # https://arxiv.org/abs/2007.04864
    for p in [5, 7, 11, 37]
      K1 = _multiquadratic_field([p * (p + 2), -p])
      @test is_p_rational(K1, p)

      K2 = _multiquadratic_field([p * (p + 2), p * (p - 2)])
      @test is_p_rational(K2, p)
    end
  end

  @testset "3. Pitoun-Varescon negative quadratic example" begin
    # Example 4.2: the 3-ramified torsion group is Z/3Z.
    # https://arxiv.org/abs/1302.3099
    K, _ = quadratic_field(-129; cached = false)
    @test !is_p_rational(K, 3)
  end

  @testset "4. Gras negative quadratic example" begin
    # Remark 6.1.
    # https://arxiv.org/abs/1709.06388
    K, _ = quadratic_field(-383; cached = false)
    @test !is_p_rational(K, 17)
  end

  @testset "5. Irregular cyclotomic prime" begin
    # Q(zeta_p) is p-rational if and only if p is regular; 37 is irregular.
    K, _ = cyclotomic_field(37; cached = false)
    @test !is_p_rational(K, 37)
  end

  @testset "6. Li-Qiu cubic and quartic negative examples" begin
    # Examples from the cubic and quartic tables.
    # https://arxiv.org/abs/2304.10157
    Qx, x = polynomial_ring(QQ, "x"; cached = false)

    K3, _ = number_field(x^3 - x^2 + x - 9, "a"; cached = false)
    @test !is_p_rational(K3, 13)

    K4a, _ = number_field(x^4 + 1, "a"; cached = false)
    @test !is_p_rational(K4a, 13)
    @test !is_p_rational(K4a, 31)

    K4b, _ = number_field(x^4 - 2 * x^2 + 4, "a"; cached = false)
    @test !is_p_rational(K4b, 7)
  end
end
