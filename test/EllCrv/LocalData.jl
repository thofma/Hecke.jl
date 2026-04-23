# Fully qualified reduction enum `EllipticCurveReduction.good` etc are too verbose for tests
const good = EllipticCurveReduction.good
const additive = EllipticCurveReduction.additive
const split_mult = EllipticCurveReduction.split_multiplicative
const nonsplit_mult = EllipticCurveReduction.nonsplit_multiplicative

function _check_reduction_impl(ld, ks, cv, tn, rt)
  @test ld.kodaira_symbol == ks
  @test ld.conductor_valuation == cv
  @test ld.tamagawa_number == tn
  @test ld.reduction_type == rt
end

_good_reduction(p) = (p, "I0", 0, 1, good)

function _check_reduction(E, p, ks, cv, tn, rt)
  ld = tates_algorithm_local(E, p, EllipticCurveLocalData)
  _check_reduction_impl(ld, ks, cv, tn, rt)
end

@testset "Local Data" begin
  @testset "Tate's algorithm over QQ" begin
    E = elliptic_curve([625, -15625, 19531250, -2929687500, -34332275390625])
    EE = @inferred tates_algorithm_global(E)
    @test a_invariants(EE) == (1, -1, 0, 4, 3)

    E = elliptic_curve([1,2,3,4,5])
    EE = @inferred tates_algorithm_global(E)
    @test a_invariants(EE) == (1, -1, 0, 4, 3)

    function _check_reduction_minimal(E, p, ks, cv, tn, rt)
      ld = tates_algorithm_local(E, p, EllipticCurveLocalData)
      _check_reduction_impl(ld, ks, cv, tn, rt)
      @test a_invariants(tidy_model(ld.minimal_model)) == a_invariants(E)
    end

    E = elliptic_curve([1, 1, 0, 40050, 7557750])   # 25350.a1
    for (p, ks, cv, tn, rt) in [
        (2,  "I1",   1, 1, nonsplit_mult),
        (3,  "I2",   1, 2, nonsplit_mult),
        (5,  "III*", 2, 2, additive),
        (13, "IV*",  2, 1, additive),
        _good_reduction(17)]
      _check_reduction_minimal(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve([1, 1, 0, -20700, 1134000])  # 150.a1
    for (p, ks, cv, tn, rt) in [
        (2, "I5",   1, 1, nonsplit_mult),
        (3, "I10",  1, 2, nonsplit_mult),
        (5, "III*", 2, 2, additive)]
      _check_reduction_minimal(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve([0, 0, 0, 2, 2])         # 2240.y1
    for (p, ks, cv, tn, rt) in [
        (2, "II", 6, 1, additive),
        (5, "I1", 1, 1, nonsplit_mult),
        (7, "I1", 1, 1, nonsplit_mult)]
      _check_reduction_minimal(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve([0, 0, 0, 0, -1])        # 144.a3
    for (p, ks, cv, tn, rt) in [
        (2, "II",  4, 1, additive),
        (3, "III", 2, 2, additive)]
      _check_reduction_minimal(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve([0, 0, 0, 108, 0])       # 576.a2
    for (p, ks, cv, tn, rt) in [
        (2, "I2*",  6, 2, additive),
        (3, "III*", 2, 2, additive)]
      _check_reduction_minimal(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve([0, -1, 0, -208, 1412])  # 800.b1
    for (p, ks, cv, tn, rt) in [
        (2, "I0*", 5, 2, additive),
        (5, "IV*", 2, 3, additive)]
      _check_reduction_minimal(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve([0, 0, 0, 0, -9])        # 3888.k1
    for (p, ks, cv, tn, rt) in [
        (2, "II", 4, 1, additive),
        (3, "IV", 5, 1, additive)]
      _check_reduction_minimal(E, p, ks, cv, tn, rt)
    end

    # minimal model is (858.k1): y^2 + xy = x^3 - 5774401*x + 5346023177
    E = elliptic_curve([-7483623723, 249446508217254])
    for (p, ks, cv, tn, rt) in [
        (2,  "I7",  1, 7, split_mult),
        (3,  "I14", 1, 14, split_mult),
        (11, "I7",  1, 7, split_mult),
        (13, "I3",  1, 1, nonsplit_mult)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    # minimal model is (58299.a1): y^2 + x*y = x^3 + 9*x + 18
    E = elliptic_curve([1, 0, 4, 7, 14])
    @test a_invariants(tates_algorithm_global(E)) == (1, 0, 0, 9, 18)
    for (p, ks, cv, tn, rt) in [
        (3,     "I2", 1, 2, split_mult),
        (19433, "I1", 1, 1, nonsplit_mult)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    # minimal model is (2752.c1): y^2 = x^3 + 16*x + 32
    E = elliptic_curve([0, 0, 0, 1, 1//2])
    for (p, ks, cv, tn, rt) in [
        (2,  "II*", 6, 1, additive),
        (43, "I1",  1, 1, nonsplit_mult)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    # not in LMFDB, local data was computed with sage
    E = elliptic_curve([0, 0, 0, 75, 657625])
    for (p, ks, cv, tn, rt) in [
        (2,   "IV",  2, 1, additive),
        (3,   "III", 2, 2, additive),
        (5,   "I5*", 2, 4, additive),
        (17,  "I1",  1, 1, split_mult),
        (521, "I1",  1, 1, nonsplit_mult)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end
  end

  @testset "Tate's algorithm over number fields" begin
    x = gen(Hecke.Globals.Qx)

    _principal(OL, x) = numerator(ideal(OL, x))

    function _check_reduction_nf(E, p, ks, cv, tn, rt)
      ld = tates_algorithm_local(E, p, EllipticCurveLocalData)
      _check_reduction_impl(ld, ks, cv, tn, rt)

      d_E  = valuation(discriminant(E), p)
      d_Em = valuation(discriminant(ld.minimal_model), p)
      @test d_E >= d_Em
      @test (d_E - d_Em) % 12 == 0
    end

    # Q(sqrt(-3))
    L, a = number_field(x^2 - x + 1)
    OL = ring_of_integers(L)

    E = elliptic_curve(L, [0, 1+a, a, a, 0])    # 2.0.3.1-49.1-CMa1
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, 1 - 3*a), "II", 2, 1, additive),
        _good_reduction(5*OL)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve(L, [0, 0, 0, -15, 22])   # 2.0.3.1-144.1-CMa2
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, 1 - 2*a), "I0*", 2, 2, additive),
        (2*OL,                    "IV*", 2, 3, additive)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve(L, [0, a, a, -1+a, 0])   # 2.0.3.1-673.1-a1
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, 29*a - 8), "I1", 1, 1, nonsplit_mult)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve(L, [1, -1, 0, -2, -1])   # 2.0.3.1-2401.3-a1
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, 1 - 3*a), "III", 2, 2, additive),
        (_principal(OL, 3*a - 2), "III", 2, 2, additive)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve(L, [1, -1, 0, 6 - 57*a, 108 - 162*a])  # 2.0.3.1-12321.1-b2
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, 1 - 2*a), "III*", 2, 2, additive),
        (_principal(OL, 4 - 7*a), "II",   2, 1, additive)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    # Q(sqrt(5))
    L, a = number_field(x^2 - x - 1)
    OL = ring_of_integers(L)

    E = elliptic_curve(L, [1, 1, 1, -3, 1])     # 2.2.5.1-100.1-b2
    for (p, ks, cv, tn, rt) in [
        (2*OL,                    "I5", 1, 5, split_mult),
        (_principal(OL, 1 - 2*a), "IV", 2, 3, additive),
        _good_reduction(3*OL)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    # Q(sqrt(3))
    L, a = quadratic_field(3)
    OL = ring_of_integers(L)

    # not in LMFDB, local data was computed with sage
    E = elliptic_curve(L, [0, 0, 0, 81, 243*a])
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, 1 + a), "II",  8, 1, additive),
        (_principal(OL, a),     "II*", 4, 1, additive),
        (_principal(OL, a + 4), "I1",  1, 1, nonsplit_mult),
        (_principal(OL, a - 4), "I1",  1, 1, nonsplit_mult)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    # not in LMFDB, local data was computed with sage
    E = elliptic_curve(L, [0, 0, 0, 3, 1])
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, 1 + a), "IV*", 2, 1, additive),
        (_principal(OL, a),     "IV",  4, 1, additive),
        (5*OL,                  "I1",  1, 1, split_mult)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    # not in LMFDB, local data was computed with sage
    E = elliptic_curve(L, [0, 0, 27, 0, 486])
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, a),        "IV*", 8, 1, additive),
        (_principal(OL, -2*a + 1), "II",  2, 1, additive),
        (_principal(OL, -2*a - 1), "II",  2, 1, additive)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    # not in LMFDB, local data was computed with sage
    E = elliptic_curve(L, [1, 0, 4, 7, 14])
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, a), "I4", 1, 4, split_mult),
        (19433*OL,          "I1", 1, 1, split_mult)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    # 5.5.14641.1-121.1-c3
    L, a = number_field(x^5 - x^4 - 4*x^3 + 3*x^2 + 3*x - 1)
    OL = ring_of_integers(L)

    E = elliptic_curve(L, [0, a-1, a^3+a^2-2*a-1, -2*a-1, -a^4-a^3+a^2-a-2])
    for (p, ks, cv, tn, rt) in [
        (_principal(OL, a^2+a-2), "I5*", 2, 2, additive)]
      _check_reduction_nf(E, p, ks, cv, tn, rt)
    end

    K, a = number_field(x^2- x + 1)
    E = elliptic_curve(K, [16807*a - 84035, 41241385934*a + 5367031656, 20124912723078142//3*a + 13331154044930911//3, 928925752459624769703*a - 289907255041158152853, -221729762092842673528466044620617//9*a + 22979609049341545658321384288371//9])
    lp = prime_decomposition(maximal_order(K), 7)
    if a + 4 in lp[1][1]
      P = lp[1][1]
    else
      P = lp[2][1]
    end
    @test "I0" == @inferred kodaira_symbol(E, P)
  end

  @testset "Tate's algorithm over rational function fields" begin
    K, t = rational_function_field(QQ, :t)

    # local data was computed with Magma

    E = elliptic_curve_from_j_invariant(t)
    for (p, ks, cv, tn, rt) in [
        (t,        "II",   2, 1, additive),
        (t - 1728, "III*", 2, 2, additive),
        (1//t,     "I1",   1, 1, split_mult)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve_from_j_invariant(t^3 + t + 1)
    for (p, ks, cv, tn, rt) in [
        (t^3 + t - 1727,  "III*", 2, 2, additive),
        (t^3 + t + 1,     "II",   2, 1, additive),
        (1//t,            "I3",   1, 3, split_mult),
        _good_reduction(t)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve(K, [0, 1, 0, 2, t])
    for (p, ks, cv, tn, rt) in [
        (t^2 - 32//27*t + 28//27,  "I1",  1, 1, nonsplit_mult),
        (1//t,                     "II*", 2, 1, additive)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve(K, [0, t, 0, t^4, 0])
    for (p, ks, cv, tn, rt) in [
        (t - 1//2, "I1",  1, 1, nonsplit_mult),
        (t + 1//2, "I1",  1, 1, split_mult),
        (t,        "I4*", 2, 4, additive),
        _good_reduction(1//t)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    k, a = quadratic_field(2)
    K, t = rational_function_field(k, "t")

    E = elliptic_curve_from_j_invariant(1//(t^2 + t + a))
    for (p, ks, cv, tn, rt) in [
        (t^2 + t + 1//1728*(1728*a - 1), "III*", 2, 2, additive),
        (t^2 + t + a,                    "I1",   1, 1, split_mult),
        (1//t,                           "IV",   2, 1, additive)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    E = elliptic_curve_from_j_invariant(t^2 - 2)
    for (p, ks, cv, tn, rt) in [
        (t^2 - 1730, "III*", 2, 2, additive),
        (t - a,      "II",   2, 1, additive),
        (t + a,      "II",   2, 1, additive),
        (1//t,       "I2",   1, 2, split_mult)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    K, t = rational_function_field(GF(2), "t")

    E = elliptic_curve_from_j_invariant(t^3//(t^2 + t + 1))
    for (p, ks, cv, tn, rt) in [
        (t,           "I0*", 5, 2, additive),
        (t^2 + t + 1, "I1",  1, 1, split_mult),
        (1//t,        "I1",  1, 1, split_mult),
        _good_reduction(t+1)]
      _check_reduction(E, p, ks, cv, tn, rt)
    end

    kt,t = rational_function_field(GF(113),:t)
    ainvs = kt.([(66*t^7 + 86*t^3)//(t^8 + 31*t^4 + 99), (41*t^14 + 34*t^10 + 72*t^6 + 47*t^2)//(t^16 + 62*t^12 + 29*t^8 + 36*t^4 + 83), (65*t^17 + 48*t^13 + 71*t^9 + 48*t^5 + 6*t)//(t^24 + 93*t^20 + 16*t^16 + 67*t^12 + 2*t^8 + 35*t^4 + 81), (58*t^24 + 93*t^20 + 98*t^16 + 26*t^12 + 55*t^8 + 46*t^4 + 15)//(t^32 + 11*t^28 + 60*t^24 + 52*t^20 + 47*t^16 + 63*t^12 + 8*t^8 + 100*t^4 + 109), 0])
    E = elliptic_curve(ainvs)

    @test all(isone(denominator(i)) for i in a_invariants(integral_model(E)[1]))
    Eglobal = tates_algorithm_global(E)
    ainvs_minimal = kt.([0, 103*t^4 + 53*t^2 + 78, 0, 14*t^8 + 61*t^6 + 2*t^4 + 44*t^2 + 50, 86*t^12 + 59*t^10 + 93*t^8 + 27*t^6 + 109*t^4 + 17*t^2 + 48])
    Eglobal2 = elliptic_curve(ainvs_minimal)
    @test is_isomorphic(Eglobal2, Eglobal)
    @test discriminant(Eglobal) == discriminant(Eglobal2)
  end

  @testset "Invariance of Tate's algorithm under transform" begin
    function _check_reduction_transform(E, p, rstu, ld)
      EE = integral_model(transform_rstu(E, rstu)[1])[1]
      tld = tates_algorithm_local(EE, p, EllipticCurveLocalData)

      @test tld.kodaira_symbol      == ld.kodaira_symbol
      @test tld.conductor_valuation == ld.conductor_valuation
      @test tld.tamagawa_number     == ld.tamagawa_number
      @test tld.reduction_type      == ld.reduction_type
    end

    x = gen(Hecke.Globals.Qx)

    E = elliptic_curve([1, 1, 0, 40050, 7557750])   # 25350.a1
    for p in [2, 3, 5, 11, 13]
      ld = tates_algorithm_local(E, p, EllipticCurveLocalData)
      for rstu in [[12, 10, 7, 6*11], [0, 0, 0, 13*25*8]]
        _check_reduction_transform(E, p, rstu, ld)
      end
    end

    L, a = number_field(x^2 - x - 1)
    OL = ring_of_integers(L)

    E = elliptic_curve(L, [1, 1, 1, -3, 1])     # 2.2.5.1-100.1-b2
    for p in [2*OL, numerator((1-2*a)*OL), 3*OL]
      ld = tates_algorithm_local(E, p, EllipticCurveLocalData)
      for rstu in [[12, -1, 1 + 2*a, 3 + a], [2+a, 1 - a, 0, (3-a)*8*(1 - 2*a)]]
        _check_reduction_transform(E, p, rstu, ld)
      end
    end

    K, t = rational_function_field(QQ, :t)
    E = elliptic_curve(K, [0, t, 0, t^4, 0])
    for p in [t, t - 1//2, 1//t]
      ld = tates_algorithm_local(E, p, EllipticCurveLocalData)
      for rstu in [[t+1, 1, 0, (t^2+1)//(t+3)], [1, 1//(t+3), 1, t^6]]
        _check_reduction_transform(E, p, rstu, ld)
      end
    end
  end

  @testset "Conductors, local getters" begin
    E = elliptic_curve([1, 1, 0, 40050, 7557750])
    @test conductor(E) == 25350
    @test (@inferred tamagawa_numbers(E)) == [1, 2 ,2, 1]
    @test (@inferred kodaira_symbols(E)) == ["I1", "I2", "III*", "IV*"]

    Rx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x^2-x+3)
    E = elliptic_curve(K, [0, -1, 1, -7820, -263580])
    OK = ring_of_integers(K)
    I = (-2*a+1)*OK
    @test I == @inferred conductor(E)

    L, a = number_field(x^2-x+1)
    E = elliptic_curve(L, [0, 0, 0, -15, 22])
    Ps = bad_primes(E)
    sort!(Ps, by = x -> minimum(x))
    @test tamagawa_number.(Ref(E), Ps) == [3, 2]
    @test kodaira_symbol.(Ref(E), Ps) == ["IV*", "I0*"]
    @test @inferred issetequal(tamagawa_numbers(E), [3, 2])
    @test @inferred issetequal(kodaira_symbols(E), KodairaSymbol.(["IV*", "I0*"]))

    k, a = quadratic_field(2)
    K, t = rational_function_field(k, "t")

    E = elliptic_curve_from_j_invariant(1//(t^2 + t + a))
    @test issetequal(conductor(E), [(t^2 + t + 1//1728*(1728*a - 1), 2), (t^2 + t + a, 1), (1//t, 2)])

    E = elliptic_curve_from_j_invariant(t^2 - 2)
    @test issetequal(conductor(E), [(t^2 - 1730, 2), (t - a, 2), (t + a, 2), (1//t, 1)])

    K, t = rational_function_field(GF(2), "t")

    E = elliptic_curve_from_j_invariant(t^3//(t^2 + t + 1))
    @test issetequal(conductor(E), [(t, 5), (t^2 + t + 1, 1), (1//t, 1)])
  end
end

