function _test_normal_form(G, D, B, p, prec = 0)
  return _test_normal_form_isometry(G, D, p) &&
         _test_normal_form_congruence(G, D, B, p, prec) &&
         Hecke._ispadic_normal_form(D, p)
end

function _test_normal_form_isometry(M, D, p)
  return islocally_isometric(Zlattice(gram = M), Zlattice(gram = D), p)
end

function _test_normal_form_congruence(G, D, B, p, prec = 0)
  X = denominator(G) * B * G * transpose(B) - denominator(G) * D
  v = valuation(reduce(gcd, Hecke._eltseq(X)), p)
  if prec == 0
    return v >= 1
  else
    return v >= prec
  end
end

@testset "helpers" begin
  R = ResidueRing(ZZ, 9)
  @test Hecke._issquare(R(1), ZZ(3))
  R = ResidueRing(ZZ, ZZ(9))
  @test Hecke._issquare(R(1), ZZ(3))
end

@testset "NormalForm" begin
  for R in [ZZ, GF(3)]
    W = R[1;]
    V = R[0 1; 1 0]

    L = diagonal_matrix([W, V])
    @test (@inferred diagonal_matrix(Hecke.collect_small_blocks(L))) == L

    L = diagonal_matrix([W, W])
    @test diagonal_matrix(Hecke.collect_small_blocks(L)) == L

    L = diagonal_matrix([W, V, W])
    @test diagonal_matrix(Hecke.collect_small_blocks(L)) == L

    L = diagonal_matrix([W])
    @test diagonal_matrix(Hecke.collect_small_blocks(L)) == L

    L = diagonal_matrix([V])
    @test diagonal_matrix(Hecke.collect_small_blocks(L)) == L

    L = diagonal_matrix([V, W, W, V, V, W, W])
    @test diagonal_matrix(Hecke.collect_small_blocks(L)) == L

    L = zero_matrix(ZZ, 0, 0)
    @test Hecke.collect_small_blocks(L) == typeof(L)[]
  end

  G1 = matrix(FlintQQ, 4, 4, [2, 0, 0, 1,
                              0, 2, 0, 1,
                              0, 0, 4, 2,
                              1, 1, 2, 6])
  G2 = matrix(FlintQQ, 4, 4, [2, 1, 1, 0,
                              1, 2, 0, 0,
                              1, 0, 2, 0,
                              0, 0, 0, 16])

  D1, U1 = @inferred Hecke.padic_normal_form(G1, 2, prec = 30)
  @test _test_normal_form(G1, D1, U1, 2, 30)

  D2, U2 = @inferred Hecke.padic_normal_form(G2, 2, prec = 30)
  @test _test_normal_form(G2, D2, U2, 2, 30)

  DD = matrix(base_ring(D1), 4, 4, [2, 1, 0, 0,
                                    1, 2, 0, 0,
                                    0, 0, 4 + 8, 0,
                                    0, 0, 0, 16])
  @test DD == D1
  DD = matrix(base_ring(D2), 4, 4, [2, 1, 0, 0,
                                    1, 2, 0, 0,
                                    0, 0, 4 + 8, 0,
                                    0, 0, 0, 16])
  @test DD == D2

  D4 = matrix(FlintQQ,  4,  4,  [2, -1, -1, -1,
                                 -1, 2, 0, 0,
                                 -1, 0, 2, 0,
                                 -1, 0, 0, 2])

  D, B = Hecke.padic_normal_form(D4, 2)
  @test _test_normal_form(D4, D, B, 2)

  @test D == matrix(base_ring(D), 4, 4, [2, 1, 0, 0,
                                         1, 2, 0, 0,
                                         0, 0, 4, 2,
                                         0, 0, 2, 4])
  A4 = matrix(FlintQQ, 4, 4, [2, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2, -1, 0, 0, -1, 2])
  D, B = Hecke.padic_normal_form(A4, 2)
  K = base_ring(D)
  @test D == matrix(K, 4, 4, [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 2])
  @test _test_normal_form(A4, D, B, 2)

  A4_extended = matrix(FlintQQ, 5, 5, [2, -1, 0, 0, -1,
                                       -1, 2, -1, 0, 0,
                                       0, -1, 2, -1, 0,
                                       0, 0, -1, 2, -1,
                                       -1, 0, 0, -1, 2])

  D, B = Hecke.padic_normal_form(A4_extended, 5)
  K = base_ring(D)
  @test D == matrix(K, 5, 5, [1, 0, 0, 0, 0,
                              0, 1, 0, 0, 0,
                              0, 0, 1, 0, 0,
                              0, 0, 0, 5, 0,
                              0, 0, 0, 0, 0])
  # isometry only works for non-degenerate lattices
  #@test _test_normal_form_isometry(A4_extended, D)
  @test  _test_normal_form_congruence(A4_extended, D, B, 5)
  #@test Hecke._ispadic_normal_form(D, 5)

  A4dual = inv(A4)
  D, B = Hecke.padic_normal_form(A4dual, 5)
  K = base_ring(D)
  @test D == matrix(K, 4, 4, [inv(K(5)), 0, 0, 0,
                              0, 1, 0, 0,
                              0, 0, 1, 0,
                              0, 0, 0, 1])
  @test _test_normal_form(A4dual, D, B, 5)

  # Corner cases
  Z = matrix(FlintQQ, 0, 0, [])
  B, D = Hecke.padic_normal_form(Z, 2)
  @test iszero(B)
  @test iszero(D)

  Z = zero_matrix(FlintQQ, 10, 10)
  B, D = Hecke.padic_normal_form(Z, 3)
  @test iszero(B)
  @test iszero(D)

  # 2-adic cases

  M = matrix(FlintQQ, 3, 3, fmpq[2, 1, 0, 1, 3, 1, 0, 1, 2])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 3, 3, fmpq[400, 0, 0, 0, 160, 0, 0, 0, 80])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 6, 6, fmpq[12544, 3584, 0, 896, 8064, 0, 3584, 1152, 896, 512, 2304, 1152, 0, 896, 18816, 5376, 3584, 8064, 896, 512, 5376, 1728, 1600, 2816, 8064, 2304, 3584, 1600, 6272, 0, 0, 1152, 8064, 2816, 0, 12544])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 4, 4, fmpq[4, 0, 2, 1, 0, 4, 1, 2, 2, 1, 5, 1, 1, 2, 1, 5])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 3, 3, fmpq[1, 0, 0, 0, 1, 0, 0, 0, 1])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 6, 6, fmpq[2, 1, 0, 1, 1, 1, 1, 2, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 3, 0, 0, 1, 0, 0, 0, 3, 0, 1, 0, 0, 0, 0, 3])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 10, 10, fmpq[3, 1, 0, 0, 0, -1, 1, -1, 0, 1, 1, 3, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 3, 1, 0, 1, -1, -1, -1, -1, 0, 1, 1, 3, -1, 0, -1, -1, 1, -1, 0, 0, 0, -1, 3, 1, 1, 2, 1, 2, -1, 0, 1, 0, 1, 3, 0, 1, 0, -1, 1, 1, -1, -1, 1, 0, 4, 1, -1, 2, -1, 0, -1, -1, 2, 1, 1, 4, 1, 2, 0, 0, -1, 1, 1, 0, -1, 1, 4, 1, 1, 1, -1, -1, 2, -1, 2, 2, 1, 5])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 6, 6, fmpq[4, 1, -1, -1, 1, -1, 1, 4, 0, 1, 2, 1, -1, 0, 4, -1, 2, -1, -1, 1, -1, 4, -1, 0, 1, 2, 2, -1, 4, -1, -1, 1, -1, 0, -1, 4])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 5, 5, fmpq[5, -1, -1, -1, -1, -1, 5, -1, -1, -1, -1, -1, 5, -1, -1, -1, -1, -1, 5, -1, -1, -1, -1, -1, 5])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 3, 3, fmpq[2, 1, 0, 1, 4, 1, 0, 1, 4])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 7, 7, fmpq[8, -4, 3, 4, 0, 1, 1, -4, 8, 1, 0, 4, 1, 1, 3, 1, 8, 4, 0, 1, 1, 4, 0, 4, 8, 3, 0, 4, 0, 4, 0, 3, 8, 4, 0, 1, 1, 1, 0, 4, 8, -4, 1, 1, 1, 4, 0, -4, 8])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)

  M = matrix(FlintQQ, 24, 24, fmpq[2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18014398509481985//18014398509481984, -1//18014398509481984, -1//18014398509481984, -1//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1//36028797018963968, -1//18014398509481984, -1//18014398509481984, -1//18014398509481984, 0, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -36028797018963969//36028797018963968, -36028797018963969//36028797018963968, -36028797018963969//36028797018963968, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18014398509481985//18014398509481984, 0, 0, -18014398509481983//18014398509481984, 0, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 0, 2, 0, -1, -1, 1, 0, 0, 0, 0, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, 2, 1, -1, 0, 0, 0, 0, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 2, 0, 0, 0, 0, 0, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 2, 0, 0, 0, 0, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, -1, -1, 18014398509481983//18014398509481984, 0, -36028797018963969//36028797018963968, -18014398509481983//18014398509481984, 0, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 18014398509481983//18014398509481984, 0, 0, -18014398509481983//18014398509481984, 0, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 2, 1, -18014398509481983//18014398509481984, 0, 36028797018963969//36028797018963968, 18014398509481983//18014398509481984, 0, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 2, 0, 0, 36028797018963969//36028797018963968, 0, 0, 0, 0, 0, 1, 18014398509481985//18014398509481984, 1//36028797018963968, 0, 0, 0, 0, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 5192296858534827340300120177508381//1298074214633706907132624082305024, 649037107316853399523116512706557//324518553658426726783156020576256, -162259276829213336369980246065155//162259276829213363391578010288128, 18014398509481979//324518553658426726783156020576256, 54043195528445949//649037107316853453566312041152512, -1298074214633706708974240478003207//649037107316853453566312041152512, 324518553658426690754359001612289//162259276829213363391578010288128, -324518553658426690754359001612289//162259276829213363391578010288128, 1, -1//18014398509481984, -1//18014398509481984, -36028797018963969//36028797018963968, 18014398509481985//18014398509481984, 0, 0, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 0, 0, 0, 649037107316853399523116512706557//324518553658426726783156020576256, 2596148429267413814265248164610069//649037107316853453566312041152512, 288230376151711757//1298074214633706907132624082305024, 2596148429267413814265248164610069//1298074214633706907132624082305024, -649037107316853435551913531670527//324518553658426726783156020576256, -1298074214633706817060631534895105//649037107316853453566312041152512, 324518553658426690754359001612289//324518553658426726783156020576256, 54043195528445949//649037107316853453566312041152512, 1, -1//18014398509481984, -1//18014398509481984, -36028797018963969//36028797018963968, 0, 0, 0, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -36028797018963969//36028797018963968, 0, 36028797018963969//36028797018963968, 36028797018963969//36028797018963968, -162259276829213336369980246065155//162259276829213363391578010288128, 288230376151711757//1298074214633706907132624082305024, 2596148429267413814265248164610069//649037107316853453566312041152512, 1298074214633707051247812158160913//1298074214633706907132624082305024, -54043195528445949//649037107316853453566312041152512, 649037107316853327465522474778629//649037107316853453566312041152512, -324518553658426690754359001612289//324518553658426726783156020576256, 324518553658426690754359001612289//324518553658426726783156020576256, 1, -1//18014398509481984, -1//18014398509481984, -36028797018963969//36028797018963968, 0, 0, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, 18014398509481979//324518553658426726783156020576256, 2596148429267413814265248164610069//1298074214633706907132624082305024, 1298074214633707051247812158160913//1298074214633706907132624082305024, 5192296858534827340300120177508381//1298074214633706907132624082305024, -1298074214633706817060631534895105//649037107316853453566312041152512, -54043195528445949//649037107316853453566312041152512, 0, 0, 0, 18014398509481983//18014398509481984, 0, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 0, 0, 0, 54043195528445949//649037107316853453566312041152512, -649037107316853435551913531670527//324518553658426726783156020576256, -54043195528445949//649037107316853453566312041152512, -1298074214633706817060631534895105//649037107316853453566312041152512, 324518553658426690754359001612289//81129638414606681695789005144064, 324518553658426690754359001612289//162259276829213363391578010288128, -324518553658426690754359001612289//162259276829213363391578010288128, 324518553658426690754359001612289//324518553658426726783156020576256, 0, 18014398509481983//18014398509481984, 0, 18014398509481983//18014398509481984, 0, 0, 0, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, -1298074214633706708974240478003207//649037107316853453566312041152512, -1298074214633706817060631534895105//649037107316853453566312041152512, 649037107316853327465522474778629//649037107316853453566312041152512, -54043195528445949//649037107316853453566312041152512, 324518553658426690754359001612289//162259276829213363391578010288128, 324518553658426690754359001612289//81129638414606681695789005144064, -324518553658426690754359001612289//162259276829213363391578010288128, 324518553658426690754359001612289//162259276829213363391578010288128, 0, 0, 0, 0, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 324518553658426690754359001612289//162259276829213363391578010288128, 324518553658426690754359001612289//324518553658426726783156020576256, -324518553658426690754359001612289//324518553658426726783156020576256, 0, -324518553658426690754359001612289//162259276829213363391578010288128, -324518553658426690754359001612289//162259276829213363391578010288128, 324518553658426690754359001612289//81129638414606681695789005144064, -324518553658426690754359001612289//162259276829213363391578010288128, 0, 0, 0, 0, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 0, 18014398509481983//18014398509481984, 18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, -18014398509481983//18014398509481984, 18014398509481983//18014398509481984, 0, -324518553658426690754359001612289//162259276829213363391578010288128, 54043195528445949//649037107316853453566312041152512, 324518553658426690754359001612289//324518553658426726783156020576256, 0, 324518553658426690754359001612289//324518553658426726783156020576256, 324518553658426690754359001612289//162259276829213363391578010288128, -324518553658426690754359001612289//162259276829213363391578010288128, 324518553658426690754359001612289//81129638414606681695789005144064])
  D, B = Hecke.padic_normal_form(M, 2)
  @test _test_normal_form(M, D, B, 2)


  # non-dyadic tests
  M = matrix(FlintQQ, 2, 2, fmpq[2, -1, -1, 2])
  D, B = Hecke.padic_normal_form(M, 3)
  @test _test_normal_form(M, D, B, 3)

  M = matrix(FlintQQ, 2, 2, fmpq[2, -1, -1, 2])
  D, B = Hecke.padic_normal_form(M, 3)
  @test _test_normal_form(M, D, B, 3)

  M = matrix(FlintQQ, 3, 3, fmpq[2, -1, 0, -1, 2, -1, 0, -1, 2])
  D, B = Hecke.padic_normal_form(M, 3)
  @test _test_normal_form(M, D, B, 3)

  M = matrix(FlintQQ, 3, 3, fmpq[3, -1, -1, -1, 3, -1, -1, -1, 3])
  D, B = Hecke.padic_normal_form(M, 3)
  @test _test_normal_form(M, D, B, 3)

  R = ResidueRing(FlintZZ, fmpz(2)^30)
  U = matrix(R,2,2,[0,1,1,0])
  V = matrix(R,2,2,[2,1,1,2])
  W1 = matrix(R,1,1,[1])
  W3 = matrix(R,1,1,[3])
  W5 = matrix(R,1,1,[5])
  W7 = matrix(R,1,1,[7])

  p = fmpz(2)
   G = diagonal_matrix(W1,W1)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [5, 0,
                                         0, 5])

   G = diagonal_matrix(W1,W3)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [5, 0,
                                         0, 7])

   G = diagonal_matrix(W1,W5)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [5, 0,
                                        0, 1])
   G = diagonal_matrix(W1,W7)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [5, 0,
                                        0, 3])

   G = diagonal_matrix(W3,W3)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [7, 0,
                                        0, 7])

   G = diagonal_matrix(W3,W5)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [7, 0,
                                        0, 1])

   G = diagonal_matrix(W3,W7)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [7, 0,
                                        0, 3])

   G = diagonal_matrix(W5,W5)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [1, 0,
                                        0, 1])
   G = diagonal_matrix(W5,W7)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [1, 0,
                                        0, 3])
   G = diagonal_matrix(W7,W7)
   b = Hecke._relations(G,1, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [3, 0,
                                        0, 3])

   G = diagonal_matrix(V,V)
   b = Hecke._relations(G,3, p)
   @test b * G * transpose(b) == matrix(R, 4, 4, [0, 1, 0, 0,
                                        1, 0, 0, 0,
                                        0, 0, 0, 1,
                                        0, 0, 1, 0])
   G = diagonal_matrix(V,W1, W1)
   b = Hecke._relations(G,5, p)
   @test b * G * transpose(b) == matrix(R, 4, 4, [0, 1, 0, 0,
                                        1, 0, 0, 0,
                                        0, 0, 7, 0,
                                        0, 0, 0, 3])

   G = diagonal_matrix(V,W1, W5)
   b = Hecke._relations(G,5, p)
   @test b * G * transpose(b) == matrix(R, 4, 4, [0, 1, 0, 0,
                                        1, 0, 0, 0,
                                        0, 0, 3, 0,
                                        0, 0, 0, 3])
   G = diagonal_matrix(V,W3, W7)
   b = Hecke._relations(G,5, p)
   @test b * G * transpose(b) == matrix(R, 4, 4, [0, 1, 0, 0,
                                        1, 0, 0, 0,
                                        0, 0, 5, 0,
                                        0, 0, 0, 5])

   G = diagonal_matrix(W1,2*W1)
   b = Hecke._relations(G,6, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [3, 0,
                                        0, 6])

   G = diagonal_matrix(W1,2*W3)
   b = Hecke._relations(G,6, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [7, 0,
                                        0, 10])

   G = diagonal_matrix(W1,2*W5)
   b = Hecke._relations(G,6, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [3, 0,
                                        0, 14])

   G = diagonal_matrix(W1,2*W7)
   b = Hecke._relations(G,6, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [7, 0,
                                        0, 2])

   G = diagonal_matrix(W3,2*W5)
   b = Hecke._relations(G,6, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [5, 0,
                                        0, 6])

   G = diagonal_matrix(W3,2*W3)
   b = Hecke._relations(G,6, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [1, 0,
                                        0, 2])

   G = diagonal_matrix(2*W5, 4*W7)
   b = Hecke._relations(G,6, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [6, 0,
                                        0, 4])

   G = diagonal_matrix(W3, 2*V)
   b = Hecke._relations(G, 7, p)
   @test b * G * transpose(b) == matrix(R, 3, 3, [7, 0, 0,
                                        0, 0, 2,
                                        0, 2, 0])

   G = diagonal_matrix(W7, 2*V)
   b = Hecke._relations(G, 7, p)
   @test b * G * transpose(b) == matrix(R, 3, 3, [3, 0, 0,
                                        0, 0, 2,
                                        0, 2, 0])

   G = diagonal_matrix(U, 2*W1)
   b = Hecke._relations(G, 8, p)
   @test b * G * transpose(b) == matrix(R, 3, 3, [2, 1, 0,
                                        1, 2, 0,
                                        0, 0, 10])
   G = diagonal_matrix(U, 2*W5)
   b = Hecke._relations(G, 8, p)
   @test b * G * transpose(b) == matrix(R, 3, 3, [2, 1, 0,
                                        1, 2, 0,
                                        0, 0, 2])
   G = diagonal_matrix(V, 2*W1)
   b = Hecke._relations(G, 8, p)
   @test b * G * transpose(b) == matrix(R, 3, 3, [0, 1, 0,
                                        1, 0, 0,
                                        0, 0, 10])
   G = diagonal_matrix(V, 2*W7)
   b = Hecke._relations(G, 8, p)
   @test b * G * transpose(b) == matrix(R, 3, 3, [0, 1, 0,
                                        1, 0, 0,
                                        0, 0, 6])

   G = diagonal_matrix(W1, W5, 2*W5)
   b = Hecke._relations(G, 9, p)
   @test b * G * transpose(b) == matrix(R, 3, 3, [3, 0, 0,
                                        0, 3, 0,
                                        0, 0, 2])

   G = diagonal_matrix(W3, W3, 2*W5)
   b = Hecke._relations(G, 9, p)
   @test b * G * transpose(b) == matrix(R, 3, 3, [5, 0, 0,
                                        0, 1, 0,
                                        0, 0, 2])
   G = diagonal_matrix(W3, W3, 2*W1)
   b = Hecke._relations(G, 9, p)
   @test b * G * transpose(b) == matrix(R, 3, 3, [5, 0, 0,
                                        0, 1, 0,
                                        0, 0, 10])

   G = diagonal_matrix(W3, 4*W1)
   b = Hecke._relations(G, 10, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [7, 0,
                                        0, 20])

   G = diagonal_matrix(W5, 4*W5)
   b = Hecke._relations(G, 10, p)
   @test b * G * transpose(b) == matrix(R, 2, 2, [1, 0,
                                        0, 4])

   # _relations errors

   @test_throws ErrorException Hecke._relations(zero_matrix(R, 0, 0), 4, p)
   @test_throws ErrorException Hecke._relations(zero_matrix(R, 0, 0), 11, p)
   @test_throws ErrorException Hecke._relations(matrix(R, 4, 4, [1, 0, 0, 0,
                                                                 0, 1, 0, 0,
                                                                 0, 0, 1, 0,
                                                                 0, 0, 0, 3]), 5, p)
   @test_throws ErrorException Hecke._relations(matrix(R, 2, 2, [1, 0,
                                                                 0, 1]), 6, p)

   @test_throws ErrorException Hecke._normalize_twobytwo(matrix(R, 2, 2, [1, 2, 2, 1]), p)

   # _two_adic_normal_forms
   G = diagonal_matrix(2*W1,2*W1,4*V)
   D, B = Hecke._two_adic_normal_forms(G, p)
   @test D == matrix(R, 4, 4, [2, 0, 0, 0,
                               0, 10, 0, 0,
                               0, 0, 0, 4,
                               0, 0, 4, 0])
   @test B * G * transpose(B) == D

   G = diagonal_matrix(W1,2*V,2*W3,2*W5)
   D, B = Hecke._two_adic_normal_forms(G, p)
   @test D == matrix(R, 5, 5, [3, 0, 0, 0, 0,
                              0, 0, 2, 0, 0,
                              0, 2, 0, 0, 0,
                              0, 0, 0, 2, 0,
                              0, 0, 0, 0, 2])
   @test D == B * G * transpose(B)

   G = diagonal_matrix(U,2*V,2*W3,2*W5)
   D, B = Hecke._two_adic_normal_forms(G, p)
   @test D == matrix(R, 6, 6, [2, 1, 0, 0, 0, 0,
                               1, 2, 0, 0, 0, 0,
                               0, 0, 4, 2, 0, 0,
                               0, 0, 2, 4, 0, 0,
                               0, 0, 0, 0, 2, 0,
                               0, 0, 0, 0, 0, 6])
   @test D == B * G * transpose(B)

   @inferred Hecke._two_adic_normal_forms(G, p, partial = true)

   # test _ispadic_normal_form

   # not the right block structure
   @test !Hecke._ispadic_normal_form(matrix(FlintQQ, 3, 3, [1, 1, 1, 1, 1, 1, 1, 1, 1]), 2)
   @test !Hecke._ispadic_normal_form(matrix(FlintQQ, 3, 3, [1, 1, 1, 1, 1, 1, 1, 1, 1]), 3)
   @test !Hecke._ispadic_normal_form(matrix(FlintQQ, 2, 2, [1, 1, 1, 1]), 3)

   @test !Hecke._ispadic_normal_form(matrix(FlintQQ, 2, 2, [2, 0, 0, 1]), 3)
   @test !Hecke._ispadic_normal_form(matrix(FlintQQ, 2, 2, [1, 0, 0, 3]), 5)
   @test !Hecke._ispadic_normal_form(matrix(FlintQQ, 2, 2, [1, 0, 0, 4]), 5)
   @test !Hecke._ispadic_normal_form(matrix(FlintQQ, 2, 2, [1, 1, 1, 1]), 2)
   @test !Hecke._ispadic_normal_form(matrix(FlintQQ, 1, 1, [9]), 2)

 end
