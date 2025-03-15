@testset "Ramification" begin
  K, a = Hecke.rationals_as_number_field()
  Q = Hecke.quaternion_algebra2(K, -1, -1)
  @test (@inferred Hecke.ramified_infinite_places(Q)) == real_places(K)

  Q = Hecke.quaternion_algebra2(QQ, -1, -1)
  QQQ = direct_product(Q, Q)[1]
  C, = center(QQQ)
  flds = first.(Hecke.components(Hecke.Field, C))
  @test (@inferred Hecke.ramified_infinite_places_of_center(QQQ)) == real_places.(flds)

  Q = matrix_algebra(QQ, 3)
  @test (@inferred schur_index(Q, inf)) == 1
  @test is_eichler(Q)

  # Test (-1, -1/QQ)
  Q = Hecke.QuaternionAlgebra(QQ, QQ(-1), QQ(-1))
  @test !is_split(Q, 2)
  @test schur_index(Q, 2) == 2
  @test schur_index(Q, ZZ(2)) == 2
  @test schur_index(Q, inf) == 2
  @test !is_split(Q, inf)
  @test schur_index(Q, 3) == 1
  @test schur_index(Q, ZZ(3)) == 1
  @test is_split(Q, ZZ(3))
  @test schur_index(Q) == 2
  @test !is_split(Q)
  @test !is_eichler(Q)

  Q, = StructureConstantAlgebra(Q)
  @test !is_split(Q, 2)
  @test schur_index(Q, 2) == 2
  @test schur_index(Q, ZZ(2)) == 2
  @test schur_index(Q, inf) == 2
  @test !is_split(Q, inf)
  @test schur_index(Q, 3) == 1
  @test schur_index(Q, ZZ(3)) == 1
  @test is_split(Q, ZZ(3))
  @test schur_index(Q) == 2
  @test !is_split(Q)
  @test !is_eichler(Q)

  # Test Mat_2((-1, -1)/QQ)
  Q = Hecke.QuaternionAlgebra(QQ, QQ(-1), QQ(-1))
  A = matrix_algebra(QQ, Q, 2)
  @test !is_split(A, 2)
  @test schur_index(A, 2) == 2
  @test schur_index(A, ZZ(2)) == 2
  @test schur_index(A, inf) == 2
  @test !is_split(A, inf)
  @test schur_index(A, 3) == 1
  @test schur_index(A, ZZ(3)) == 1
  @test is_split(A, ZZ(3))
  @test schur_index(A) == 2
  @test !is_split(A)
  @test is_eichler(A)

  K, = Hecke.rationals_as_number_field()
  OK = maximal_order(K)
  # Test (-1, -1; QQ)
  Q = Hecke.QuaternionAlgebra(K, K(-1), K(-1))
  p2 = prime_decomposition(OK, 2)[1][1]
  p3 = prime_decomposition(OK, 3)[1][1]
  rlp = real_places(K)[1]
  @test !is_split(Q, p2)
  @test schur_index(Q, p2) == 2
  @test schur_index(Q, rlp) == 2
  @test !is_split(Q, rlp)
  @test schur_index(Q, p3) == 1
  @test is_split(Q, p3)
  @test schur_index(Q) == 2
  @test !is_split(Q)
  @test !is_eichler(Q)

  Q, = StructureConstantAlgebra(Q)
  @test !is_split(Q, p2)
  @test schur_index(Q, p2) == 2
  @test schur_index(Q, rlp) == 2
  @test !is_split(Q, rlp)
  @test schur_index(Q, p3) == 1
  @test is_split(Q, p3)
  @test schur_index(Q) == 2
  @test !is_split(Q)
  @test !is_eichler(Q)

  A = Hecke.QuaternionAlgebra(QQ, QQ(1), QQ(1))
  @test schur_index(A) == 1
  @test is_split(A)
  @test is_eichler(A)
  A = Hecke.QuaternionAlgebra(K, K(1), K(1))
  @test schur_index(A) == 1
  @test is_split(A)
  @test is_eichler(A)

  K, = quadratic_field(5)
  A = Hecke.QuaternionAlgebra(K, K(1), K(1))
  @test schur_index(A) == 1
  @test is_split(A)
  @test is_eichler(A)

  K, = quadratic_field(5)
  A = Hecke.QuaternionAlgebra(K, K(-1), K(-1))
  @test schur_index(A) == 2
  @test !is_split(A)
  @test !is_eichler(A)

  A = matrix_algebra(K, 3)
  @test is_eichler(A)

  Qx, x = QQ["x"]
  K, a = number_field(x^3 - 2, "a")
  A = Hecke.QuaternionAlgebra(K, K(-1), K(-1))
  @test schur_index(A) == 2
  @test !is_split(A)
  @test is_eichler(A)
  p = complex_places(K)
  @test is_split(A, p[1])

  A = matrix_algebra(QQ, 2)
  @test schur_index(A) == 1

  @testset "ignore complex embeddings" begin
    # The schur index of QQ[i]^{2×2} is 1
    # Test this for various ways of writing QQ[i]^{2×2}

    QQi, i = cyclotomic_field(4, :i)
    QQi2x2 = matrix_algebra(QQi, 2)
    QQi2x2i = StructureConstantAlgebra(QQi, i .* multiplication_table(QQi2x2))
    QQi2x2ip1 = StructureConstantAlgebra(QQi, (i+1) .* multiplication_table(QQi2x2))

    @test schur_index(QQi2x2) == 1 # harmless
    @test schur_index(QQi2x2i) == 1
    @test schur_index(QQi2x2ip1) == 1

    # A usecase where QQi2x2i can pop up
    X = zero_matrix(QQ, 4, 4)
    Y = zero_matrix(QQ, 4, 4)
    IM = QQ[0 -1;1 0]
    X[1:2,1:2] = Y[1:2,3:4] = Y[3:4,1:2] = IM
    QQIM2x2 = matrix_algebra(QQ, [X, Y])
    QQIM2x2overQQi = Hecke._as_algebra_over_center(StructureConstantAlgebra(QQIM2x2)[1])[1]

    @test schur_index(QQIM2x2overQQi) == 1
  end

  # Eichler
  QG = QQ[small_group(6, 1)]
  @test is_eichler(QG)
  QG = QQ[small_group(8, 4)]
  @test !is_eichler(QG)

  # bug in positive root calculation
  m = Array{Rational{Int}, 3}(undef, 4, 4, 4)
  m[1, :, :] = [346//83 0 0 0; 0 346//83 0 0; 6//205 0 0 0; 0 2//83 0 0]
  m[2, :, :] = [-12 0 0 0; 0 -12 0 0; 0 0 0 0; 0 0 0 0]
  m[3, :, :] = [0 0 346//83 0; 0 0 0 1038//205; 0 0 6//205 0; 0 0 0 6//205]
  m[4, :, :] = [0 0 -820//83 0; 0 0 0 -12; 0 0 0 0; 0 0 0 0]
  K, = rationals_as_number_field()
  A = StructureConstantAlgebra(K, K.(m))
  @test is_split(A, real_places(K)[1])
  @test is_split(A)

  # another bug in positive root calculation
  let
    K, = rationals_as_number_field()
    Ky, y = K["y"]
    f = y^36 - 6144*y^35 - 41943040*y^34 + 331786223616*y^33 + 447501232504832*y^32 - 6843782583742889984*y^31 + 3157275540365850443776*y^30 + 68762083209159724603801600*y^29 - 97559633622127041169877630976*y^28 - 361970882121956800274885400068096*y^27 + 802780148957408543309960012219023360*y^26 + 977059812317683872145272580438950412288*y^25 - 3409117522231051343013324572504138912366592*y^24 - 900638526471366017613972779255698906278789120*y^23 + 8534080184547490570450694866685297882736304848896*y^22 - 2070188970340273835050361230537591360407130911801344*y^21 - 13175274896840567577610149576325406847631516973672693760*y^20 + 7761412759855105814997742215630143245049982509946673037312*y^19 + 12544181524621926439246237141237904991509788192096159086411776*y^18 - 11510050506966931427495529309581497732543225385436898025432678400*y^17 - 6889545043385424653826243622611199685423334812911473873716990967808*y^16 + 9859663121554864996620009426414028733184181500916257055984614767591424*y^15 + 1496188261764983914895632992432252168212416686885579109800462984677425152*y^14 - 5252212740019725417552692821649733983497628398260721799054047309937894227968*y^13 + 575336918926574382480431079259650304471405851900069812529642712221683437010944*y^12 + 1739436793076026240631276963304353127593557629734079955813277531545449707115380736*y^11 - 531718315906559105230796775298759951053386449014483460834265580882593162524752871424*y^10 - 333282254698712661046141586661468326428614701913953424890384635081001368453923007889408*y^9 + 174775242309231818566942702106607290184375760036011750997421259399050741056432215676682240*y^8 + 26792294715104435772836907854413679118731874211905513581670115827165181582556210540092325888*y^7 - 29786049304956939174938779967344029815434833719281736340864304685572101960464450151990182281216*y^6 + 1818926460276399992039510671660009222591365569819337124408027619161108985235076718378928652156928*y^5 + 2480948942222137060701817711715934781111041302717252192293488827485508211494213998851670463976833024*y^4 - 511816669599224790303165521145523399492641646829011710123630321899929001812653966034302083423394594816*y^3 - 58233363296622909474493499294779551231162782928100887907399716625058588650684184579902814825061785010176*y^2 + 27521983391880858139329850743625043289558779870019373484851066072643074513061817696840222637321508238655488*y - 2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976
    P = real_embeddings(K)[1]
    @test Hecke.n_positive_roots(f, P) == 21
  end

  # Schur index over center
  let
    K, = quadratic_field(2)
    A = Hecke.QuaternionAlgebra(K, K(-1), K(-1))
    @test schur_index(A) == 2
    AA, = restrict_scalars(A, QQ)
    @test schur_index_over_center(AA) == 2
    c = infinite_places(K)[1]
    @test schur_index_over_center(AA, c) == 2

    K, = quadratic_field(-1)
    A = Hecke.QuaternionAlgebra(K, K(-1), K(-1))
    @test schur_index(A) == 1
    AA, = restrict_scalars(A, QQ)
    @test schur_index_over_center(AA) == 1
    c = infinite_places(K)[1]
    @test schur_index_over_center(AA, c) == 1
  end
end
