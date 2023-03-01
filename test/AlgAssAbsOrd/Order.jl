@testset "AlgAssAbsOrd" begin
  Qx, x = FlintQQ["x"]

  A = matrix(QQ, 3, 3, [1,3^4,0,0,1,0,0,0,1]);
  B = matrix(QQ, 3, 3, [1,0,0,27,1,0,0,0,1]);
  C = matrix(QQ, 3, 3, [125,3^4,0,3*18,125-90,0,0,0,1]);
  D = matrix(QQ, 3, 3, [1,0,0,0,1,0,0,0,-1]);
  E = matrix(QQ, 3, 3, [1,0,3^4,0,1,0,0,0,1]);
  F = matrix(QQ, 3, 3, [1,0,0,0,1,3^5,0,0,1]);
  G = matrix(QQ, 3, 3, [1,0,0,0,1,0,3^3,0,1]);
  H = matrix(QQ, 3, 3, [1,0,0,0,1,0,0,9,1]);
  l = [A, B, C, D, E, F, G, H]
  A = matrix_algebra(QQ, 3)
  O = Order(A, l)
  @test discriminant(O) == -8862938119652501095929

  @testset "Quaternion Algebras" begin
    function sum_of_two_squares(a::ZZRingElem)
      for i=1:Int(isqrt(a))
        for j=1:Int(isqrt(a))
          if a==i^2+j^2
            return true
          end
        end
      end
      return false
    end

    for b in Hecke.squarefree_up_to(100)[2:end]
      K, a = number_field(x^2-b, check = false, cached = false)
      O = maximal_order(K);
      cocval = Matrix{nf_elem}(undef, 2, 2)
      G = NfToNfMor[hom(K,K,a),hom(K,K,-a)]
      cocval[1,1] = K(1)
      cocval[1,2] = K(1)
      cocval[2,1] = K(1)
      cocval[2,2] = K(-1)
      A = Hecke.CrossedProductAlgebra(K,G,cocval)
      if Hecke.is_split(A)
        A1 = Hecke.CrossedProductAlgebra(O, G, cocval)
        O1 = Order(A1, basis(A1))
        d = discriminant(O1)
        fac = factor(d)
        for p in keys(fac.fac)
          On = Hecke.pmaximal_overorder(O1, Int(p))
          @test valuation(discriminant(On), p) == 0
        end
        @test sum_of_two_squares(ZZRingElem(b))
      else
        @test !sum_of_two_squares(ZZRingElem(b))
      end
    end

    A = Hecke.quaternion_algebra2(4,36)
    @test Hecke.is_split(A)
    A = Hecke.quaternion_algebra2(-1,-1)
    O = Order(A, [A[i] for i=1:4])
    @test schur_index(A) == 2
  end

  @testset "Crossed Product Order" begin

    K, a = number_field(x^4-4*x^2+1)
    O = maximal_order(K)
    Autos = Vector{NfToNfMor}(undef, 4)
    Autos[1] = hom(K, K, a)
    Autos[2] = hom(K, K, -a)
    Autos[3] = hom(K, K, a^3 - 4*a)
    Autos[4] = hom(K, K, -a^3 + 4*a)
    MatCoc = [0 0 0 0; 0 1 0 1; 0 1 1 0; 0 0 1 1]
    Coc = Matrix{nf_elem}(undef, 4, 4)
    for i = 1:4
      for j = 1:4
        Coc[i, j] = K(-1)^MatCoc[i, j]
      end
    end
    A = Hecke.CrossedProductAlgebra(O, Autos, Coc)
    @test is_split(A)
    O1 = Order(A, basis(A))
    d = discriminant(O1)
    fac1 = factor(discriminant(O))
    fac2 = factor(d)
    @test Set(collect(keys(fac1.fac))) == Set(collect(keys(fac2.fac)))
    for p in keys(fac1.fac)
      O3 = Hecke.pmaximal_overorder(O1, Int(p))
      @test valuation(discriminant(O3), p) == 0
    end
  end

  @testset "Any order" begin
    A = AlgAss(x^2 - QQFieldElem(1, 5))

    O = any_order(A)

    # Test whether O is indeed an order
    @test one(A) in O

    for b in basis(O, copy = false)
      @test is_integral(elem_in_algebra(b, copy = false))
      for c in basis(O, copy = false)
        @test elem_in_algebra(b*c, copy = false) in O
      end
    end

    # Some more miscellaneous tests
    b = rand(O, 10)
    @test elem_in_algebra(b) in O

    b = A(QQFieldElem[ QQFieldElem(1), QQFieldElem(1, 3) ])
    @test denominator(b, O)*b in O
  end

  @testset "Maximal Order" begin
    A = AlgAss(x^2 + 10x + 7)
    AA = deepcopy(A) # avoid caching
    O1 = maximal_order(A)
    O2 = Hecke.maximal_order_via_decomposition(AA)
    @test discriminant(O1) == discriminant(O2)

    QG = group_algebra(FlintQQ, small_group(2, 1))
    O = maximal_order(QG)
    @test isone(abs(discriminant(O)))

    M = matrix_algebra(FlintQQ, 3)
    O = maximal_order(M)
    @test isone(abs(discriminant(O)))

    # large one, triggers splitting
    Qx, x = QQ["x"]
    f = prod(x - i for i in 1:30)
    A = AlgAss(f)
    R = any_order(A)
    M = MaximalOrder(R)
    @test isone(abs(discriminant(M)))

    G = small_group(6, 1)
    QG = QQ[G]
    ZG = Order(QG, basis(QG))
    @test !ismaximal(ZG)

    # This is not ZG, so we need to also make it maximal at 5
    O = Order(QG, [one(QG), 5 * QG(gens(G)[1]), 5 * QG(gens(G)[2])])
    @test !ismaximal(O)
    @test discriminant(maximal_order(ZG)) == -1

    S = overorders(ZG)
    for R in S
      _ = maximal_order(R)
    end
    for R in S
      _ = maximal_order(R)
    end
    @test count(ismaximal, S) == 2

    # Trigger multiple maximal orders in the AlgAss case
    A, AtoQG = AlgAss(QG)
    ZG = Order(A, basis(A))
    @test !ismaximal(ZG)

    # This is not ZG, so we need to also make it maximal at 5
    O = Order(A, [one(A), 5 * (AtoQG\(QG(gens(G)[1]))), (5 * (AtoQG\(QG(gens(G)[2]))))])
    @test !ismaximal(O)
    @test discriminant(maximal_order(ZG)) == -1

    S = overorders(ZG)
    for R in S
      _ = maximal_order(R)
    end
    for R in S
      _ = maximal_order(R)
    end
    @test count(ismaximal, S) == 2

    A = matrix_algebra(QQ, 6)
    O = Order(A, basis(A), isbasis = true)
    M = maximal_order(O)
    @test is_unit(discriminant(M))

    G = small_group(10, 1)
    QG = QQ[G]
    ZG = Order(QG, basis(QG))
    # there are exactly two maximal overorders and we hope to find them all
    @test length(unique([Hecke.new_maximal_order(ZG, false) for i in 1:20])) == 2
  end

  @testset "rand" begin
    Qx, x = FlintQQ["x"]
    A = AlgAss(x^2 - QQFieldElem(1, 5))
    O = any_order(A)

    for n = (3, ZZRingElem(3), big(3), 1:3, big(1):3)
      @test rand(rng, O, n) isa elem_type(O)
      @test rand(O, n) isa elem_type(O)
      m = make(O, n)
      @test Random.gentype(m) == elem_type(O)
      @test rand(make(O, n), 3) isa Vector{elem_type(O)}

      @test reproducible(m)
    end
  end

  @testset "index" begin
    G = small_group(2, 1)
    QG = QQ[G]
    R = Order(QG, basis(QG))
    M = maximal_order(R)
    @test (@inferred index(R, M)) == 2
  end
end
