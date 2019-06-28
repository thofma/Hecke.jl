@testset "AlgAssAbsOrd" begin
  Qx, x = FlintQQ["x"]

  @testset "Quaternion Algebras" begin
    function sum_of_two_squares(a::fmpz)
      for i=1:Int(root(a,2))
        for j=1:Int(root(a,2))
          if a==i^2+j^2
            return true
          end
        end
      end
      return false
    end

    for b in Hecke.squarefree_up_to(100)[2:end]
      K,a=NumberField(x^2-b)
      O=maximal_order(K);
      cocval=Array{nf_elem, 2}(undef, 2, 2)
      G=[Hecke.NfToNfMor(K,K,a),Hecke.NfToNfMor(K,K,-a)]
      cocval[1,1]=K(1)
      cocval[1,2]=K(1)
      cocval[2,1]=K(1)
      cocval[2,2]=K(-1)
      A = Hecke.CrossedProductAlgebra(K,G,cocval)
      if Hecke.issplit(A)
        A1 = Hecke.CrossedProductAlgebra(O,G,cocval)
        O1 = Order(A1, basis(A1))
        d = discriminant(O1)
        fac = factor(d)
        for p in keys(fac.fac)
          On = Hecke.pmaximal_overorder(O1, Int(p))
          @test valuation(discriminant(On), p) == 0
        end
        @test sum_of_two_squares(fmpz(b))
      else
        @test !sum_of_two_squares(fmpz(b))
      end
    end

    A=Hecke.quaternion_algebra(4,36)
    @test Hecke.issplit(A)
    A=Hecke.quaternion_algebra(-1,-1)
    O= Order(A, [A[i] for i=1:4])
    @test Hecke.schur_index_at_real_plc(O)==2

  end

  @testset "Crossed Product Order" begin

    K, a = NumberField(x^4-4*x^2+1)
    O = maximal_order(K)
    Autos = Array{NfToNfMor, 1}(undef, 4)
    Autos[1] = NfToNfMor(K, K, a)
    Autos[2] = NfToNfMor(K, K, -a)
    Autos[3] = NfToNfMor(K, K, a^3 - 4*a)
    Autos[4] = NfToNfMor(K, K, -a^3 + 4*a)
    MatCoc = [0 0 0 0; 0 1 0 1; 0 1 1 0; 0 0 1 1]
    Coc = Array{nf_elem, 2}(undef, 4, 4)
    for i = 1:4
      for j = 1:4
        Coc[i, j] = K(-1)^MatCoc[i, j]
      end
    end
    A = Hecke.CrossedProductAlgebra(O, Autos, Coc)
    @test Hecke.issplit(A)
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
    A = AlgAss(x^2 - fmpq(1, 5))

    O = any_order(A)

    # Test whether O is indeed an order
    @test one(A) in O

    for b in basis(O, copy = false)
      @test isintegral(elem_in_algebra(b, copy = false))
      for c in basis(O, copy = false)
        @test elem_in_algebra(b*c, copy = false) in O
      end
    end

    # Some more miscellaneous tests
    b = rand(O, 10)
    @test elem_in_algebra(b) in O

    b = A([ fmpq(1), fmpq(1, 3) ])
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
  end
end
