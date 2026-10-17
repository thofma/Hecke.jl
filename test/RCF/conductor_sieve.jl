@testset "RCF" begin

  @testset "abelian extensions && related examples" begin

    Qx, x = polynomial_ring(QQ, "x")
    K, a = number_field(x - 1, "a")
    l = Hecke.abelian_normal_extensions(K, Int[2,2], ZZRingElem(10)^4)
    @test length(l)==47
    l1 = collect(Hecke.C22_extensions(10^4))
    @test length(l1)==47

    @test length(abelian_extensions(QQ, [3], ZZRingElem(10)^3)) == 5
    @test length(abelian_extensions(K, [3], ZZRingElem(10)^3)) == 5

    @test length(abelian_extensions(QQ, [3], ZZRingElem(10)^8)) == 1592
    @test length(abelian_extensions(K, [3], ZZRingElem(10)^8)) == 1592

    K, a = number_field(x^2+1, "a")
    auts = small_generating_set(automorphism_list(K, copy = false))
    l = Hecke.abelian_normal_extensions(K, Int[2], ZZRingElem(10)^5)
    @test length(l) == 41
    l1 = typeof(l[1])[x for x in l if abs(discriminant(x, QQ)) < 5*10^3]
    lnn = Hecke.abelian_extensions(K, Int[2], 5*ZZRingElem(10)^3)
    ln = typeof(l[1])[x for x in lnn if is_normal(x)]
    @test length(ln) == length(l1)
    for x in l[1:5]
      L = number_field(x)
      autsL = Hecke.absolute_automorphism_group(x, auts)
      K, autos = Hecke._relative_to_absolute(L, autsL)
      @test length(autos)==2
      y = small_generating_set(closure(autos, *))
      @test length(y)==1 || length(y)==2
      if length(y) == 2
        @test y[1]*y[2] == y[2]*y[1]
      else
        @test y[1]^2 != id_hom(K)
      end
    end
  end

  @testset "Tame conductor prime restrictions" begin
    O = maximal_order(quadratic_field(21)[1])
    @test sort!(Hecke.tame_conductors_degree_2(O, ZZ(200);
                                            unramified_outside = ZZ.([2, 3, 5]))) ==
          [(1, ZZ(1)), (3, ZZ(3)), (5, ZZ(25)), (15, ZZ(75))]
    @test sort!(Hecke.tame_conductors_degree_2(O, ZZ(200);
                                            unramified_outside = ZZ.([3, 7]))) ==
          [(1, ZZ(1)), (3, ZZ(3)), (7, ZZ(7)), (21, ZZ(21))]
    @test Hecke.tame_conductors_degree_2(O, ZZ(200);
                                       unramified_outside = ZZ.([2])) == [(1, ZZ(1))]

    # Check norms and prime support using ideal arithmetic.
    for K in (quadratic_field(21)[1], cyclotomic_field(15)[1])
      O = maximal_order(K)
      candidates = [(m, norm(radical(m*O))) for m in 1:2:200 if is_squarefree(ZZ(m))]
      for bound in (1, 24, 81, 200)
        for allowed in (ZZ.([2]), ZZ.([3, 5, 7, 11]), ZZ.([7, 11]))
          expected = [(m, n) for (m, n) in candidates if n <= bound &&
                      all(p -> p in allowed, prime_divisors(ZZ(m)))]
          @test sort!(Hecke.tame_conductors_degree_2(O, ZZ(bound);
                                                  unramified_outside = allowed)) == expected
        end
      end
    end
  end

end
