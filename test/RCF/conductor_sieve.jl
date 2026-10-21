@testset "RCF" begin

  @testset "Missing tame conductors" begin
    O = maximal_order(cyclotomic_field(15)[1])
    @test Hecke.tame_conductors_degree_2(O, ZZ(24)) == [(1, ZZ(1))]
    @test Hecke.tame_conductors_degree_2(O, ZZ(25)) == [(1, ZZ(1)), (5, ZZ(25))]

    # The old cutoff missed an actual quadratic extension with conductor norm 49.
    k, = quadratic_field(5)
    l, = cyclotomic_real_subfield(7)
    K, = compositum(k, l)
    bound = 49*abs(discriminant(maximal_order(K)))^2
    fields = Hecke.abelian_normal_extensions(K, [2], bound)
    @test length(fields) == 1
    @test norm(conductor(only(fields))[1]) == 49

    # Check norms using ideal arithmetic.
    for K in (quadratic_field(21)[1], cyclotomic_field(15)[1])
      O = maximal_order(K)
      candidates = [(m, norm(radical(m*O))) for m in 1:2:200 if is_squarefree(ZZ(m))]
      for bound in (1, 24, 25, 80, 81, 200)
        expected = [(m, n) for (m, n) in candidates if n <= bound]
        @test sort!(Hecke.tame_conductors_degree_2(O, ZZ(bound))) == expected
      end
    end
  end

  @testset "Tame choices at primes dividing the degree" begin
    # The tame C6 field of conductor 21 has discriminant -64827 and
    # ramification index 2 at 3. Q(zeta_21) has group C2 x C6 and also
    # needs the tame choice at 3 to complete the conductor from prime 7.
    O = maximal_order(rationals_as_number_field()[1])
    for (bound, expected) in ((64826, [-16807]), (64827, [-64827, -16807]))
      fields = abelian_extensions(QQ, [6], ZZ(bound); tame = true)
      number_fields = [number_field(AbsSimpleNumField, C) for C in fields]
      discs = [discriminant(maximal_order(K)) for K in number_fields]
      @test sort!(discs) == expected
      @test all(K -> signature(K) == (0, 3), number_fields)
    end
    for bound in (0, 1)
      @test isempty(abelian_extensions(QQ, [6], ZZ(bound); tame = true))
    end
    bound = ZZ(3)^6 * ZZ(7)^10
    fields = abelian_extensions(QQ, [2, 6], bound; tame = true)
    @test length(fields) == 1
    K = number_field(AbsSimpleNumField, only(fields))
    @test discriminant(maximal_order(K)) == bound
    @test is_isomorphic(K, cyclotomic_field(21)[1])
    @test isempty(abelian_extensions(QQ, [2, 6], bound - 1; tame = true))
    for allowed in (ZZ.([3, 7]), ZZ.([7]), ZZ.([3]))
      conds = Hecke.conductorsQQ(O, [6], ZZ(64827), true;
                                 unramified_outside = allowed)
      @test (21 in conds) == (3 in allowed && 7 in allowed)
      @test all(c -> is_squarefree(ZZ(c)), conds)
    end
    @test sort!(Hecke.conductorsQQ(O, [3], ZZ(1000), true)) ==
          [7, 13, 19, 31]
  end

  @testset "Tame normal extensions" begin
    # Over Q(sqrt(-31)), the unramified cubic extension times K(sqrt(-3))
    # is tame, with conductor (3) and relative discriminant norm 729.
    # Also test relative tameness over a wildly ramified base, and the
    # radical norms at the already ramified primes 2 and 3 of Q(zeta_12).
    K, = quadratic_field(-31)
    O = maximal_order(K)
    bound = ZZ(31)^6 * ZZ(729)
    fields = abelian_normal_extensions(K, [6], bound; tame = true)
    @test length(fields) == 1
    @test norm(conductor(only(fields))[1]) == 9
    @test norm(discriminant(only(fields))) == 729
    @test isempty(abelian_normal_extensions(K, [6], bound - 1; tame = true))
    @test isempty(Hecke.conductors(O, [6], ZZ(0), true))
    for gtype in ([2], [3], [6])
      @test isempty(abelian_normal_extensions(K, gtype, ZZ(0); tame = true))
    end
    for allowed in (ZZ.([3]), ZZ.([7]))
      conds = Hecke.conductors(O, [6], ZZ(729), true;
                              unramified_outside = allowed)
      @test any(c -> c[1] == 3 && isempty(c[2]), conds) == (3 in allowed)
      @test all(c -> isempty(c[2]), conds)
    end
    fields = abelian_normal_extensions(K, [3], ZZ(31)^3; tame = true)
    @test norm(conductor(only(fields))[1]) == 1
    @test isempty(abelian_normal_extensions(K, [3], ZZ(31)^3 - 1; tame = true))

    K, = cyclotomic_real_subfield(9)
    fields = abelian_normal_extensions(K, [2], ZZ(19683); tame = true)
    @test length(fields) == 1
    @test norm(conductor(only(fields))[1]) == 3
    @test discriminant(only(fields), QQ) == -19683
    @test isempty(abelian_normal_extensions(K, [2], ZZ(19682); tame = true))

    O = maximal_order(cyclotomic_field(12)[1])
    for (gtype, m, weight) in (([6], 2, 256), ([6], 3, 729),
                               ([6], 6, 186624), ([2, 6], 2, 65536),
                               ([2, 6], 3, 531441))
      conds = Hecke.conductors(O, gtype, ZZ(weight), true)
      @test count(c -> c[1] == m && isempty(c[2]), conds) == 1
      @test all(c -> isempty(c[2]), conds)
      @test !any(c -> c[1] == m && isempty(c[2]),
                 Hecke.conductors(O, gtype, ZZ(weight - 1), true))
    end
  end

  @testset "Tame primes dividing the extension degree" begin
    # The compositum of Q(sqrt(-3)) and the real cubic subfield of Q(zeta_7)
    # is cyclic sextic, with conductor 21 and discriminant -64827 = -3^3*7^4.
    # Its ramification index at 3 is 2: tame ramification at a prime dividing
    # the degree. The old sieve missed this conductor.
    # Also check that disjoint tame and wild local factors can be combined.
    K, = rationals_as_number_field()
    O = maximal_order(K)
    P = prime_decomposition(O, 3)[1][1]
    Q = prime_decomposition(O, 7)[1][1]
    target = Dict(P => 1, Q => 1)
    bound = ZZ(64827)
    conds = Hecke.conductors_generic(O, [6], bound)
    @test count(==(target), conds) == 1
    @test count(==(Dict(P => 2)), conds) == 1
    @test length(conds) == length(Set(conds))
    mixed = Dict(prime_decomposition(O, 2)[1][1] => 2, Q => 1)
    mixed_bound = ZZ(4)^3 * ZZ(7)^4
    @test mixed in Hecke.conductors_generic(O, [6], mixed_bound)
    fields = abelian_extensions(K, [6], bound)
    field = only(filter(C -> norm(conductor(C)[1]) == 21, fields))
    @test abs(discriminant(field, QQ)) == bound
    @test all(C -> norm(conductor(C)[1]) != 21,
              abelian_extensions(K, [6], bound - 1))

    K, = quadratic_field(-31)
    O = maximal_order(K)
    P = prime_decomposition(O, 3)[1][1]
    target = Dict(P => 1)
    bound = abs(discriminant(O))^6 * ZZ(729)
    @test count(==(target), Hecke.conductors_generic(O, [6], bound)) == 1
    @test !(target in Hecke.conductors_generic(O, [6], bound - 1))
    fields = abelian_extensions(K, [6], bound)
    field = only(filter(C -> norm(conductor(C)[1]) == 9, fields))
    @test norm(discriminant(field)) == 729
  end

  @testset "Cyclic sextic discriminants" begin
    # Complete LMFDB list of C6 fields over Q with absolute discriminant <= 10^6.
    # https://www.lmfdb.org/NumberField/?galois_group=6T1
    # Completeness: https://www.lmfdb.org/NumberField/Completeness
    K, = rationals_as_number_field()
    fields = abelian_extensions(K, [6], ZZ(10)^6)
    expected = ZZRingElem[
      -771147, -419904, -153664, -64827, -19683, -16807,
      300125, 371293, 453789, 820125,
    ]
    @test sort!([ZZ(discriminant(C, QQ)) for C in fields]) == expected
  end

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
    O = maximal_order(rationals_as_number_field()[1])
    @test sort!(Hecke.tame_conductors_degree_2(O, ZZ(200);
                                            unramified_outside = ZZ.([2, 3, 5]))) ==
          [(1, ZZ(1)), (3, ZZ(3)), (5, ZZ(5)), (15, ZZ(15))]
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
