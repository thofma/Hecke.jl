@testset "Totally real and totally complex class fields" begin
  Qx, x = polynomial_ring(QQ)

  for (f, sig) in [(x^2 - 10, (4, 0)), (x^2 + 5, (0, 2)), (x^3 - 2, (1, 1))]
    K, a = number_field(f)
    C = hilbert_class_field(K)
    @test signature(C) == sig
    @test @inferred(is_totally_real(C)) == iszero(sig[2])
    @test @inferred(is_totally_complex(C)) == iszero(sig[1])
  end

  K, a = number_field(x - 1)
  OK = maximal_order(K)
  C = ray_class_field(5 * OK)
  @test signature(C) == (2, 0)
  @test @inferred is_totally_real(C)
  @test @inferred !is_totally_complex(C)

  C = ray_class_field(5 * OK, real_places(K))
  @test signature(C) == (0, 2)
  @test @inferred !is_totally_real(C)
  @test @inferred is_totally_complex(C)

  C = ray_class_field(5 * OK, real_places(K), n_quo = 2)
  @test signature(C) == (2, 0)
  @test @inferred is_totally_real(C)
  @test @inferred !is_totally_complex(C)
end

@testset "Class field subfields" begin
  K = quadratic_field(3)[1]
  for C in (hilbert_class_field(quadratic_field(13*17*37)[1]),
            cyclotomic_field(ClassField, 13),
            ray_class_field(5*maximal_order(K), real_places(K)))
    @test_throws ArgumentError subfields(C; degre = 2)
    @test_throws ArgumentError subfields(C; degree = 2, type = [2])
    @test_throws ArgumentError subfields(C; degree = 2, type = [2], is_normal)
    @test_throws ArgumentError subfields(C; degree = 2.0)
    @test_throws ArgumentError subfields(C; type = 2)

    # Enumerate all subfields of C/base_field(C) using subgroups, independently
    # of stable_subgroups and its degree/type restrictions.
    mQ = C.quotientmap
    expected = [ray_class_field(C.rayclassgroupmap, mQ*q)
                for (_, q) in subgroups(codomain(mQ); fun = quo)]
    # No normality flag, followed by two ways to request normality over QQ
    # (the field fixed by all automorphisms of each base field used here).
    for normality in ((;), (; is_normal),
                      (; is_normal = automorphism_list(base_field(C))))
      all_fields = subfields(C; normality...)
      reference = isempty(normality) ? expected : filter(is_normal, expected)
      @test Set(all_fields) == Set(reference)
      for d in divisors(degree(C))
        actual = subfields(C; degree = Int(d), normality...)
        @test Set(actual) == Set(filter(F -> degree(F) == d, reference))
      end
      for d in (3, Int(degree(C)) + 1)
        @test Set(subfields(C; degree = d, normality...)) ==
              Set(filter(F -> degree(F) == d, reference))
      end
      for d in (-2, -1, 0)
        @test Set(subfields(C; degree = d, normality...)) == Set(reference)
      end
      for t in (Int[], [1], [2], [2, 2], [4], [3], [5])
        actual = subfields(C; type = t, normality...)
        @test Set(actual) == Set(filter(F -> is_isomorphic(codomain(F.quotientmap), abelian_group(t)), reference))
      end
    end

    trivial = only(subfields(C; degree = 1))
    @test is_normal(trivial)
    @test only(subfields(trivial; is_normal)) == trivial
    @test only(subfields(trivial)) == trivial
    @test only(subfields(trivial; type = Int[])) == trivial
    @test isempty(subfields(trivial; degree = 2))
    @test isempty(subfields(trivial; type = [4]))
    @test isempty(subfields(trivial; type = [4], is_normal))
  end
end

@testset "RCF" begin
  Qx, x = polynomial_ring(QQ)
  k, a = number_field(x - 1, "a")
  Z = maximal_order(k)

  @testset "quadratic Kummer generator" begin
    R, mR = ray_class_group(5 * Z, real_places(k), n_quo = 2)
    quotients = collect(index_p_subgroups(
      R, ZZRingElem(2), (A, H) -> quo(A, H)[2]))
    C = ray_class_field(mR, only(quotients))

    @test !isdefined(C, :A)
    @test !isdefined(C, :cyc)
    generator = quadratic_kummer_generator(C)
    @test base_ring(generator) === k
    @test !is_square(evaluate(generator))
    @test !isdefined(C, :A)
    @test !isdefined(C, :cyc)

    extension = kummer_extension(2, [generator])
    for q in (3, 7, 11, 13, 17, 19)
      P = first(prime_decomposition(Z, q))[1]
      artin_image = C.quotientmap(preimage(C.rayclassgroupmap, P))
      expected = mod(Int(artin_image[1]), 2)
      observed = mod(Int(Hecke.canonical_frobenius(P, extension)[1]), 2)
      @test observed == expected
    end
  end

  function doit(u::AbstractUnitRange, p::Int = 3)
    cnt = 0
    for i in u
      I = ideal(Z, i)
      r, mr = ray_class_group(I, n_quo=p)
      for s in index_p_subgroups(r, ZZRingElem(p), (A,x) -> quo(A, x)[2])
        a = ray_class_field(mr, s)
        if is_conductor(a, I, check=false)
          K = number_field(a)
          cnt += 1
        end
      end
    end
    return cnt
  end

  @test doit(1:100) == 16
  @test doit(10^18:10^18+100) == 18
  @test doit(10^18:10^18+1000, 11) == 2

  K, a = quadratic_field(-5)
  H = hilbert_class_field(K)
  L = number_field(H, over_subfield = true)
  @test absolute_degree(L) == 4

  f = x^3 - 36*x -1
  K, a = number_field(f, cached = false, check = false)
  H = hilbert_class_field(K)
  L1 = number_field(H)
  L2 = number_field(H, using_stark_units = true, redo = true)
  @test is_isomorphic(Hecke.simplified_absolute_field(L1)[1], Hecke.simplified_absolute_field(L2)[1])

  f = x^2 - x - 100
  K, a = number_field(f, cached = false, check = false)
  H = hilbert_class_field(K)
  L1 = number_field(H)
  L2 = number_field(H, using_stark_units = true, redo = true)
  @test is_isomorphic(Hecke.simplified_absolute_field(L1)[1], Hecke.simplified_absolute_field(L2)[1])
  @test length(closure(Hecke.absolute_automorphism_group(H), *)) == 10

  r, mr = Hecke.ray_class_groupQQ(Z, 32, true, 8);
  q, mq = quo(r, [r[1]])
  C = ray_class_field(mr, mq)
  KC = number_field(C)
  auts = Hecke.rel_auto(C)
  @test length(closure(auts, *)) == 8

  k, a = wildanger_field(3, 13)
  zk = maximal_order(k)
  r0 = hilbert_class_field(k)
  @test degree(r0) == 9
  r1 = ray_class_field(4*zk, n_quo = 2)
  r2 = ray_class_field(5*zk, n_quo = 2)
  @test isone(conductor(intersect(r1, r2))[1])
  @test conductor(r1 * r2)[1] == 20*zk
  @test Hecke.is_subfield(r1, r1*r2)
  @test !Hecke.is_subfield(r0, r1*r2)

  K = simple_extension(number_field(r1))[1]
  ZK = maximal_order(K)
  lp = factor(2*3*5*maximal_order(k))
  for p = keys(lp)
    t = prime_decomposition_type(r1, p)
    l = prime_decomposition(ZK, p)
    @test t[3] == length(l)
    @test valuation(norm(l[1][1]), p) == t[2]
    @test t[1] * t[2] * t[3] == degree(r1)
    @test all(x->valuation(norm(x[1]), p) == t[2], l)
  end

  ln = [(2, true), (3, false), (5, false), (13, true), (31, false)]
  for (p, b) = ln
    @test Hecke.is_local_norm(r1, zk(p)) == b
  end

  Qx, x = polynomial_ring(QQ, "x");
  k, a = number_field(x^2 - 10, "a");
  A = ray_class_field(35*maximal_order(k))
  B = Hecke.maximal_abelian_subfield(A, k)
  @test A == B
  @test conductor(A) == conductor(B)

  K, _ = compositum(k, wildanger_field(3, 13)[1])
  A = maximal_abelian_subfield(ClassField, K)
  @test degree(A) == 2
  @test degree(intersect(A, cyclotomic_field(ClassField, 10))) == 1

  Qx, x = polynomial_ring(QQ, "x");
  k, a = number_field(x^2 - 10, "a");
  A = ray_class_field(35*maximal_order(k))

  K, = simple_extension(number_field(A))
  @test A == maximal_abelian_subfield(K)

  K, = simple_extension(number_field(A))
  maximal_order(K)
  @test A == maximal_abelian_subfield(K)

  cyclotomic_extension(k, 6)
  Hecke._cyclotomic_extension_non_simple(k, 6)

  r = ray_class_field(5*maximal_order(quadratic_field(3)[1]))
  absaut = absolute_automorphism_group(r)
  @test length(closure(absaut, *)) == 8 # normal

  r = ray_class_field(27*maximal_order(quadratic_field(42)[1]))
  @test absolute_automorphism_group(r) isa Vector
  # Too large to check

  K = quadratic_field(3)[1]
  OK = maximal_order(K)
  rcf = ray_class_field(5*OK, real_places(K))
  absaut = absolute_automorphism_group(rcf) # normal
  @test length(closure(absaut, *)) == 32

  r = hilbert_class_field(quadratic_field(13*17*37)[1])
  @test isone(discriminant(r))
  absaut = absolute_automorphism_group(r) # normal
  @test length(closure(absaut, *)) == 8
  a, ma = automorphism_group(r)
  @assert order(a) == 4
  f = ma(a[1]) * ma(a[2])
  @assert preimage(ma, f) == a([1,1])

  f = frobenius_map(r)
  lp = prime_decomposition(base_ring(r), 19)
  @assert preimage(ma, f(lp[1][1])) == a[2] #true for both actually.
  Hecke.find_frob(r.cyc[1])
  norm_group(r)

  s = ray_class_field(7*base_ring(r))
  h = hom(base_field(r), base_field(r), gen(base_field(r)))
  q = Hecke.extend_hom(r, s, h)
  @test q == "not finished"
  @test Hecke.maximal_p_subfield(s, 2) == r

  @test is_abelian(number_field(r))
  @test is_abelian(base_field(r))
  @test length(subfields(r)) == 5
  @test length(subfields(r; degree = 2)) == 3
  @test is_central(r)
  @test length(subfields(r; degree = 2, is_normal)) == 3
  @test length(subfields(r; type = [2], is_normal)) == 3
  @test length(subfields(r; is_normal = automorphism_list(base_field(r)))) == 5

  K = quadratic_field(5)[1]
  OK = maximal_order(K)
  rcf = ray_class_field(9*OK, real_places(K))
  @test length(closure(absolute_automorphism_group(rcf), *)) == 12

  rcf = ray_class_field(21*OK, real_places(K))
  c = conductor(rcf)
  @test c[1] == 21*OK
  @test length(c[2]) == 2 # the order is wrong

  k = quadratic_field(8)[1]
  e = equation_order(k)
  @test degree(Hecke.ring_class_field(e)) == 1
  k = quadratic_field(8*9)[1]
  e = equation_order(k)
  @test degree(Hecke.ring_class_field(e)) == 2

  k, _ = number_field(x^3 - 69*x - 52)
  kk = number_field(ray_class_field(1*maximal_order(k), real_places(k)))
  @test degree(kk) == 2

  k, a= wildanger_field(3, 13)
  C = ray_class_field(7*maximal_order(k); n_quo = 3)
  for p = [2, 3, 5, 7]
    d = absolute_prime_decomposition_type(C, p)
    @test sum(x[1]*x[2]*x[3] for x = d) == absolute_degree(C)
  end
end

@testset "Jon Yard" begin
  for (D, m) = [(3, 32), (5, 32), (13, 32), (3, 27)]
    K = quadratic_field(D)[1]
    OK = maximal_order(K)
    rcf = ray_class_field(m*OK,real_places(K))
    F = number_field(rcf)
#    @show length(absolute_automorphism_group(rcf))
    @test length(absolute_automorphism_group(rcf)) > 1
  end
end

@testset "Some abelian extensions" begin
  Qx, x = polynomial_ring(QQ, "x")
  K, a = number_field(x - 1, "a")
  O = maximal_order(K)
  r, mr = Hecke.ray_class_groupQQ(O, 7872, true, 16)
  ls = subgroups(r, quotype = [16], fun = (x, y) -> quo(x, y, false)[2])
  @test Hecke.has_quotient(r, [16])
  class_fields = []
  for s in ls;
    C = ray_class_field(mr, s)::Hecke.ClassField{Hecke.MapRayClassGrp, FinGenAbGroupHom}
    CC = number_field(C)
    if Hecke._is_conductor_minQQ(C, 16)
      push!(class_fields, CC)
    end
  end
  @test length(class_fields) == 14

  K, a = quadratic_field(2, cached = false)
  @test length(abelian_extensions(K, [2], ZZRingElem(10)^4, absolutely_distinct = true)) == 38

  # with target signatures
  K, a = number_field(x^3 - x^2 - 2*x + 1, cached = false)
  l = abelian_extensions(K, [2, 2], ZZRingElem(10)^12)
  @test length(l) == 28
  l1 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(4, 4)])
  @test length(l1) == 3
  l2 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(0, 6)])
  @test length(l2) == 25
  l3 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(0, 6), (4, 4)])
  @test length(l3) == 28
  l4 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(0, 6), (4, 4), (0, 0)])
  @test length(l4) == 28
  l5 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(0, 0)])
  @test length(l5) == 0

  # a wrong conductor

  K, = cyclotomic_field(21)
  C = maximal_abelian_subfield(ClassField, K)
  @test norm(conductor(C)[1]) == 21

  C = cyclotomic_field(ClassField, 1)
  @test C == C*C
end

@testset "Empty tame abelian extension search" begin
  # A tame search with no possible fields returns an empty result.
  K, _ = quadratic_field(2, cached = false)
  @test isempty(abelian_extensions(K, [2], ZZ(1);
                                  signatures = [(4, 0)], only_tame = true))
end

@testset "Abelian extension search bounds" begin
  # Validate prime norm bounds independently of signature and tame filters.
  K, _ = quadratic_field(2, cached = false)
  OK = maximal_order(K)
  bound = ZZ(10)^25
  err = ArgumentError("Discriminant bound too large: prime ideal norm bound must fit in Int")
  for only_tame in (false, true)
    @test_throws err Hecke.conductors_generic(OK, [2], bound; only_tame)
    @test_throws err abelian_extensions(K, [2], bound; only_tame)
    @test_throws err abelian_extensions(K, [2], bound;
                                       signatures = [(4, 0)], only_tame)
    @test_throws err abelian_extensions(K, [2], bound;
                                       signatures = [(0, 0)], only_tame)
  end
  # Large discriminant bounds are supported when the prime norm bound is small.
  bound = abs(discriminant(OK))^19 * ZZ(2)^18
  @test isempty(only(Hecke.conductors_generic(OK, [19], bound; only_tame = true)))
end

@testset "Tame abelian extension searches" begin
  # A quadratic extension is tame exactly when it is unramified above 2.
  K, _ = quadratic_field(2, cached = false)
  all_fields = abelian_extensions(K, [2], ZZ(10)^3)
  expected = filter(C -> isodd(norm(conductor(C)[1])), all_fields)
  tame_fields = abelian_extensions(K, [2], ZZ(10)^3; only_tame = true)
  @test !isempty(tame_fields)
  @test Set(tame_fields) == Set(expected)
end

@testset "Abelian extensions with prescribed infinite ramification" begin
  # Absolute representatives must preserve the prescribed real ramification.
  K, = quadratic_field(5)
  O = maximal_order(K)
  places = real_places(K)
  finite_conductor = 6061*O
  bound = ZZ(5)^4 * ZZ(6061)^4
  for p in places
    fields = abelian_extensions(K, [2, 2], bound;
                                conductors = [finite_conductor],
                                ramified_at_inf_plc = (true, [p]))
    distinct = abelian_extensions(K, [2, 2], bound;
                                  conductors = [finite_conductor],
                                  ramified_at_inf_plc = (true, [p]),
                                  absolutely_distinct = true)
    @test length(fields) == length(distinct) == 27
    @test fields == distinct || Set(fields) == Set(distinct)
    @test all(C -> conductor(C) == (finite_conductor, [p]), distinct)
    @test all(C -> signature(C) == (4, 2), distinct)
    @test all(C -> discriminant(C, QQ) == bound, distinct)
    @test isempty(abelian_extensions(K, [2, 2], bound - 1;
                                    conductors = [finite_conductor],
                                    ramified_at_inf_plc = (true, [p]),
                                    absolutely_distinct = true))
  end

  Qx, x = QQ[:x]
  reference, = number_field(x^4 - 6*x^2 - 11)
  primes = first.(prime_decomposition(O, 11))
  for p in places
    fields = abelian_extensions(K, [2], ZZ(275);
                                conductors = primes,
                                ramified_at_inf_plc = (true, [p]))
    @test length(fields) == 1
    for conds in (primes, reverse(primes))
      distinct = abelian_extensions(K, [2], ZZ(275);
                                    conductors = conds,
                                    ramified_at_inf_plc = (true, [p]),
                                    absolutely_distinct = true)
      @test fields == distinct
      @test norm(conductor(only(distinct))[1]) == 11
      @test conductor(only(distinct))[2] == [p]
      L = number_field(AbsSimpleNumField, only(distinct))
      @test discriminant(maximal_order(L)) == -275
      @test signature(L) == (2, 1)
      @test is_isomorphic(L, reference)
    end
  end

  mixed_reference, = number_field(x^4 - x^2 - 1)
  complex_reference, = number_field(x^4 - 8*x^2 + 36)
  fields = abelian_extensions(K, [2], ZZ(400); conductors = [4*O])
  distinct = abelian_extensions(K, [2], ZZ(400);
                                conductors = [4*O],
                                absolutely_distinct = true)
  for (list, expected) in ((fields, [-400, -400, 400]),
                           (distinct, [-400, 400]))
    number_fields = [number_field(AbsSimpleNumField, C) for C in list]
    @test sort!([discriminant(maximal_order(L)) for L in number_fields]) ==
          expected
    for L in number_fields
      reference = signature(L) == (2, 1) ? mixed_reference : complex_reference
      @test is_isomorphic(L, reference)
    end
  end
  complex_field = only(filter(C -> signature(C) == (0, 2), distinct))
  for absolutely_distinct in (false, true)
    @test isempty(abelian_extensions(K, [2], ZZ(400);
                                    conductors = [4*O],
                                    ramified_at_inf_plc = (true, places[1:0]),
                                    absolutely_distinct = absolutely_distinct))
    fields = abelian_extensions(K, [2], ZZ(400);
                                conductors = [4*O],
                                ramified_at_inf_plc = (true, places),
                                absolutely_distinct = absolutely_distinct)
    @test length(fields) == 1
    @test only(fields) == complex_field
  end

  conductors = [4*P for P in primes]
  fields = abelian_extensions(K, [2], ZZ(4400);
                              conductors = conductors,
                              ramified_at_inf_plc = (true, places))
  distinct = abelian_extensions(K, [2], ZZ(4400);
                                conductors = conductors,
                                ramified_at_inf_plc = (true, reverse(places)),
                                absolutely_distinct = true)
  @test length(fields) == 2
  @test length(distinct) == 1
  reference, = number_field(x^4 + 8*x^2 + 11)
  L = number_field(AbsSimpleNumField, only(distinct))
  @test discriminant(maximal_order(L)) == 4400
  @test signature(L) == (0, 2)
  @test is_isomorphic(L, reference)
end

@testset "Absolutely distinct extensions with target signature" begin
  # Signature searches identify conjugate fields across infinite-place subsets.
  K, = quadratic_field(5)
  O = maximal_order(K)
  primes = first.(prime_decomposition(O, 11))
  relative_fields = abelian_extensions(K, [2], ZZ(275);
                                      conductors = primes,
                                      signatures = [(2, 1)])
  @test length(relative_fields) == 2
  Qx, x = QQ[:x]
  reference, = number_field(x^4 - 6*x^2 - 11)
  for conds in (primes, reverse(primes))
    fields = abelian_extensions(K, [2], ZZ(275);
                               conductors = conds,
                               signatures = [(2, 1)],
                               absolutely_distinct = true)
    @test length(fields) == 1
    L = number_field(AbsSimpleNumField, only(fields))
    @test discriminant(maximal_order(L)) == -275
    @test signature(L) == (2, 1)
    @test is_isomorphic(L, reference)
  end

  for P in primes
    single = only(filter(C -> conductor(C)[1] == P, relative_fields))
    for conds in ([P], [factor(P)])
      fields = abelian_extensions(K, [2], ZZ(275);
                                 conductors = conds,
                                 signatures = [(2, 1)],
                                 absolutely_distinct = true)
      @test length(fields) == 1
      @test only(fields) == single
    end
    for ideals in ([P, 4*O], [4*O, P])
      for conds in (ideals, factor.(ideals))
        fields = abelian_extensions(K, [2], ZZ(400);
                                   conductors = conds,
                                   signatures = [(2, 1)],
                                   absolutely_distinct = true)
        @test sort!([discriminant(C, QQ) for C in fields]) == [-400, -275]
        @test all(C -> signature(C) == (2, 1), fields)
        @test all(C -> conductor(C)[1] in ideals, fields)
        @test only(filter(C -> conductor(C)[1] == P, fields)) == single
      end
    end
  end

  mixed_reference, = number_field(x^4 - x^2 - 1)
  fields = abelian_extensions(K, [2], ZZ(400);
                             conductors = [4*O],
                             signatures = [(2, 1)],
                             absolutely_distinct = true)
  @test length(fields) == 1
  L = number_field(AbsSimpleNumField, only(fields))
  @test discriminant(maximal_order(L)) == -400
  @test signature(L) == (2, 1)
  @test is_isomorphic(L, mixed_reference)

  fields = abelian_extensions(K, [2], ZZ(400);
                             signatures = [(2, 1)],
                             absolutely_distinct = true)
  number_fields = [number_field(AbsSimpleNumField, C) for C in fields]
  @test sort!([discriminant(maximal_order(L)) for L in number_fields]) ==
        [-400, -275]
  @test all(L -> signature(L) == (2, 1), number_fields)
  @test count(L -> is_isomorphic(L, reference), number_fields) == 1
  @test count(L -> is_isomorphic(L, mixed_reference), number_fields) == 1

  for absolutely_distinct in (false, true)
    @test isempty(abelian_extensions(K, [2], ZZ(400);
                                    conductors = [4*O],
                                    signatures = [(4, 0)],
                                    absolutely_distinct = absolutely_distinct))
    fields = abelian_extensions(K, [2], ZZ(400);
                               conductors = [4*O],
                               signatures = [(0, 2)],
                               absolutely_distinct = absolutely_distinct)
    @test length(fields) == 1
    @test signature(only(fields)) == (0, 2)
    @test discriminant(only(fields), QQ) == 400
  end

  permutations = [[1, 2, 3, 4], [2, 3, 4, 1],
                  [3, 4, 1, 2], [4, 1, 2, 3]]
  candidates = [[1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]]
  full_orbits = [[[1, 2], [1, 4], [2, 3], [3, 4]], [[1, 3], [2, 4]]]
  half_orbits = [[[1, 2], [3, 4]], [[1, 3]], [[1, 4], [2, 3]], [[2, 4]]]
  for (stabilizer, expected_orbits) in
      (([1, 2, 3, 4], full_orbits), ([1, 3], half_orbits),
       ([1], [[s] for s in candidates]))
    seen = Set{Vector{Int}}()
    representatives = [s for s in candidates
                       if Hecke._is_new_infinite_orbit!(seen, permutations,
                                                       stabilizer, s)]
    @test length(representatives) == length(expected_orbits)
    @test all(orbit -> count(s -> s in orbit, representatives) == 1,
              expected_orbits)
  end
end

@testset "Frobenius at infinity" begin
  K, = quadratic_field(21)
  OK = maximal_order(K)
  C = ray_class_field(6*OK, real_places(K)[1:1])
  sigma = complex_conjugation(C, real_places(K)[1])
  L = number_field(C)
  e = real_embeddings(K)[1]
  @test all(ee -> sigma * ee == conj(ee), extend(e, hom(K, L)))

  k, = quadratic_field(23)
  @test_throws ArgumentError complex_conjugation(C, real_places(k)[1])
  C = ray_class_field(6*OK, real_places(K)[1:1])
  @test_throws ArgumentError complex_conjugation(C, real_places(K)[2])

  K = quadratic_field(15)[1]
  OK = maximal_order(K)
  rcf = ray_class_field(9*OK,real_places(K))
  @test domain(complex_conjugation(rcf,real_places(K)[1])) == number_field(rcf)
end


@testset "extend base field" begin
  Qx, x = QQ["x"]
  k, a = number_field(x^3 - 3*x^2 - 87*x + 424)
  #random transformation from x^3-5 - so that lll does s.th.
  K, mkK = normal_closure(k)

  zk = lll(maximal_order(k))
  ZK = lll(maximal_order(K))

  C, mC = ray_class_group(27*zk, real_places(k))
  Lambda = ray_class_field(mC)
  G = genus_field(Lambda, rationals_as_number_field()[1])
  @test degree(G) == 54

  GK = Hecke.extend_base_field(G, mkK)
  @test degree(GK) == 27

  GG = genus_field(ray_class_field(27*ZK), k)
  @test degree(GG) == 9*27
end

@testset "Knots - elementary" begin
  Qx, x = QQ["x"]
  f = x^4 - x^3 - 32*x^2 + 23*x + 224
  k = number_field(f, cached = false)[1];
  zk = lll(maximal_order(k))
  Gamma = ray_class_field(8*zk, real_places(k))
  @test degree(Gamma) == 128

  G = genus_field(Gamma)
  @test degree(G) == 8

  Z = Hecke.maximal_central_subfield(Gamma, stable = 20, lower_bound = degree(G))
  @test degree(Z) == 16

  lp = prime_decomposition(zk, 2)
  d = Set([elementary_divisors(decomposition_group(Gamma, p[1])) for p = lp])
  @test d == Set([ZZRingElem[2,2,4], ZZRingElem[2,2,2,2,4]])

  d = Set([elementary_divisors(inertia_subgroup(Gamma, p[1])) for p = lp])
  @test d == Set([ZZRingElem[2,2], ZZRingElem[2,2,2,2]])
end

@testset "Knots - abelian" begin
  Qx, x = QQ["x"]
  f = x^4 - x^3 - 32*x^2 + 23*x + 224
  k = splitting_field(f)
  s = subfields(k, degree = 3)[1][1]
  k = relative_simple_extension(k, s)[1]
  C = ray_class_field(k)
  @test order(Hecke.knot(C)) == 2

  k = number_field([x^2-3, x^2-5])[1]
  ka = absolute_simple_field(k)[1]
  C = ray_class_field(ka)
  @test order(Hecke.knot(C)) == 1

  k = number_field([x^2+3, x^2-13])[1]
  ka = absolute_simple_field(k)[1]
  C = ray_class_field(ka)
  @test order(Hecke.knot(C)) == 2

  Z, G = Hecke.small_knot(ka)
  @test degree(Z) == 2
  @test degree(G) == 1
end

@testset "Knots - non-abelian" begin
  k, a = cyclotomic_field(7)
  f = minpoly(a+1//a)
  k, a = number_field(f)
  zk = lll(maximal_order(k))
  R = ray_class_field(29*31*37*41*43*zk, n_quo = 2)
  G, mG = automorphism_group(k)
  h = Hecke.norm_group_map(R, R, mG(G[1]))
  hh = Hecke.norm_group_map(R, R, mG(G[2]))
  S = fixed_field(R, kernel(h-hh)[1])

  ns = norm_group(S)[1]
  for i = subgroups(ns; quotype = [2,2])
    t = fixed_field(S, i[1])
    @test degree(t) == 4
    @test is_normal(t) || normal_closure(t) == S
  end
end

@testset "Conductor fix" begin
  flds = abelian_extensions(QQ, [2, 2], ZZ(4225), only_real = true)
  @test length(flds) == 4
end

@testset "Kaiser-Lorenz" begin
  Qx, x = QQ["x"]
  f = x^6-x^5+x^4-2*x^3+x^2+1
  k = splitting_field(f)
  I = Hecke.lorenz_module(k, 12)
  @test Hecke.is_consistent(I)
end

@testset "Enumerate by conductor" begin
  l = abelian_extensions([3], collect(1:10^3); only_real = true)
  @test length(l) == 159
  l = abelian_extensions([2], collect(1:10^3))
  @test length(l) == 607
end

let
  Qx, x = QQ["x"]
  K, a = rationals_as_number_field()
  all_fields = abelian_extensions(K, [2], ZZRingElem(10)^3, absolutely_distinct = true)
  OK = maximal_order(K)
  lp = prime_ideals_up_to(OK, 10^3)
  prime_cond = abelian_extensions(K, [2], ZZRingElem(10)^3, absolutely_distinct = true, conductors = lp)
  @test length(prime_cond) == count(is_prime.(first.(conductor.(all_fields))))

  # with target signatures
  K, a = number_field(x^3 - x^2 - 2*x + 1, cached = false)
  l = abelian_extensions(K, [2, 2], ZZRingElem(10)^12)
  conds = Hecke.conductors_generic(K, [2, 2], ZZ(10)^12)
  l = abelian_extensions(K, [2, 2], ZZRingElem(10)^12)
  ll = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, conductors = conds)
  @test length(l) == length(ll)
  l1 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(4, 4)])
  ll1 = abelian_extensions(K, [2, 2], ZZRingElem(10)^12, signatures = [(4, 4)], conductors = conds)
  @test length(l1) == length(ll1)
end

let
  # https://github.com/thofma/Hecke.jl/issues/1625
  K, a = cyclotomic_field(7, :a)
  P, x = polynomial_ring(K, :x)
  L, = number_field(x^3 - 840539241479//13824*a^5 - 18036715089631//9216*a^4 - 18036715089631//9216*a^3 - 840539241479//13824*a^2 - 7320065966297//9216)
  @test !is_abelian(L)
end

let
  # fix hashing
  K, = quadratic_field(-1)
  OK = maximal_order(K)
  C = ray_class_field(1*OK)
  CC = ray_class_field(1*OK)
  @test C == CC
  @test hash(C) == hash(CC)
  D = Dict()
  D[C] = 1
  @test haskey(D, CC)
end

@testset "Grunwald Wang" begin
  Q = rationals_as_number_field()[1]
  Z = maximal_order(Q)
  @test degree(Hecke.grunwald_wang(Dict(2*Z => 2, 5*Z => 2))) == 2
  @test degree(Hecke.grunwald_wang(Dict(2*Z => 2, 5*Z => 3))) == 6
end

let # cornercase with trivial automorphism group
  Qx, x = QQ[:x]
  f = x^4 + 4*x^2 + 1
  K, a = number_field(f, :a)
  OK = maximal_order(K)
  ab = abelian_normal_extensions(K, [4], ZZ(100000000000000000000545460846592))
  L = number_field(ab[1])
  @test degree(L) == 4
end

@testset "Candy" begin
  C = cyclotomic_field(ClassField, 12)
  @test ngens(number_field(C)) == 2
  @test ngens(number_field(SimpleNumField, C)) == 1
  @test degree(number_field(AbsSimpleNumField, C)) == 4

  k, a = wildanger_field(3, 13)
  H = hilbert_class_field(k)
  d = discriminant(FacElem, H)
  @test is_one(evaluate(d))
  d = absolute_discriminant(FacElem, H)
  @test evaluate(d) == discriminant(maximal_order(k))^9
end
