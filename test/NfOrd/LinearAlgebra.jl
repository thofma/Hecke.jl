@testset "Linear algebra" begin

  @testset "Dixon solve" begin
    Qx, x = FlintQQ["x"]
    K, a = number_field(x^3 + 3)
    A = rand(matrix_space(K, 4, 4), 10:100)
    while iszero(det(A))
      A = rand(matrix_space(K, 4, 4), 10:100)
    end
    b = rand(matrix_space(K, 4 ,1), 10:100)
    @test A * Hecke._solve_dixon(A, b) == b
  end

  @testset "Pseudo matrices" begin
    Qx, x = polynomial_ring(FlintQQ, "x")

    # Compute a pseudo-hnf of a matrix over Z and check result against the HNF

    K,  a = number_field(x - 1, "a")
    O = maximal_order(K)

    A =
    [ 154830247 724968499 442290149 700116640 313234502;
      384015369 193254623 792471850 452111534 717477652;
      816720700 46054709 339475042 389090910 103149313;
      104945689 475264799 821863415 806964485 676397437;
      281047486 709449227 590950934 18224679 295696061]

    Ahnf =
    [ 1 0 0 0 34095268312495604433062164807036095571620397;
      0 1 0 0 18160914505139254049490851505162505507397915;
      0 0 1 0 37265321283634252189185025806030875371477390;
      0 0 0 1 2276874339297612770861218322365243729516503
      0 0 0 0 37684868701591492337245802520684209569420259]

    de = ZZRingElem(37684868701591492337245802520684209569420259)
    AoverO = matrix_space(O, 5, 5)(map(z -> O(z), A))

    Apm = Hecke.pseudo_matrix( AoverO, [(O(1)*O)::Hecke.AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem} for i in 1:5])

    d = numerator(det(Apm))

    Apseudohnf = Hecke.pseudo_hnf_mod(Apm, d)

    z = Apseudohnf.matrix

    for i in 1:nrows(z)
      Hecke.mul_row!(z, i, K(norm(Apseudohnf.coeffs[i])))
    end

    zinZ = matrix_space(FlintZZ, 5, 5)(map(zz -> numerator(coordinates(O(zz))[1]), z.entries))
    c = parent(zinZ)(Ahnf) - zinZ

    @test all([ mod(c[i,j], de) == 0 for i in 1:5, j in 1:5])

    B = Hecke.pseudo_matrix(matrix(K, [1 1; 1 1; 1 0]), [ ideal(O, K(1)), ideal(O, K(QQFieldElem(1, 2))), ideal(O, K(1)) ])

    Bhnf = pseudo_hnf(B, :lowerleft, true)

    @test Bhnf.matrix == matrix(K, [0 0; 1 0; 1 1])

    # Construct random pseudo-matrices over different fields and check if the
    # pseudo hermite normal form span the same module

    @testset "Q[x]/x^$i - 10)" for i in 2:5
      K,  a = number_field(x^i - 10, "a")
      O = maximal_order(K)
      #println("  Testing over field $(x^i - 10)")

      for j in 1:1
        l = rand(10:20) - i + 1
        ll = rand(1:20)
        z = rand(matrix_space(O, l, l), ZZRingElem(2)^ll)
        #println("    $l x $l matrix with $ll bits")
        cc = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[ideal(O, 1) for i in 1:l]
        pm = Hecke.pseudo_matrix(z, cc)
        d = det(pm)
        ppm = Hecke.pseudo_hnf(pm)
        @test Hecke._spans_subset_of_pseudohnf(pm, ppm)
        @test d == det(ppm)
        ppmkb, trafo = Hecke.pseudo_hnf_kb_with_transform(pm)
        @test Hecke._spans_subset_of_pseudohnf(pm, ppmkb)
        @test ppmkb.matrix == trafo*pm.matrix
      end
    end

    @testset "Field towers" begin
      f = x^2 + 36*x + 16
      K,  a = number_field(f, "a")
      Ky, y = K["y"]
      g = y^3 - 51*y^2 + 30*y - 28
      L, b = number_field(g, "b")

      t = rand(-1000:1000, 3, 3)
      PM = Hecke.pseudo_matrix(matrix(K, t))
      G, U = Hecke.pseudo_hnf_kb_with_transform(PM)
      @test Hecke._spans_subset_of_pseudohnf(PM, G)
      @test !iszero(det(U))
      @test G.matrix == U*PM.matrix

      G2, U2 = Hecke.pseudo_hnf_kb_with_transform(PM, :lowerleft)
      @test Hecke._spans_subset_of_pseudohnf(PM, G2, :lowerleft)
      @test !iszero(det(U2))
      @test G2.matrix == U2*PM.matrix

      Lz, z = L["z"]
      h = z^2 + 4*z + 10
      M, c = number_field(h, "c")
      PN = Hecke.pseudo_matrix(matrix(L, t))
      H, V = Hecke.pseudo_hnf_kb_with_transform(PN)
      @test Hecke._spans_subset_of_pseudohnf(PN, H)
      @test !iszero(det(V))
      @test H.matrix == V*PN.matrix

      H2, V2 = Hecke.pseudo_hnf_kb_with_transform(PN, :lowerleft)
      @test Hecke._spans_subset_of_pseudohnf(PN, H2, :lowerleft)
      @test !iszero(det(V2))
      @test H2.matrix == V2*PN.matrix
    end

    @testset "in span" begin
      K,  a = number_field(x^3 - 10, "a")
      O = maximal_order(K)
      ideals = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]
      p = 2
      while length(ideals) < 5
        ideals = union(ideals, prime_decomposition(O, p))
        p = next_prime(p)
      end
      A = Hecke.pseudo_matrix(one(matrix_space(O, 5, 5)), [ p for (p, e) in ideals ])
      v = [ K(rand(p, 100)) for (p, e) in ideals ]
      @test Hecke._in_span(v, A)[1]

      K,  a = number_field(x, "a")
      O = maximal_order(K)
      A = Hecke.pseudo_matrix(matrix(O, map(O, [ 1 2 3 4; 0 7 8 9; 0 0 11 12; 0 0 0 13 ])), [ O(1)*O for i = 1:4 ])
      @test Hecke._in_span(map(K, [1, 2, 3, 4]), A)[1]
      @test Hecke._in_span(map(K, [5, 6, 7, 8]), A)[1] == false
    end
  end

  @testset "rand" begin
    R, x = polynomial_ring(FlintQQ, "x")
    K, a = number_field(x, "a")
    O = maximal_order(K)
    I = Hecke.AbsSimpleNumFieldOrderFractionalIdeal(ideal(O, O(2)), ZZRingElem(2))
    @assert I isa Hecke.AbsSimpleNumFieldOrderFractionalIdeal
    J = numerator(I)
    @assert J isa Hecke.AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

    for (T, E) in (I => AbsSimpleNumFieldElem, J => Hecke.AbsSimpleNumFieldOrderElem)
      m = make(T, 3)
      @test all(x -> x isa E,
                (rand(T, 3), rand(rng, T, 3), rand(m), rand(rng, m)))
      @test rand(m, 3) isa Vector{E}
      @test reproducible(T, 3)
      @test reproducible(m)
    end
  end

  # issue 859
  Qx, x = polynomial_ring(FlintQQ, "x");
  K, a = number_field(x^2 + 1, "a", cached = false);
  M = matrix(K, 1, 3, [5*a, 3*a, 0])
  pm = pseudo_hnf(pseudo_matrix(M), :lowerleft)
  @test Hecke._spans_subset_of_pseudohnf(pm, pm, :lowerleft)
  M = matrix(K, 1, 3, [0, 0, 3*a])
  pm = pseudo_hnf(pseudo_matrix(M), :lowerleft)
  @test Hecke._spans_subset_of_pseudohnf(pm, pm, :upperright)

  Qx, x = polynomial_ring(FlintQQ, "x")
  f = x - 1
  K, a = number_field(f, "a", cached = false)
  Kt, t = polynomial_ring(K, "t")
  g = t^2 + 1
  E, b = number_field(g, "b", cached = false)
  gens = Vector{Hecke.RelSimpleNumFieldElem{AbsSimpleNumFieldElem}}[map(E, [-6*b + 7, 37//2*b + 21//2, -3//2*b + 5//2]), map(E, [b + 2, 1, 0])]
  pm = pseudo_hnf(pseudo_matrix(matrix(gens)), :lowerleft)
  @test Hecke._spans_subset_of_pseudohnf(pm, pm, :lowerleft)

  # issue 1112
  K, a = cyclotomic_real_subfield(8, "a");
  Kt, t = K["t"];
  E, b = number_field(t^2 - a * t + 1, "b");
  V = hermitian_space(E, gram_matrix(root_lattice(:E, 8)));
  L = lattice(V);
  L2 = dual(L);
  M = pseudo_matrix(L2)
  H = pseudo_hnf(M, :lowerleft)
  @test all(is_one, H.coeffs)
  @test is_one(H.matrix)
end
