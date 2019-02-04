@testset "Linear algebra" begin

  @testset "Pseudo matrices" begin

    Qx, x = PolynomialRing(FlintQQ, "x")

    # Compute a pseudo-hnf of a matrix over Z and check result against the HNF

    K,  a = NumberField(x - 1, "a")
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

    de = fmpz(37684868701591492337245802520684209569420259)
    AoverO = MatrixSpace(O, 5, 5)(map(z -> O(z), A))

    Apm = Hecke.PseudoMatrix( AoverO, [(O(1)*O)::Hecke.NfOrdIdl for i in 1:5])

    d = numerator(det(Apm))

    Apseudohnf = Hecke.pseudo_hnf_mod(Apm, d)

    z = Apseudohnf.matrix

    for i in 1:nrows(z)
      Hecke.mul_row!(z, i, K(norm(Apseudohnf.coeffs[i])))
    end

    zinZ = MatrixSpace(FlintZZ, 5, 5)(map(zz -> numerator(elem_in_basis(O(zz))[1]), z.entries))
    c = parent(zinZ)(Ahnf) - zinZ

    @test all([ mod(c[i,j], de) == 0 for i in 1:5, j in 1:5])

    B = Hecke.PseudoMatrix(matrix(K, [1 1; 1 1; 1 0]), [ ideal(O, K(1)), ideal(O, K(fmpq(1, 2))), ideal(O, K(1)) ])

    Bhnf = pseudo_hnf(B, :lowerleft, true)

    @test Bhnf.matrix == matrix(K, [0 0; 1 0; 1 1])

    # Construct random pseudo-matrices over different fields and check if the
    # pseudo hermite normal form span the same module
    
    @testset "Q[x]/x^$i - 10)" for i in 2:5 
       K,  a = NumberField(x^i - 10, "a")
      O = maximal_order(K)
      #println("  Testing over field $(x^i - 10)")

      for j in 1:1
        l = rand(10:20) - i + 1
        ll = rand(1:20)
        z = rand(MatrixSpace(O, l, l), fmpz(2)^ll)
        #println("    $l x $l matrix with $ll bits")
        cc = [ (O(1)*O)::Hecke.NfOrdIdl for i in 1:l]
        pm = Hecke.PseudoMatrix(z, cc)
        d = det(pm)
        ppm = Hecke.pseudo_hnf(pm)
        @test Hecke._spans_subset_of_pseudohnf(pm, ppm)
        @test d == det(ppm)
        ppmkb, trafo = Hecke.pseudo_hnf_kb_with_trafo(pm)
        @test Hecke._spans_subset_of_pseudohnf(pm, ppmkb)
        @test ppmkb.matrix == trafo*pm.matrix
      end
    end

    @testset "Field towers" begin
      f = x^2 + 36*x + 16
       K,  a = NumberField(f, "a")
      Ky, y = K["y"]
      g = y^3 - 51*y^2 + 30*y - 28
      L, b = NumberField(g, "b")

      t = rand(-1000:1000, 3, 3)
      PM = Hecke.PseudoMatrix(matrix(K, t))
      G, U = Hecke.pseudo_hnf_kb_with_trafo(PM)
      @test Hecke._spans_subset_of_pseudohnf(PM, G)
      @test !iszero(det(U))
      @test G.matrix == U*PM.matrix

      G2, U2 = Hecke.pseudo_hnf_kb_with_trafo(PM, :lowerleft)
      @test Hecke._spans_subset_of_pseudohnf(PM, G2, :lowerleft)
      @test !iszero(det(U2))
      @test G2.matrix == U2*PM.matrix

      Lz, z = L["z"]
      h = z^2 + 4*z + 10
      M, c = NumberField(h, "c")
      PN = Hecke.PseudoMatrix(matrix(L, t))
      H, V = Hecke.pseudo_hnf_kb_with_trafo(PN)
      @test Hecke._spans_subset_of_pseudohnf(PN, H)
      @test !iszero(det(V))
      @test H.matrix == V*PN.matrix

      H2, V2 = Hecke.pseudo_hnf_kb_with_trafo(PN, :lowerleft)
      @test Hecke._spans_subset_of_pseudohnf(PN, H2, :lowerleft)
      @test !iszero(det(V2))
      @test H2.matrix == V2*PN.matrix
    end

    @testset "in span" begin
       K,  a = NumberField(x^3 - 10, "a")
      O = maximal_order(K)
      ideals = []
      p = 2
      while length(ideals) < 5
        ideals = union(ideals, prime_decomposition(O, p))
        p = next_prime(p)
      end
      A = Hecke.PseudoMatrix(one(MatrixSpace(O, 5, 5)), [ p for (p, e) in ideals ])
      v = [ K(rand(p, 100)) for (p, e) in ideals ]
      @test Hecke._in_span(v, A)[1]

       K,  a = NumberField(x, "a")
      O = maximal_order(K)
      A = Hecke.PseudoMatrix(matrix(O, map(O, [ 1 2 3 4; 0 7 8 9; 0 0 11 12; 0 0 0 13 ])), [ O(1)*O for i = 1:4 ])
      @test Hecke._in_span(map(K, [1, 2, 3, 4]), A)[1]
      @test Hecke._in_span(map(K, [5, 6, 7, 8]), A)[1] == false
    end
  end
end

