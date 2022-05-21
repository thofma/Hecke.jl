@testset "ZGenus" begin
  A = matrix(ZZ, 2, 2, [1, 1, 1, 1])
  @test (false, 1) == Hecke._iseven(A)
  A = matrix(ZZ, 2, 2, [2, 1, 1, 2])
  @test (true, -1) == Hecke._iseven(A)
  @test iseven(genus(A))

  A = matrix(ZZ, 2, 2, [1, 2, 2, 3])
  @test (false, 1) == Hecke._iseven(A)
  @test (1, ZZ[-1;]) == Hecke._split_odd(A)


  A = matrix(ZZ, 2, 2, [1, 2, 2, 3])
  @test (1, ZZ[-1;]) ==  Hecke._split_odd(A)
  @test 0== Hecke._trace_diag_mod_8(A)

  A = matrix(ZZ, 2, 2, [1, 2, 2, 5])
  @test (1, ZZ[1;]) ==  Hecke._split_odd(A)
  @test (false, 1) == Hecke._iseven(A)
  @test 2== Hecke._trace_diag_mod_8(A)

  A = 2*diagonal_matrix(map(ZZ,[1, 2, 3, 4]))
  @test Hecke._p_adic_symbol(A, 2, 2) == [[1, 2, 3, 1, 4], [2, 1, 1, 1, 1], [3, 1, 1, 1, 1]]
  @test Hecke._p_adic_symbol(A, 3, 1) == [[0, 3, 1], [1, 1, -1]]

  A = diagonal_matrix(map(ZZ, [1, 2, 3, 4]))
  @test Hecke._two_adic_symbol(A, 2) == [[0, 2, 3, 1, 4], [1, 1, 1, 1, 1], [2, 1, 1, 1, 1]]

  #equality testing
  g1 = ZpGenus(2,[[0, 2, 7, 0, 0], [3, 1, 7, 1, 7]])
  g2 = ZpGenus(2,[[0, 2, 3, 0, 0], [3, 1, 3, 1, 3]])
  @test g1 != g2

  g1 = genus(A, 3)
  g2 = genus(A, 3)
  @test g1 == g2
  @test iseven(g1)
  @test 4==dim(g1)
  @test 4 == rank(g1)
  @test 4 == dim(g1)
  @test 6 == det(g1)
  g1 = genus(A,2)
  @test det(g1) == 3*8

  A = diagonal_matrix(map(ZZ,[1,3,-3]))
  @test excess(genus(A, 2)) == 2
  @test excess(genus(A, 3)) == 0
  @test excess(genus(A, 5)) == 0
  @test excess(genus(A, 7)) == 0
  @test excess(genus(A, 11)) == 0
  A = 2*diagonal_matrix(map(ZZ,[1,3,-3]))
  @test excess(genus(A, 2)) == 2
  @test excess(genus(A, 3)) == 0
  @test excess(genus(A, 5)) == 0
  @test excess(genus(A, 7)) == 0
  @test excess(genus(A, 11)) == 0

  A = 2*diagonal_matrix(map(ZZ,[1,2,3,4]))
  @test excess(genus(A, 2)) == 2
  @test excess(genus(A, 3)) == 6
  @test excess(genus(A, 5)) == 0
  @test excess(genus(A, 7)) == 0
  @test excess(genus(A, 11)) == 0

  A = diagonal_matrix(map(ZZ,[2, 4, 18]))
  G = genus(A, 2)
  @test level(G) == 4

  A = diagonal_matrix(map(ZZ,[2, 4, 18]))
  G = genus(A, 2)
  @test norm(G) == 2
  @test scale(G) == 2
  @test scale(genus(A, 3)) == 1
  A = ZZ[0 1; 1 0]
  @test norm(genus(A, 2)) == 2

  A = diagonal_matrix(map(ZZ, [1, 2, 3]))
  g = genus(A, 2)
  @test signature(g) == 5
  g = genus(A, 3)
  @test signature(g) == 1

  A = matrix(ZZ, 2, 2, [1,1,1,2])
  G2 = genus(A, 2)
  @test Hecke._is2adic_genus(G2._symbol)
  @test Hecke._is2adic_genus(G2)
  @test sprint(show, G2) isa String
  A = matrix(ZZ, 2, 2, [1,0,0,2])
  G = genus(A)
  @test 2 == det(G)
  @test !iseven(G)

  output =[[15, 2, 3, 0, 0],
         [15, 2, 7, 0, 0],
         [15, 2, 1, 1, 2],
         [15, 2, 5, 1, 6],
         [15, 2, 1, 1, 6],
         [15, 2, 5, 1, 2],
         [15, 2, 7, 1, 0],
         [15, 2, 3, 1, 4]]
  @test output == Hecke._blocks([15, 2, 0, 0, 0])

  @test size(Hecke._local_genera(2, 3, 1, 2, false))[1]==12
  @test size(Hecke._local_genera(2, 3, 1, 2, true))[1]==4
  @test size(Hecke._local_genera(5, 2, 2, 2, true))[1]==6

  @test length(genera((2,2), 10, even=true))==0  # check that a bug in catesian_product_iterator is fixed
  @test 4 == length(genera((4,0), 125, even=true))
  G = genus(diagonal_matrix(map(ZZ,[2, 4, 18])))
  @test 36 == level(G)
  G = genus(diagonal_matrix(map(ZZ,[2, 4, 18])))
  @test 2 == scale(G)
  @test 2 == norm(G)

  G = genus(diagonal_matrix(map(ZZ,[6, 4, 18])))
  @test norm(G) == 2
  @test sprint(show, G) isa String
  G = genus(matrix(ZZ, 2, 2, [0, 1, 1, 0]))
  @test norm(G) == 2


  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(2,3,1,2,false))
  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(2,5,4,4,true))
  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(3,2,2,2,true))
  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(3,3,4,4,true))
  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(5,2,2,2,true))

  A = diagonal_matrix(fmpz[2, -4, 6, 8])
  G = genus(A)
  q1 = discriminant_group(G)
  q2 = discriminant_group(Zlattice(gram=A))

  A = matrix(ZZ, 0, 0, [])
  g2 = genus(A, 2)
  g3 = genus(A, 3)
  g = genus(A)
  @test norm(g) == 0
  @test scale(g) == 0
  @test det(g) == 1
  @test rank(g) == 0
  @test level(g) == 1
  @test iseven(g)
  @test signature(g) == 0
  @test rank(representative(g))==0
  @test norm(g2) == 0
  @test scale(g2) == 0
  @test det(g2) == 1
  @test rank(g2) == 0
  @test iseven(g2)
  @test level(g2) == 1
  @test signature(g2) == 0
  @test excess(g2) == 0
  @test norm(g3) == 0
  @test scale(g3) == 0
  @test det(g3) == 1
  @test rank(g3) == 0
  @test signature(g3) == 0
  @test excess(g3) == 0
  @test rank(representative(g2))==0


  g3 = genus(diagonal_matrix(map(ZZ,[1,3,27])), 3)
  n3 = genus(matrix(ZZ,0,0,[]),3)
  @test g3 == orthogonal_sum(n3, g3)
  @test Hecke._species_list(g3) == [1, 1, 1]
  h3 = genus(diagonal_matrix(map(ZZ,[1,3,9])), 3)
  @test Hecke._standard_mass(h3) ==  9//16
  @test orthogonal_sum(g3,h3)==direct_sum(h3,g3)


  # These examples are taken from Table 2 of [CS1988]_::

  M_p = Hecke._M_p
  @test M_p(0, 2) == 1
  @test M_p(1, 2) == 1//2
  @test M_p(-2, 2) == 1//3
  @test M_p(2, 2) == 1
  @test M_p(3, 2) == 2//3
  @test M_p(-4, 2) == 8//15
  @test M_p(4, 2) == 8//9
  @test M_p(5, 2) == 32//45
  @test M_p(0, 3) == 1
  @test M_p(1, 3) == 1//2
  @test M_p(-2, 3) == 3//8
  @test M_p(2, 3) == 3//4
  @test M_p(3, 3) == 9//16
  @test M_p(-4, 3) == 81//160
  @test M_p(4, 3) == 81//128
  @test M_p(5, 3) == 729//1280
  @test M_p(0, 5) == 1
  @test M_p(1, 5) == 1//2
  @test M_p(-2, 5) == 5//12
  @test M_p(2, 5) == 5//8
  @test M_p(3, 5) == 25//48
  @test M_p(-4, 5) == 625//1248
  @test M_p(4, 5) == 625//1152

  A = diagonal_matrix(fmpz[1, 1, 1, 1])
  G = genus(A)
  @test Hecke._standard_mass_squared(G) == (1//48)^2

  @test Hecke._quadratic_L_function_squared(1, -4) == (1//4)^2
  @test Hecke._quadratic_L_function_squared(-4, -4) == (5//2)^2
  @test Hecke._quadratic_L_function_squared(2, 1) == (1//6)^2

  @test Hecke._zeta_exact(4)==1//90
  @test Hecke._zeta_exact(-3)==1//120
  @test Hecke._zeta_exact(0)==-1//2


  @test Hecke._gamma_exact(4)==6
  @test Hecke._gamma_exact(3)==2
  @test Hecke._gamma_exact(2)==1
  @test Hecke._gamma_exact(1)==1

  @test Hecke._gamma_exact(1//2)==1
  @test Hecke._gamma_exact(3//2)==1//2
  @test Hecke._gamma_exact(5//2)==3//4
  @test Hecke._gamma_exact(7//2)==15//8

  @test Hecke._gamma_exact(-1//2)==-2
  @test Hecke._gamma_exact(-3//2)==4//3
  @test Hecke._gamma_exact(-5//2)==-8//15
  @test Hecke._gamma_exact(-7//2)==16//105


  A = matrix(ZZ, 2, 2, [1, 1, 1, 2])
  G = genus(A)
  @test Hecke._isglobal_genus(G)
  G = genus(diagonal_matrix(fmpz[2, 2, 2, 2]))
  G._symbols[1]._symbol=[[0,2,3,0,0], [1,2,5,1,0]]
  @test !Hecke._isglobal_genus(G)


  L = Zlattice(gram=matrix(ZZ, 2, 2, [0, 1, 1, 0]))
  G = genus(L)
  g2 = genus(L, 2)
  g7 = genus(L, 7)
  @test local_symbol(G, 2) == g2
  @test local_symbol(G, 7) == g7
  q = discriminant_group(G) # corner case
  @test order(q) == 1
  L2 = Zlattice(gram=2*ZZ[2 1; 1 2])
  G2 = genus(L2)
  @test genus(orthogonal_sum(L,L2)[1]) == orthogonal_sum(G, G2)
  @test length(representatives(G2)) == 1

  G = genera((8,0), 1, even=true)[1]
  @test mass(G) == 1//696729600

  G = genus(diagonal_matrix(fmpz[1, 3, 9]),3)
  @test Hecke._mass_squared(G) == (9//8)^2

  # representatives, mass and genus enumeration
  DB = lattice_database()
  for i in 1:(long_test ? 200 : 10)
    L = lattice(DB,i)
    G = genus(L)
    q1 = quadratic_space(G)
    q2 = rational_span(L)
    @test Hecke.is_isometric(q1, q2)
    L2 = representative(G)
    G2 = genus(L2)
    @test G==G2
  end

  genus_orders_sage = [[1, 1], [1], [1, 1], [1, 1, 1, 1], [1, 1], [1, 1], [1, 1], [1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1], [1, 1], [1, 1, 1, 1], [1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 2], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 2], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 2, 2, 2, 2], [1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [2, 2], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 2, 2, 2, 2], [1, 2], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2], [1, 2], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 3, 3, 3, 3], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 2, 2, 2], [1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 2, 2], [2, 2], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 2, 2], [1, 2], [1, 1, 1, 1, 1, 1], [1, 2, 2, 2], [1, 1], [1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 2, 2], [1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 3, 3, 4, 4], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 2], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 2, 2], [1, 1, 1, 1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1], [1, 2], [1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2], [1, 2], [1, 1, 1, 1, 1, 1], [1, 1]]

  for d in 1:(long_test ? 199 : 50)
    L = [length(representatives(G)) for G in genera((1,1), d)]
    @test genus_orders_sage[d] == sort!(L)
  end


  # some randomly chosen unimodular matrices
  B = [ZZ[7 -4; 2 -1],
  matrix(ZZ,3,3,[1, 1, -4, 0, 1, -3, 0, -1, 4]),
  matrix(ZZ,4,4, [0, -4, -3, -1, 1, -2, -3, -1, -1, -1, 1, 0, 1, -2, -4, 1])]

  sigdet = []
  for d  in 1:(long_test ? 32 : 10)
    for sig in [(2,0), (1,1), (1,2),(4,0)]
      push!(sigdet, (sig, d))
    end
  end

  if long_test
    for sig in [(0,3), (1,2), (2,2)]
      push!(sigdet, (sig, 2^7))
    end
  end

  for (sig,d) in sigdet
    for G in genera(sig, d)
      L = representative(G)
      spL = ambient_space(L)
      b = B[rank(L)-1]
      spLt = quadratic_space(QQ, b*gram_matrix(L)*transpose(b))
      # Our is_isometric_with_isometry is too slow to handle the other cases
      if rank(L) <= 2
        flag, iso = Hecke.is_isometric_with_isometry(spL,spLt)
        @test flag
        @test iso*gram_matrix(spLt)*transpose(iso) == gram_matrix(spL)
      end
      if is_definite(L)
        # compare the two algorithms used to calculate the mass
        @test mass(L) == mass(G)
      end
      @test genus(L)==G
      D = discriminant_group(L)
      q1, _ = normal_form(D)
      q1 = Hecke.gram_matrix_quadratic(q1)
      q2 = discriminant_group(G)
      q2, _ = normal_form(q2)
      q2 = Hecke.gram_matrix_quadratic(q2)
      @test q1 == q2
      G2 = genus(D, sig)
      if iseven(G) == true
        @test is_genus(D, sig) == true
      end
      @test G == G2
      # test local representations
      if rank(L) >= 2
        diag = diagonal_matrix(fmpq[1, 2])*basis_matrix(L)[1:2,1:end]
        sub = lattice(ambient_space(L), diag)
        g = genus(sub)
        @test Hecke.represents(G, genus(sub))
      end
      if rank(L) >= 3
        diag = diagonal_matrix(fmpq[1, 2, 4])*basis_matrix(L)[1:3,1:end]
        sub = lattice(ambient_space(L), diag)
        g = genus(sub)
        @test Hecke.represents(G, genus(sub))
      end
      if rank(L) >= 3
        diag = diagonal_matrix(fmpq[4, 2, 2])*basis_matrix(L)[1:3,1:end]
        sub = lattice(ambient_space(L), diag)
        g = genus(sub)
        @test Hecke.represents(G, genus(sub))
      end
    end
  end

  for d in 1:(long_test ? 50 : 10)
    for sig in [(2,0),(3,0),(4,0)]
      for G in genera(sig,d)
        m = mass(G)
        L = representative(G)
        @test genus(L)==G
        @test mass(L)==m
        rep = genus_representatives(L)
        @test sum(1//automorphism_group_order(M) for M in rep)==m
         q = ambient_space(L)
         for r in rep
           qr = ambient_space(r)
           #b, i = Hecke.is_isometric_with_isometry(q,qr)
           @test is_isometric(q, qr)
           #@test b
           #@test i*gram_matrix(qr)*transpose(i) == gram_matrix(q)
         end
      end
    end
  end

end
