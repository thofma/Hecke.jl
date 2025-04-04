@testset "ZZGenus" begin
  A = matrix(ZZ, 2, 2, [1, 1, 1, 1])
  @test (false, 1) == Hecke._iseven(A)
  A = matrix(ZZ, 2, 2, [2, 1, 1, 2])
  @test (true, -1) == Hecke._iseven(A)
  @test iseven(genus(A))
  A = matrix(QQ, 1, 2, [1 3])
  @test_throws ArgumentError genus(A)
  @test_throws ArgumentError genus(A, 3)
  A = matrix(QQ, 2, 2, [1 1; 1 1])
  @test_throws ArgumentError genus(A)
  @test_throws ArgumentError genus(A, 3)
  A = matrix(QQ, 2, 2, [1 3; 2 0])
  @test_throws ArgumentError genus(A)
  @test_throws ArgumentError genus(A, 3)

  A = matrix(ZZ, 2, 2, [1, 2, 2, 3])
  @test (false, 1) == Hecke._iseven(A)
  @test (1, ZZ[-1;]) == Hecke._split_odd(A)

  @test length(unique!([genus(A), genus(A)]))==1
  @test length(unique!([genus(A, 2), genus(A, 2)]))==1

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
  g1 = ZZLocalGenus(2,[[0, 2, 7, 0, 0], [3, 1, 7, 1, 7]])
  g2 = ZZLocalGenus(2,[[0, 2, 3, 0, 0], [3, 1, 3, 1, 3]])
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
  @test G != rescale(G, -1)

  output =[[15, 2, 3, 0, 0],
         [15, 2, 7, 0, 0],
         [15, 2, 1, 1, 2],
         [15, 2, 5, 1, 6],
         [15, 2, 1, 1, 6],
         [15, 2, 5, 1, 2],
         [15, 2, 7, 1, 0],
         [15, 2, 3, 1, 4]]
  @test output == Hecke._blocks([15, 2, 0, 0, 0])

  @test size(Hecke._local_genera(2, 3, 1, 0, 2, false))[1]==12
  @test size(Hecke._local_genera(2, 3, 1, 0, 2, true))[1]==4
  @test size(Hecke._local_genera(5, 2, 2, 0, 2, true))[1]==6

  @test length(integer_genera((2,2), 10, even=true))==0  # check that a bug in catesian_product_iterator is fixed
  @test 4 == length(integer_genera((4,0), 125, even=true))
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


  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(2,3,1,0,2,false))
  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(2,5,4,0,4,true))
  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(3,2,2,0,2,true))
  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(3,3,4,0,4,true))
  @test all(hasse_invariant(g) == hasse_invariant(ambient_space(representative(g)),prime(g)) for g in Hecke._local_genera(5,2,2,0,2,true))

  A = diagonal_matrix(ZZRingElem[2, -4, 6, 8])
  G = genus(A)
  q1 = discriminant_group(G)
  q2 = discriminant_group(integer_lattice(gram=A))

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
  n5 = genus(matrix(ZZ,0,0,[]),5)
  @test g3 == direct_sum(n3, g3)
  @test_throws ArgumentError direct_sum(n3, n5)
  @test n3 == direct_sum(n3, n3)
  @test Hecke._species_list(g3) == [1, 1, 1]
  h3 = genus(diagonal_matrix(map(ZZ,[1,3,9])), 3)
  @test Hecke._standard_mass(h3) ==  9//16
  @test direct_sum(g3,h3)==direct_sum(h3,g3)


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

  A = diagonal_matrix(ZZRingElem[1, 1, 1, 1])
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
  G = genus(diagonal_matrix(ZZRingElem[2, 2, 2, 2]))
  G._symbols[1]._symbol=[[0,2,3,0,0], [1,2,5,1,0]]
  @test !Hecke._isglobal_genus(G)


  L = integer_lattice(gram=matrix(ZZ, 2, 2, [0, 1, 1, 0]))
  G = genus(L)
  g2 = genus(L, 2)
  g7 = genus(L, 7)
  @test local_symbol(G, 2) == g2
  @test local_symbol(G, 7) == g7
  q = discriminant_group(G) # corner case
  @test order(q) == 1
  L2 = integer_lattice(gram=2*ZZ[2 1; 1 2])
  G2 = genus(L2)
  @test genus(direct_sum(L,L2)[1]) == direct_sum(G, G2)
  @test length(representatives(G2)) == 1
  @test representative(G2)===representative(G2) # caching

  G = integer_genera((8,0), 1, even=true)[1]
  @test mass(G) == 1//696729600

  G = genus(diagonal_matrix(ZZRingElem[1, 3, 9]),3)
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
    L = [length(representatives(G)) for G in integer_genera((1,1), d)]
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
    for G in integer_genera(sig, d)
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
        diag = diagonal_matrix(QQFieldElem[1, 2])*basis_matrix(L)[1:2,1:end]
        subL = lattice(ambient_space(L), diag)
        g = genus(subL)
        @test represents(G, g)
      end
      if rank(L) >= 3
        diag = diagonal_matrix(QQFieldElem[1, 2, 4])*basis_matrix(L)[1:3,1:end]
        subL = lattice(ambient_space(L), diag)
        g = genus(subL)
        @test represents(G, g)

        diag = diagonal_matrix(QQFieldElem[4, 2, 2])*basis_matrix(L)[1:3,1:end]
        subL = lattice(ambient_space(L), diag)
        g = genus(subL)
        @test represents(G, g)
      end
    end
  end

  for d in 1:(long_test ? 50 : 10)
    for sig in [(2,0),(3,0),(4,0)]
      for G in integer_genera(sig,d)
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


  # primes
  G = genus(root_lattice(:E, 7))
  lis = @inferred primes(G)
  @test lis == ZZRingElem[2]

  G = genus(hyperbolic_plane_lattice(2*3*5*7*37))
  lis = @inferred primes(G)
  @test lis == ZZRingElem[2,3,5,7,37]

  # primary and elementary

  L = integer_lattice(gram=matrix(ZZ, [[2, -1, 0, 0, 0, 0],[-1, 2, -1, -1, 0, 0],[0, -1, 2, 0, 0, 0],[0, -1, 0, 2, 0, 0],[0, 0, 0, 0, 6, 3],[0, 0, 0, 0, 3, 6]]))
  Lr = root_sublattice(L) #this is D4
  Ls = orthogonal_submodule(L, Lr)
  G = genus(L)
  Gr = genus(Lr)
  Gs = genus(Ls)
  @test !is_primary_with_prime(G)[1]
  @test is_elementary(Gr, 2)
  bool, p = @inferred is_primary_with_prime(Gs)
  @test bool && !is_elementary(Gs, p)

  for i in [6,7,8]
    L = root_lattice(:E, i)
    G = genus(L)
    @test is_elementary(G, 9-i)
    @test i != 8 || is_unimodular(G)
  end
  G = [genus(root_lattice(:D, j)) for j in [4,5,6,7]]
  @test all(g -> is_primary(g, 2), G)
  @test all(g -> !is_unimodular(g), G)
  j = any(g -> !is_elementary(g,2), G)
  @test j !== nothing

end

@testset "spinor genus" begin
  # The following examples are given in
  # [CS99] 3rd edition, Chapter 15, 9.6 pp. 392

  A = diagonal_matrix(QQFieldElem[3, 16])
  G = genus(A)
  sym2 = local_symbols(G)[1]
  @test automorphous_numbers(sym2) == [3, 5]

  A = integer_lattice(gram=ZZ[2 1 0; 1 2 0; 0 0 18])
  G = genus(A)
  sym = local_symbols(G)
  @test automorphous_numbers(sym[1]) == [1, 3, 5, 7]
  @test automorphous_numbers(sym[2]) == [1, 3]

  # Note that the generating set given is not minimal.
  # The first supplementation rule is used here::

  A = diagonal_matrix(QQFieldElem[2, 2, 4])
  G = genus(A)
  sym = local_symbols(G)
  @test automorphous_numbers(sym[1]) == [1, 2, 3, 5, 7]

  # but not there::

  A = diagonal_matrix(QQFieldElem[2, 2, 32])
  G = genus(A)
  sym = local_symbols(G)
  @test automorphous_numbers(sym[1]) == [1, 2, 5]

  # Here the second supplementation rule is used::

  A = diagonal_matrix(QQFieldElem[2, 2, 64])
  G = genus(A)
  sym = local_symbols(G)
  @test automorphous_numbers(sym[1]) == [1, 2, 5]

  L1 = integer_lattice(gram=ZZ[6 3 0; 3 6 0; 0 0 2])
  g = genus(L1)
  # two classes in the improper spinor genus
  @test length(Hecke.proper_spinor_generators(g))==1
  @test !is_automorphous(g, 5)

  M1 = matrix(ZZ, 4, 4, [3,0,-1,1,0,3,-1,-1,-1,-1,6,0,1,-1,0,6])
  L1 = integer_lattice(gram=M1)
  g = genus(L1)
  @test Hecke.proper_spinor_generators(g) == [3]
  @test Hecke.improper_spinor_generators(g) == [] # unique in genus


 L = [ZZ[1 0 0 0; 0 32 0 4; 0 0 16 0; 0 4 0 1],
  ZZ[16 0 8 12; 0 32 24 20; 8 24 23 21; 12 20 21 22],
  ZZ[36 18 33 3; 18 36 39 24; 33 39 50 22; 3 24 22 20],
  ZZ[4 2 3 1; 2 4 3 2; 3 3 12 6; 1 2 6 10],
  ZZ[1 0 0 0; 0 128 0 8; 0 0 16 0; 0 8 0 1],
  ZZ[64 0 32 0; 0 2 0 1; 32 0 32 0; 0 1 0 1],
  ZZ[64 32 48 40; 32 48 32 40; 48 32 39 35; 40 40 35 38],
  ZZ[16 12 0 0; 12 11 0 0; 0 0 16 4; 0 0 4 3]]
 L = [integer_lattice(gram=g) for g in L]
 G = [genus(i) for i in L]
 @test [length(Hecke.proper_spinor_generators(i)) == length(Hecke.improper_spinor_generators(i)) for i in G] == [1,0,1,0,1,1,0,0]

end

@testset "non integral genera" begin
  # Rescaling
  L = root_lattice(:D, 7)
  G = genus(L)
  G2 = @inferred rescale(G, -2)
  @test genus(rescale(L, -2)) == G2
  @test signature_pair(G2) == reverse(signature_pair(G))
  @test det(G2) == (-2)^7*det(G)
  @test scale(G2) == 2*scale(G)
  @test rescale(G2, -1//2) == G
  G3 = @inferred rescale(G2, 3//5)
  @test scale(G3) == 6//5
  @test rescale(G3, -5//6) == G
  @test_throws ArgumentError rescale(G, ZZ(0))
  @test_throws ArgumentError rescale(G, QQ(0))

  # Printing
  G = genus(rescale(root_lattice(:E, 8), 1//(2*3*5*7*11*13*17)))
  @test sprint(show, G) isa String

  # Representative
  L = hyperbolic_plane_lattice(4)
  G = genus(L)
  G2 = rescale(G, -1//15)
  L2 = representative(G2)
  @test genus(L2) == G2
  @test G2 == genus(hyperbolic_plane_lattice(-4//15))
  @test genus(rescale(L2, -15)) == G
  L = root_lattice(:A, 4)
  G = genus(L)
  G2 = rescale(G, -1//13)
  G22 = direct_sum(G2, G)
  L2 = representative(G22)
  @test genus(L2) == G22
  G = integer_genera((0,8), 1)[1]
  G2 = rescale(G, -5)
  G3 = rescale(G, 7//92)
  G4 = rescale(G, -1//10000009)
  L = representative(G)
  @test genus(rescale(L, -5)) == G2
  @test genus(rescale(L, 7//92)) == G3
  @test genus(rescale(L, -1//10000009)) == G4

  # Representatives
  L = root_lattice(:A, 8)
  L2 = rescale(L, -1//8)
  repL = genus_representatives(L)
  repL2 = genus_representatives(L2)
  @test all(LL -> genus(LL) == genus(L2), repL2)
  @test length(repL) == length(repL2) == 2
  @test all(LL -> genus(rescale(LL, -8)) == genus(L), repL2)
  @test !is_isometric(repL2[1], repL2[2])

  # Enumeration
  gen = @inferred integer_genera((1, 1), 4//3, min_scale = 1//18, max_scale = 12)
  @test length(gen) == 8
  @test all(g -> det(g) == -4//3, gen)
  @test all(g -> !is_integral(g), gen)
  @test all(g -> scale(g) in [1//9, 1//3, 2//9, 2//3], gen)
  gen = @inferred integer_genera((1, 1), 4//3, min_scale = 1//18, max_scale = 12, even = true)
  @test isempty(gen)
  @test_throws ArgumentError integer_genera((1,1), 4//3, min_scale = -1//18)
  @test_throws ArgumentError integer_genera((1,1), 4//3, max_scale = -12)
  gen1 = @inferred integer_genera((0,8), 5, even = true)
  @test length(gen1) == 1
  gen2 = @inferred integer_genera((0, 8), 5, min_scale = 1//5, even = true)
  @test length(gen2) == 1
  @test gen1 == gen2
  gen3 = integer_genera((0,8), 5)
  gen4 = integer_genera((0, 8), 5, min_scale = 1//5)
  @test all(g -> g in gen4, gen3)
  @test all(g -> g in gen4, gen2)
  @test isempty(integer_genera((0, 8), 1, min_scale = 2))
  gen = @inferred integer_genera((0,8), 1, min_scale = 1//2, max_scale = 4)
  @test length(gen) == 53
  @test !isempty(integer_genera((4,0), 5; min_scale=1, max_scale=15, even=true))

  # Mass
  gen = integer_genera((0,8), 16, even=true)
  for g in gen
    k = rand(-50:50)
    while k == 0
      k = rand(-50:50)
    end
    g2 = rescale(g, 1//k)
    @test mass(g) == mass(g2)
  end

  # Discriminant group
  G = genus(rescale(root_lattice(:A, 1), 1//3))
  @test_throws ArgumentError discriminant_group(G)

  # Represents
  for k in 1:10
    n = rand(4:50)
    S = rand([:A, :D])
    L = root_lattice(S, n)
    G = genus(L)
    G2 = genus(dual(L))
    @test represents(G2, G)
    @test !represents(G, G2)
  end

  # Spinor genera
  M1 = matrix(ZZ, 4, 4, [3,0,-1,1,0,3,-1,-1,-1,-1,6,0,1,-1,0,6])
  L = integer_lattice(gram = M1)
  G = genus(L)
  G2 = rescale(G, 8//109)
  @test_throws ArgumentError Hecke.automorphous_numbers(local_symbol(G2, 109))
  @test_throws ArgumentError Hecke.is_automorphous(G2, 6)
  @test Hecke.improper_spinor_generators(G) == Hecke.improper_spinor_generators(G2)
  @test Hecke.proper_spinor_generators(G) == Hecke.proper_spinor_generators(G2)

end

@testset "Fix issues" begin
  ## Issue 1103
  @test sprint(show, "text/plain", genus(root_lattice(:E, 8), 2)) isa String
end
