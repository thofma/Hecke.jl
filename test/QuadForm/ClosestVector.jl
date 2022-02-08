@testset "ClosestVector.jl" begin
  #=
  The quadratic triple QT = [Q, L, c] is an n-dimensional ellipsoid with rational coefficients.
  Where,
  Q is an nxn symmetric matrix of the quadratic form , 
  L is a rational column vector of length n &
  c is a rational number
  =#
  Q = matrix(QQ,3,3,[1 0 0; 0 1 0; 0 0 1]);
  L = matrix(fmpq[1,0,0]);
  c = fmpq(2//5);
  Lat = Zlattice(gram = matrix(QQ,3,3,[1,0,0,0,1,0,0,0,1]));
  v = matrix(fmpq[-1,0,0]);
  u = fmpq(3//5);
  @test Hecke.closest_vectors(Q, L,c, sorting=true)[1] == Hecke.closest_vectors(Lat, v, u, sorting=true)[1]

  function compare_functions(Q::MatrixElem{T}, K::MatrixElem{T}, d::T) where T <: RingElem
    List1 = Hecke.closest_vectors(Q, K, d, sorting=true);
    L, v, c = Hecke.convert_type(Q, K, d)
    List2 = Hecke.closest_vectors(L, v, c, sorting=true);
    for i in 1:length(List1)
      if List1[i] == List2[i]
        return true
      else
        error("The entry at position $i in the two lists don't match.")
      end
    end
  end

  function compare_functions(L::ZLat, v::MatrixElem{T} , upperbound::T) where T <: RingElem
    List1 = Hecke.closest_vectors(L, v, upperbound, sorting=true);
    Q, K, d = Hecke.convert_type(L, v, upperbound);
    List2 = Hecke.closest_vectors(Q, K, d, sorting=true);
    for i in 1:length(List1)
      if List1[i] == List2[i]
        return true
      else
        error("The entry at position $i in the two lists don't match.")
      end
    end
  end

  #EXAMPLE 1a: 3-dimensional sphere
  Q1 = matrix(QQ,3,3,[1 0 0; 0 1 0; 0 0 1]);
  L1 = matrix(fmpq[1,1,1]);
  c1 = fmpq(1);

  #EXAMPLE 1b: 4-dimensional sphere
  Q2 = matrix(QQ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
  L2 = matrix(fmpq[1,1,1,1]);
  c2 = fmpq(3);

  #EXAMPLE 1c: 6-dimensional sphere
  Q3 = matrix(QQ,6,6,[1 0 0 0 0 0; 0 1 0 0 0 0; 0 0 1 0 0 0; 0 0 0 1 0 0; 0 0 0 0 1 0; 0 0 0 0 0 1]);
  L3 = matrix(fmpq[1,0,1,0,2,0]);
  c3 = fmpq(4//3);

  #-----------------------------------------------------------------------------

  #Examples for closest_vectors()
  #Example 1:
  Lat1 = Zlattice(gram = matrix(QQ,3,3,[1,0,0,0,1,0,0,0,1]));
  v1 = matrix(fmpq[-1,0,0]);
  u1 = fmpq(3//5);

  #Example 1:
  Lat2 = Zlattice(gram = matrix(QQ,4,4,[1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1]));
  v2 = matrix(fmpq[-1,-1,-1,-1]);
  u2 = fmpq(41//11);

  #Example 1:
  Lat3 = Zlattice(gram = matrix(QQ,6,6,[1,0,0,0,0,0, 0,1,0,0,0,0, 0,0,1,0,0,0, 0,0,0,1,0,0, 0,0,0,0,1,0, 0,0,0,0,0,1]));
  v3 = matrix(fmpq[-1,0,-1,0,-2,0]);
  u3 = fmpq(14//3);

  @testset "Comparing closest_vectors(Q, K, d) to closest_vectors(Lat, vec, upperbound) list" begin
    @test compare_functions(Q1, L1, c1) == true
    @test compare_functions(Q2, L2, c2) == true
    @test compare_functions(Q3, L3, c3) == true
  end

  @testset "Comparing closest_vectors(Lat, vec, upperbound) list to closest_vectors(Q, K, d)" begin
    @test compare_functions(Lat1, v1, u1) == true
    @test compare_functions(Lat2, v2, u2) == true
    @test compare_functions(Lat3, v3, u3) == true
  end
  @testset "Comparing closest_vectors() computed with respect to type fmpz and fmpq" begin
    Q0 = matrix(ZZ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
    L0 = matrix(fmpz[1,1,1,1]);
    c0 = fmpz(3);
    @test compare_functions(Q0, L0, c0) == true

    Q01 = matrix(QQ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
    L01 = matrix(fmpq[1,1,1,1]);
    c01 = fmpq(3);
    @test compare_functions(Q01, L01, c01) == true
    
    List1 = Hecke.closest_vectors(Q0, L0, c0)
    List2 = Hecke.closest_vectors(Q01, L01, c01)
    for i in 1:length(List1)
      @test List1[i] == List2[i]
    end 
  end

  @testset "Conversion from Quadratic Triple set to Closest Vector Enumeration input parameters" begin
    Q3 = matrix(QQ,6,6,[1 0 0 0 0 0; 0 1 0 0 0 0; 0 0 1 0 0 0; 0 0 0 1 0 0; 0 0 0 0 1 0; 0 0 0 0 0 1]);
    L3 = matrix(fmpq[1,0,1,0,2,0]);
    c3 = fmpq(4//3);
    cvp = Hecke.convert_type(Q3,L3,c3);
    @test  det(basis_matrix(cvp[1])) == 1
    @test cvp[2] == matrix(fmpq[-1, 0, -1, 0, -2, 0])
    @test cvp[3] == 14//3
  end
    
  @testset "Conversion from Closest Vector Enumeration to Quadratic Triple set input parameters" begin
    Lat = Zlattice(gram = matrix(QQ,3,3,[1,0,0,0,1,0,0,0,1]));
    vec = matrix(fmpq[-1,-1,-1]);
    upbound = fmpq(2);
    qt = Hecke.convert_type(Lat, vec, upbound);
    @test qt[1] == matrix(QQ,3,3,[1 0 0; 0 1 0; 0 0 1])
    @test qt[2] == matrix(fmpq[1,1,1])
    @test qt[3] == 1
  end

  @testset "Quadratic Triple Tests" begin
    @testset "Projective Quadratic Triple" begin
      Q = matrix(QQ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
      L = matrix(fmpq[1,1,1,1]);
      c = fmpq(3);          
      @test Hecke.projective_quadratic_triple(Q, L, c, 1) == (Q[1, 1], L[1], 0)
      @test Hecke.projective_quadratic_triple(Q, L, c, 4) == (Q, L, c)
    end

    @testset "Finite set of integers for a 1-dimensional quadratic triple" begin
      Q = matrix(QQ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
      L = matrix(fmpq[1,1,1,1]);
      c = fmpq(3);
      Q1 = Hecke.projective_quadratic_triple(Q, L, c, 1)[1];
      L1 = Hecke.projective_quadratic_triple(Q, L, c, 1)[2];
      c1 = Hecke.projective_quadratic_triple(Q, L, c, 1)[3];
      @test Hecke.range_ellipsoid_dim1(Q1, L1, c1) == -2:0
    end

    @testset "Different Types of Extended Quadratic Triple" begin
      @testset "Quadratic triple extension from a 1-dimensional quadratic triple" begin
        Q = matrix(QQ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
        L = matrix(fmpq[1,1,1,1]);
        c = fmpq(3);
        @test Hecke.positive_quadratic_triple(fmpz(1), Q, L, c)[1] == Q[2:4, 2:4]
        @test Hecke.positive_quadratic_triple(fmpz(1), Q, L, c)[2] == L[2:4, 1:1]
        @test Hecke.positive_quadratic_triple(fmpz(1), Q, L, c)[3] == 6
      end

      @testset "Quadratic triple extension from a m-dimensional quadratic triple to m+n-1 quadratic triple" begin
        Q = matrix(QQ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
        L = matrix(fmpq[1,1,1,1]);
        c = fmpq(3);
        @test Hecke.positive_quadratic_triple2(fmpz[-2,0,1], Q,L,c)[1][1] == 1  
        @test Hecke.positive_quadratic_triple2(fmpz[-2,0,1], Q,L,c)[2][1] == 1
        @test Hecke.positive_quadratic_triple2(fmpz[-2,0,1], Q,L,c)[3] == 6
      end
    end 
  end

  @testset "Finite set tests" begin
    Q = matrix(QQ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
    Q1 = -Q;
    L = matrix(fmpq[1,1,1,1]);
    c = fmpq(3);
    @test Hecke.closest_vectors(Q, L, c, sorting=true)[1] == [-2, -1, -1, -1]
    @test size(Hecke.closest_vectors(Q, L, c), 1) == 9 
    @test Hecke.closest_vectors(Q, L, c, sorting=true)[1] == Hecke.closest_vectors(Q1,L,c, sorting=true)[1]

    @test Hecke.closest_vectors(Q, L, c, equal=true, sorting=true)[1] == [-2, -1, -1, -1]
    @test size(Hecke.closest_vectors(Q, L, c, equal=true), 1) == 8 
    @test Hecke.closest_vectors(Q, L, c, equal=true, sorting=true)[1] == Hecke.closest_vectors(Q1,L,c, sorting=true)[1]
    

    L1, L2, L3 = Hecke.convert_type(Q,L,c)
    @test Hecke.closest_vectors(L1, L2, L3, sorting=true)[1] == Hecke.closest_vectors(Q, L, c, sorting=true)[1]
    @test size(Hecke.closest_vectors(L1, L2, L3), 1) == size(Hecke.closest_vectors(Q, L, c), 1)
    @test Hecke.closest_vectors(L1, L2, L3, equal=true, sorting=true)[1] == Hecke.closest_vectors(Q, L, c, equal=true, sorting=true)[1]
    @test size(Hecke.closest_vectors(L1, L2, L3, equal=true), 1) == size(Hecke.closest_vectors(Q, L, c, equal=true), 1)
    t = Hecke.closest_vectors(L1, L2, L3, equal=true)
    L21 = Vector{typeof(L2[1])}()
    for i1 in L2
      push!(L21, i1)
    end
    for i in 1:size(t)[1]
      @test inner_product(ambient_space(L1), L21-t[i], L21-t[i]) == L3
    end

    x = matrix(QQ, 4, 1, Hecke.closest_vectors(Q, L, c)[5]);
    xt = transpose(matrix(QQ, 4, 1, Hecke.closest_vectors(Q, L, c)[5]));
    R = (xt * Q * x)[1] + (2 * xt * L)[1] + c;
    @test  R <= 0 

    y = matrix(QQ, 4, 1, Hecke.closest_vectors(Q1, L, c)[5]);
    yt = transpose(matrix(QQ, 4, 1, Hecke.closest_vectors(Q1, L, c)[5]));
    S = (yt * Q * y)[1] + (2 * yt * L)[1] + c;
    @test  S <= 0 
  end
end
