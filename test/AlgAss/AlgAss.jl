function test_alg_morphism_char_0(A, B, AtoB)
  @test iszero(AtoB(zero(A)))
  @test iszero(AtoB\(zero(B)))
  @test isone(AtoB(one(A)))
  @test isone(AtoB\(one(B)))

  for i = 1:5
    c = rand(A, -10:10)
    d = rand(A, -10:10)
    @test AtoB\(AtoB(c)) == c
    @test AtoB\(AtoB(d)) == d
    @test AtoB(c + d) == AtoB(c) + AtoB(d)
    @test AtoB(c*d) == AtoB(c)*AtoB(d)

    e = rand(B, -10:10)
    f = rand(B, -10:10)
    @test AtoB(AtoB\(e)) == e
    @test AtoB(AtoB\(f)) == f
    @test AtoB\(e + f) == (AtoB\(e)) + (AtoB\(f))
    @test AtoB\(e*f) == (AtoB\(e)) * (AtoB\(f))
  end
end

function test_alg_morphism_char_p(A, B, AtoB)
  @test iszero(AtoB(zero(A)))
  @test iszero(AtoB\(zero(B)))
  @test isone(AtoB(one(A)))
  @test isone(AtoB\(one(B)))

  for i = 1:5
    c = rand(A)
    d = rand(A)
    @test AtoB\(AtoB(c)) == c
    @test AtoB\(AtoB(d)) == d
    @test AtoB(c + d) == AtoB(c) + AtoB(d)
    @test AtoB(c*d) == AtoB(c)*AtoB(d)

    e = rand(B)
    f = rand(B)
    @test AtoB(AtoB\(e)) == e
    @test AtoB(AtoB\(f)) == f
    @test AtoB\(e + f) == AtoB\(e) + AtoB\(f)
    @test AtoB\(e*f) == (AtoB\(e))*(AtoB\(f))
  end
end

@testset "Associative algebras" begin

  # creation

  @test_throws ArgumentError associative_algebra(QQ, map(QQ, reshape([1 2 1 2; 1 2 1 2], 2, 2, 2)))

  @testset "Change of ring" begin

    # Restrict from number field to Q
    Qx, x = FlintQQ["x"]
    f = x^3 - 2
    K, a = number_field(f, "a")

    A = StructureConstantAlgebra(matrix_ring(K, 2))
    B, BtoA = Hecke.restrict_scalars(A, FlintQQ)
    @test base_ring(B) == FlintQQ
    @test dim(B) == dim(A)*degree(K)

    test_alg_morphism_char_0(B, A, BtoA)

    # Extend to K again
    C, CtoB = Hecke._as_algebra_over_center(B)
    @test is_isomorphic(K, base_ring(C))
    @test dim(C) == dim(A)

    test_alg_morphism_char_0(C, B, CtoB)

    # Restrict from number field to number field
    g = x^9 - 15x^6 - 87x^3 - 125
    L, b = number_field(g, "b")
    KtoL = hom(K, L, -2//45*b^7 + 7//9*b^4 + 109//45*b)

    A = StructureConstantAlgebra(matrix_ring(L, 2))
    B, BtoA = Hecke.restrict_scalars(A, KtoL)

    @test base_ring(B) == K
    @test dim(B) == dim(A)*div(degree(L), degree(K))

    test_alg_morphism_char_0(B, A, BtoA)

    # Restrict from F_q to F_p
    Fp = GF(7)
    Fq, a = finite_field(7, 3, "a")

    A = StructureConstantAlgebra(matrix_ring(Fq, 2))
    B, BtoA = Hecke.restrict_scalars(A, Fp)
    @test base_ring(B) == Fp
    @test dim(B) == dim(A)*degree(K)

    test_alg_morphism_char_p(B, A, BtoA)

    # Extend to Fq again
    C, CtoB = Hecke._as_algebra_over_center(B)
    @test characteristic(base_ring(C)) == characteristic(Fq)
    @test degree(base_ring(C)) == degree(Fq)
    @test dim(C) == dim(A)

    test_alg_morphism_char_p(C, B, CtoB)

    # Extend from F_p^m to F_p^n
    Fqx, x = Fq["x"]
    f = x^2 + 5x + 2
    A = associative_algebra(f)
    B, BtoA = Hecke._as_algebra_over_center(A)
    @test characteristic(base_ring(B)) == characteristic(Fq)
    @test absolute_degree(base_ring(B)) == degree(f)*degree(Fq)
    @test dim(B) == 1

    test_alg_morphism_char_p(B, A, BtoA)

    Fp = GF(3)
    mt = Array{elem_type(Fp), 3}(undef, 2, 2, 2)
    mt[1, 1, 1] = Fp(0)
    mt[1, 1, 2] = Fp(2)
    mt[1, 2, 1] = Fp(2)
    mt[1, 2, 2] = Fp(1)
    mt[2, 1, 1] = Fp(2)
    mt[2, 1, 2] = Fp(1)
    mt[2, 2, 1] = Fp(1)
    mt[2, 2, 2] = Fp(1)
    A = associative_algebra(Fp, mt)
    B, BtoA = Hecke._as_algebra_over_center(A)
    @test characteristic(base_ring(B)) == characteristic(Fp)
    @test degree(base_ring(B)) == dim(A)
    @test dim(B) == 1

    test_alg_morphism_char_p(B, A, BtoA)

    # zero algebra

    A = associative_algebra(QQ, Array{QQFieldElem}(undef, 0, 0, 0))
    @test dim(A) == 0
    A = associative_algebra(QQ, Array{QQFieldElem}(undef, 0, 0, 0), QQFieldElem[])
    @test dim(A) == 0
  end

  # n = dim(A)^2 = dim(B)^2
  function test_mat_alg_morphism(AtoB::Hecke.AbsAlgAssMor, n::Int)
    A = domain(AtoB)
    B = codomain(AtoB)

    test_alg_morphism_char_p(A, B, AtoB)

    sum_of_diag = AtoB\B[1]
    for i = 2:n
      sum_of_diag += AtoB\B[(i - 1)*n + i]
    end
    @test isone(sum_of_diag)

    # B[i + (j - 1)*n]*B[k + (l - 1)*n] == B[i + (l - 1)*n], if j == k, and 0, otherwise
    for j = 1:n
      jN = (j - 1)*n
      for i = 1:n
        ji = jN + i
        for l = 1:n
          lN = (l - 1)*n
          for k = 1:n
            if j == k
              @test AtoB\(B[ji]*B[k + lN]) == AtoB\B[i + lN]
            else
              @test iszero(AtoB\(B[ji]*B[k + lN]))
            end
          end
        end
      end
    end
  end

  @testset "Matrix Algebra" begin
    Fp = GF(7)
    Fq, a = finite_field(7, 2, "a")

    A = StructureConstantAlgebra(matrix_ring(Fq, 3))
    B, AtoB = Hecke._as_matrix_algebra(A)
    @test dim(B) == dim(A)

    test_mat_alg_morphism(AtoB, 3)

    G = SymmetricGroup(4)
    A = StructureConstantAlgebra(GroupAlgebra(Fp, G))[1]
    Adec = Hecke.decompose(A)

    i = 2
    B = Adec[1][1]
    while dim(B) != 9
      B = Adec[i][1]
      i += 1
    end

    C, BtoC = Hecke._as_matrix_algebra(B)

    test_mat_alg_morphism(BtoC, 3)

    i = 2
    B = Adec[1][1]
    while dim(B) != 4
      B = Adec[i][1]
      i += 1
    end

    C, BtoC = Hecke._as_matrix_algebra(B)

    test_mat_alg_morphism(BtoC, 2)
  end

  @testset "Splitting at infinite place" begin
    G = small_group(8, 4)
    Qx, x = polynomial_ring(FlintQQ, "x")
    K, a = number_field(x - 1, "a")
    A = Hecke.GroupAlgebra(K, G)
    H = first(c[1] for c in Hecke.decompose(A) if dim(c[1]) == 4)
    P = infinite_places(K)[1]
    @test !is_split(H, P)

    K, a = number_field(x - 1, "a")
    A = Hecke.GroupAlgebra(K, G)
    H = first(c[1] for c in Hecke.decompose(A) if dim(c[1]) == 1)
    P = infinite_places(K)[1]
    @test is_split(H, P)

    K, a = number_field(x^2 - 2, "a")
    HH = Hecke.quaternion_algebra2(2, 3)
    A = associative_algebra(K, map(K, HH.mult_table))
    Ps = real_places(K)
    @test is_split(A, Ps[1])
    @test is_split(A, Ps[2])
  end

  A = zero_algebra(QQ)
  @test_throws ArgumentError direct_product(typeof(A)[])
end
