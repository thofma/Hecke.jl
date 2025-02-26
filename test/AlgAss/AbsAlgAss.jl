@testset "AbstractAssociativeAlgebra" begin

  @testset "Decomposition" begin
    Fp = GF(3)
    G = small_group(8, 4)
    FpG = group_algebra(Fp, G)

    dec = decompose(FpG)
    @test length(dec) == 5
    dim1 = 0
    dim4 = 0
    for (A, toFpG) in dec
      if dim(A) == 1
        dim1 += 1
      elseif dim(A) == 4
        dim4 += 1
      end
    end
    @test dim1 == 4
    @test dim4 == 1

    # Check whether the maps "work"
    A, toFpG = dec[1]
    e = toFpG(one(A))
    @test e^2 == e
    ee = toFpG\one(FpG)
    @test ee^2 == ee

    # And now the same for StructureConstantAlgebra
    FpG = StructureConstantAlgebra(FpG)[1]
    dec = decompose(FpG)
    @test length(dec) == 5
    dim1 = 0
    dim4 = 0
    for (A, toFpG) in dec
      if dim(A) == 1
        dim1 += 1
      elseif dim(A) == 4
        dim4 += 1
      end
    end
    @test dim1 == 4
    @test dim4 == 1

    # Check whether the maps "work"
    A, toFpG = dec[1]
    e = toFpG(one(A))
    @test e^2 == e
    ee = toFpG\one(FpG)
    @test ee^2 == ee

    # And now for MatAlgebra
    A = matrix_algebra(Fp, 2)

    dec = decompose(A)
    @test length(dec) == 1

    B, BtoA = dec[1]
    @test dim(B) == 4

    e = BtoA(one(B))
    @test e^2 == e
    ee = BtoA\one(A)
    @test ee^2 == ee

    A = matrix_algebra(Fp, [ matrix(Fp, [ 1 1; 0 1 ]) ]) # not semisimple!
    @test_throws AssertionError decompose(A)

    Qx, x = QQ["x"]
    A = StructureConstantAlgebra((x^2 + 1)*(x^2 + 3))
    dec = Hecke.as_number_fields(A)

    @test length(dec) == 2
    @test degree(dec[1][1]) == 2
    @test degree(dec[2][1]) == 2

    K, AtoK = dec[1]
    e = AtoK(one(A))
    @test e^2 == e
    ee = AtoK\one(K)
    @test ee^2 == ee
  end

  @testset "Generators" begin
    Qx, x = QQ["x"]
    A = StructureConstantAlgebra((x^2 + 1)*(x^2 + 3))
    g, full_basis, v = gens_with_data(A)

    @test length(full_basis) == dim(A)

    M = zero_matrix(QQ, dim(A), dim(A))
    for i = 1:dim(A)
      Hecke.elem_to_mat_row!(M, i, full_basis[i])
    end
    @test rank(M) == dim(A)

    for i = 1:dim(A)
      b = full_basis[i]
      a = one(A)
      for (j, k) in v[i]
        a *= g[j]^k
      end
      @test b == a
    end
  end

  @testset "Radical" begin
    Qx, x = QQ["x"]
    # f = x^2 + 1
    # g = x^3 + 3x^2 + 5x - 5
    f2g3 = x^13 + 9x^12 + 44x^11 + 120x^10 + 205x^9 + 153x^8 + 32x^7 - 168x^6 - 5x^5 - 485x^4 + 500x^3 - 400x^2 + 375x - 125 # = f^2*g^3
    A = StructureConstantAlgebra(f2g3)
    fg = A(QQFieldElem[-5, 5, -2, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0]) # = f*g
    J = radical(A)
    I = left_ideal(A, fg)
    @test I == J

    f = x^2 + 1
    K, a = number_field(f, "a")
    Ky, y = K["y"]
    # g = y^3 - 3y^2 - 3y + 2
    # h = y^2 + 5y + 5
    g2h3 = y^12 + 9y^11 + 3y^10 - 198y^9 - 603y^8 + 423y^7 + 4829y^6 + 8430y^5 + 4335y^4 - 2675y^3 - 3075y^2 + 500 # = g^2*h^3
    A = StructureConstantAlgebra(g2h3)
    gh = A(map(K, [10, -5, -28, -13, 2, 1, 0, 0, 0, 0, 0, 0])) # = g*h
    J = radical(A)
    I = left_ideal(A, gh)
    @test I == J

    G = small_group(8, 4)
    F2 = GF(2)
    A = group_algebra(F2, G)
    I = radical(A)
    bI = F2[1 0 0 0 0 0 0 1;
            0 1 0 0 0 0 0 1;
            0 0 1 0 0 0 0 1;
            0 0 0 1 0 0 0 1;
            0 0 0 0 1 0 0 1;
            0 0 0 0 0 1 0 1;
            0 0 0 0 0 0 1 1]
    @test I == Hecke._ideal_from_matrix(A, bI)
    ge = [A(g) - A(one(G)) for g in G]
    @test all(in(I), ge)
    AS, AStoA = StructureConstantAlgebra(A)
    I = radical(AS)
    @test all(in(I), preimage.(Ref(AStoA), ge))

    F3 = GF(3)
    A = group_algebra(F3, G)
    I = radical(A)
    @test is_zero(I)

    F4 = GF(2, 2)
    A = group_algebra(F4, G)
    I = radical(A)
    ge = [A(g) - A(one(G)) for g in G]
    @test all(in(I), ge)
    AS, AStoA = StructureConstantAlgebra(A)
    I = radical(AS)
    @test all(in(I), preimage.(Ref(AStoA), ge))

    A = group_algebra(QQ, G)
    I = radical(A)
    @test nrows(basis_matrix(I, copy = false)) == 0

    for K in [ F2, F4, QQ ]
      A = matrix_algebra(K, [ matrix(K, 2, 2, [ 1, 0, 0, 0 ]), matrix(K, 2, 2, [ 0, 1, 0, 0 ]), matrix(K, 2, 2, [ 0, 0, 0, 1]) ]) # i. e. upper triangular matrices
      I = radical(A)
      @test nrows(basis_matrix(I, copy = false)) == 1
    end
  end

  @testset "rand" begin
    Fp = GF(3)
    G = small_group(8, 4)
    FpG = group_algebra(Fp, G)
    A = StructureConstantAlgebra(FpG)[1]
    @assert A isa Hecke.AbstractAssociativeAlgebra

    E = elem_type(A)
    @test rand(A) isa E
    @test rand(rng, A) isa E
    @test rand(A, 2, 3) isa Matrix{E}

    Random.seed!(rng, rand_seed)
    a = rand(rng, A)
    Random.seed!(rng, rand_seed)
    @test a == rand(rng, A)
  end

  K, a = quadratic_field(2)
  A = matrix_algebra(K, 3)
  Ares, = restrict_scalars(A, QQ)
  @test (@inferred Hecke.dimension_of_center(Ares)) == 2
  @test (@inferred Hecke.dimension_over_center(Ares)) == 9
  @test (@inferred Hecke.degree_as_central_simple_algebra(Ares)) == 3

  G = small_group(5, 1);
  QG = QQ[G];
  idems = @inferred central_primitive_idempotents(QG)
  @test isone(sum(idems))
  @test length(idems) == 2

  A = matrix_algebra(QQ, 2)
  idems = @inferred central_primitive_idempotents(A)
  @test idems == [one(A)]

  # semisimple

  Fp = GF(2)
  @test !is_semisimple(Fp[small_group(2, 1)])
  @test is_semisimple(QQ[small_group(2, 1)])

  # etale

  Qx, x = QQ["x"]
  @test is_etale(StructureConstantAlgebra(x))
  @test !is_etale(StructureConstantAlgebra(x^2))

  # zero algebra

  K, = quadratic_field(-1)
  for k in (K, QQ)
    A = zero_algebra(k)
    @test !is_simple(A)
    @test length(decompose(A)) == 0
    @test is_semisimple(A)
    B, m = direct_product(k, typeof(A)[]; task = :sum)
    @test is_zero(B) && dim(B) == 0
    @test length(m) == 0
  end

  # product of components

  A = group_algebra(QQ, small_group(2, 1))
  C, p = Hecke.product_of_components_with_projection(A, Int[])
  @test is_zero(C) && dim(C) == 0
  @test domain(p) === A && codomain(p) === C && is_one(p(one(A)))

  # Skolem-Noether
  K, a = quadratic_field(-13)
  A = matrix_algebra(K, 3)
  X = rand(A, -1:1)
  while !is_invertible(X)[1]
    X = rand(A, -1:1)
  end
  h = hom(A, A, inv(X) .* basis(A) .* X)
  a = Hecke._skolem_noether(h)
  @test all(h(b) == inv(a) * b * a for b in basis(A))

  let
    # maximal separable subalgebra
    Qx, x = QQ[:x]
    A = associative_algebra((x^2 + 1)^2)
    B, BtoA = Hecke.maximal_separable_subalgebra(A)
    @test domain(BtoA) === B
    @test codomain(BtoA) == A
    @test dim(B) == 2
    @test is_simple(B)
  end

  let
    # multiplicative depdendencies
    a = QQ[1 2; 3 4]
    c = QQ[-3 2; 3 0]
    v = [a, a^2, c, c*a]
    m = Hecke._multiplicative_dependencies([a, a^2, c, c*a])
    for w in m
      @test isone(prod(v[i]^Int(w[i]) for i in 1:length(v)))
    end
  end

  let
    # separability, commutative algebras only for now
    K, t = rational_function_field(GF(3), :t);
    Kx, x = K["x"];
    A = associative_algebra(x^3 - t)
    @test !is_separable(A)
    A = associative_algebra(x^2 - t)
    @test is_separable(A)
    A = associative_algebra(x^9 - t)
    @test !is_separable(A)
    A = associative_algebra((x^2 - t)^2)
    @test !is_separable(A)
    A = associative_algebra((x^2 - t)*(x^4 + t^2))
    @test is_separable(A)

    A = matrix_algebra(QQ, 2)
    @test is_separable(A)
    A = matrix_algebra(GF(9), 2)
    @test is_separable(A)
  end

  let
    # decompose
    K, t = rational_function_field(GF(3), :t);
    Kx, x = K["x"];
    # we don't have a radical yet, so take a group algebra, which will know
    # that it is semisimple
    A = group_algebra(K, abelian_group(5));
    dec = decompose(A)
    # A = F_3(t)[C_5] = F_3(t)[X]/(X^5 - 1) and this factors into deg 4 * deg 1
    @test length(dec) == 2 && issetequal(dim.(first.(dec)), [1, 4])
  end
end
