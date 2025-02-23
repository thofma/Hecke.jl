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
  for F in (GF(2),
            GF(4),
            Native.GF(2),
            Native.GF(2, 1),
            Native.GF(ZZ(2)),
            Native.GF(ZZ(2), 2),
            rational_function_field(GF(2))[1],
            rational_function_field(GF(4))[1])
    A = group_algebra(F, G)
    I = radical(A)
    bI = F[1 0 0 0 0 0 0 1;
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
  end

  for F in (GF(3),
            GF(9),
            Native.GF(3),
            Native.GF(3, 1),
            Native.GF(ZZ(3)),
            Native.GF(ZZ(3), 1),
            GF(next_prime(ZZ(2)^70)),
            GF(next_prime(ZZ(2)^70), 2),
            rational_function_field(GF(3))[1],
            rational_function_field(GF(next_prime(ZZ(2)^70)))[1])
    A = group_algebra(F, G)
    I = radical(A)
    @test is_zero(I)
  end

  for F in (GF(2, 2),
            Native.GF(2, 2),
            Native.GF(ZZ(2), 2),
            rational_function_field(GF(2))[1],
            rational_function_field(GF(4))[1])
    A = group_algebra(F, G)
    I = radical(A)
    ge = [A(g) - A(one(G)) for g in G]
    @test all(in(I), ge)
    AS, AStoA = StructureConstantAlgebra(A)
    I = radical(AS)
    @test all(in(I), preimage.(Ref(AStoA), ge))
  end

  for K in [QQ, rationals_as_number_field()[1]]
    A = group_algebra(K, G)
    I = radical(A)
    @test nrows(basis_matrix(I, copy = false)) == 0
  end

  for K in (GF(2),
            GF(4),
            Native.GF(2),
            Native.GF(2, 2),
            QQ,
            rationals_as_number_field()[1],
            rational_function_field(GF(2))[1],
            rational_function_field(GF(4))[1])
    A = matrix_algebra(K, [ matrix(K, 2, 2, [ 1, 0, 0, 0 ]), matrix(K, 2, 2, [ 0, 1, 0, 0 ]), matrix(K, 2, 2, [ 0, 0, 0, 1]) ]) # i. e. upper triangular matrices
    I = radical(A)
    @test dim(I) == 1
  end

  # function field example
  let
    k, o = finite_field(9)
    K, t = rational_function_field(k, :t)
    Kx, x = K[:x]
    A = associative_algebra(x^3 + o*t^3)
    I = radical(A)
    @test dim(I) == 2
    @test all(b -> b^3 == 0, basis(I)) # must be nilpotent
  end
end
