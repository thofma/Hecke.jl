@testset "Lattice multiplication maps" begin
  F, t = rational_function_field(GF(7), "t")
  for (R, K, p) in ((ZZ, QQ, QQ(2)),
                    (parent(numerator(t)), F, t),
                    (localization(F, degree), F, inv(t)))
    A = matrix_algebra(K, 2)
    L = Hecke.lattice(A, R, basis(A))
    a = A(K[p 1; 0 0])
    b = A(K[0 0; 1 0])
    x = L(b)
    for side in (:left, :right)
      f = @inferred Hecke.multiplication_map(L, a; side)
      expected = side === :left ? a*b : b*a
      @test Hecke.elem_in_algebra(f(x)) == expected
      ff = @inferred Hecke.multiplication_map(L, L(a); side)
      @test ff(x) == f(x)
      @test f(preimage(f, f(x))) == f(x)
      @test iszero(f(zero(L)))
      @test_throws ArgumentError preimage(f, L(one(A)))

      N = p*L
      g = Hecke.multiplication_map(L, N, p*one(A); side)
      y = N(p*one(A))
      @test g(L(one(A))) == y
      @test preimage(g, y) == L(one(A))
      gg = @inferred Hecke.multiplication_map(L, N, y; side)
      @test gg(L(one(A))) == y
      @test_throws ArgumentError Hecke.multiplication_map(L, N, one(A); side)

      Z = Hecke.zero_lattice(A, R)
      h = @inferred Hecke.multiplication_map(Z, a; side)
      @test iszero(h(zero(Z)))
      @test iszero(preimage(h, zero(Z)))
    end
    @test_throws ArgumentError Hecke.multiplication_map(L, a; side = :invalid)
    Aother = matrix_algebra(K, 2)
    Lother = Hecke.lattice(Aother, R, basis(Aother))
    @test_throws ArgumentError Hecke.multiplication_map(L, one(Aother); side = :left)
    @test_throws ArgumentError Hecke.multiplication_map(L, Lother(one(Aother)); side = :left)
  end
end
