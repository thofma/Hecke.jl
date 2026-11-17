@testset "AlgAss/Map" begin
  let
    k = GF(2)
    A = matrix_algebra(k, 2)
    B = matrix_ring(k, 2)
    f = hom(A, B, B.(matrix.(basis(A))))
    @test domain(f) === A
    @test codomain(f) === B
    @test is_one(f(one(A)))
    for _ in 1:10
      x = rand(A)
      y = rand(A)
      @test f(x * y) == f(x) * f(y)
      @test f(x + y) == f(x) + f(y)
    end

    @test_throws Hecke.AbstractAlgebra.NotImplementedError preimage(f, one(B))

    @test_throws ArgumentError hom(A, B, B.(matrix.(basis(A)))[1:3])
    @test_throws ArgumentError hom(A, B, [zero(B), zero(B), zero(B), zero(B)])

    g = hom(A, B, B.(matrix.(basis(A))); inverse = b -> A(matrix(b)))
    @test preimage(g, one(B)) == one(A)
  end

  let
    k = GF(2, 2)
    A = matrix_algebra(k, 2)
    B = matrix_ring(k, 2);
    f = hom(A, B, x -> x^2, B.(matrix.(basis(A))))
    @test f(gen(k) * one(A)) == gen(k)^2 * one(B)
  end

  # Test preimages under an inclusion, an isomorphism, and a quotient map.
  @testset "Element preimages of algebra morphisms" begin
    A = matrix_algebra(QQ, 2)
    Z, iota = center(A)
    @test preimage(iota, A(3)) == Z(3)
    outside = A(QQ[0 1; 0 0])
    @test !first(Hecke.has_preimage_with_preimage(iota, outside))
    @test_throws ArgumentError preimage(iota, outside)

    f = hom(A, A, basis(A))
    inv(f)
    @test preimage(f, A[2]) == A[2]

    _, t = polynomial_ring(QQ, "t")
    B = associative_algebra(t^2)
    Q, q = quo(B, radical(B))
    ok, b = Hecke.has_preimage_with_preimage(q, one(Q))
    @test ok && q(b) == one(Q)
  end

  @testset "Threaded morphisms" begin
    A = matrix_algebra(QQ, 1)
    f = Hecke.id_hom(A)

    @test length(f.c_t_threaded) >= Hecke._maxthreadid()
    @test length(f.d_t_threaded) >= Hecke._maxthreadid()

    results = Vector{Tuple{Bool, Bool}}(undef, Threads.nthreads())
    Threads.@threads :static for i in eachindex(results)
      results[i] = (f(one(A)) == one(A), preimage(f, one(A)) == one(A))
    end
    @test all(first, results)
    @test all(last, results)
  end
end
