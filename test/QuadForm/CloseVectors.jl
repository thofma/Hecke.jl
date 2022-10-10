@testset "QuadForm/CloseVectors" begin
  L = Zlattice(gram = matrix(QQ, 3, 3, [1, 0, 0,
                                        0, 1, 0,
                                        0, 0, 1]))
  v = [-1, 0, 0]
  b = 3//5
  cl = @inferred close_vectors(L, v, b)
  @test first.(cl) == [[-1, 0, 0]]
  # Try some different input types
  @test close_vectors(L, fmpq[-1, 0, 0], b) isa Vector{Tuple{Vector{fmpz}, fmpq}}
  @test close_vectors(L, fmpz[-1, 0, 0], big"3"//5) isa Vector{Tuple{Vector{fmpz}, fmpq}}
  @test close_vectors(L, [-1//1, 0, 0], QQ(3//5)) isa Vector{Tuple{Vector{fmpz}, fmpq}}
  @test close_vectors(L, fmpq[-1, 0, 0], b, Int) isa Vector{Tuple{Vector{Int}, fmpq}}
  @test close_vectors(L, fmpz[-1, 0, 0], big"3"//5, Int) isa Vector{Tuple{Vector{Int}, fmpq}}
  @test close_vectors(L, [-1//1, 0, 0], QQ(3//5), Int) isa Vector{Tuple{Vector{Int}, fmpq}}

  cl = @inferred close_vectors_iterator(L, v, b)
  @test first.(collect(cl)) == [[-1, 0, 0]]
  # Try some different input types
  @test collect(close_vectors_iterator(L, fmpq[-1, 0, 0], b)) isa Vector{Tuple{Vector{fmpz}, fmpq}}
  @test collect(close_vectors_iterator(L, fmpz[-1, 0, 0], big"3"//5)) isa Vector{Tuple{Vector{fmpz}, fmpq}}
  @test collect(close_vectors_iterator(L, [-1//1, 0, 0], QQ(3//5))) isa Vector{Tuple{Vector{fmpz}, fmpq}}

  @test collect(close_vectors_iterator(L, fmpq[-1, 0, 0], b, Int)) isa Vector{Tuple{Vector{Int}, fmpq}}
  @test collect(close_vectors_iterator(L, fmpz[-1, 0, 0], big"3"//5, Int)) isa Vector{Tuple{Vector{Int}, fmpq}}
  @test collect(close_vectors_iterator(L, [-1//1, 0, 0], QQ(3//5), Int)) isa Vector{Tuple{Vector{Int}, fmpq}}

  v = [-1//2, 0, 0]
  b = 3//5
  cl = @inferred close_vectors(L, v, b)
  @test issetequal(first.(cl), Vector{fmpz}[[-1, 0, 0], [0, 0, 0]])
  cl = @inferred close_vectors(L, v, b)
  @test issetequal(first.(collect(cl)), Vector{fmpz}[[-1, 0, 0], [0, 0, 0]])

  v = [-1//3, -1//3, 0]
  b = 9//5
  cl = @inferred close_vectors(L, v, b)
  @test sort!(first.(cl)) == sort!([[0, 0, 0], [-1, 0, 0], [0, -1, 0], [-1, -1, 0],
                                    [0, 0, -1], [0, 0, 1], [-1, 0, -1], [-1, 0, 1],
                                    [0, -1, -1], [0, -1, 1]])

  v = [-1//3, -1//3, 0]
  b = 9//5
  cl = @inferred collect(close_vectors_iterator(L, v, b))
  @test sort!(first.(cl)) == sort!([[0, 0, 0], [-1, 0, 0], [0, -1, 0], [-1, -1, 0],
                                    [0, 0, -1], [0, 0, 1], [-1, 0, -1], [-1, 0, 1],
                                    [0, -1, -1], [0, -1, 1]])

  L = Zlattice(matrix(QQ, 1, 1, [2]))
  cl = @inferred close_vectors(L, [0], 1)
  @test first.(cl) == [[0]]
  cl = @inferred collect(close_vectors_iterator(L, [0], 1))
  @test first.(cl) == [[0]]

  cl = @inferred close_vectors(L, [0], 9//2)
  @test issetequal(first.(cl), Vector{fmpz}[[1], [-1], [0]])
  cl = @inferred collect(close_vectors_iterator(L, [0], 9//2))
  @test issetequal(first.(cl), Vector{fmpz}[[1], [-1], [0]])

  cl = @inferred close_vectors(L, [0], 4, 4)
  @test issetequal(first.(cl), Vector{fmpz}[[-1], [1]])
  cl = @inferred collect(close_vectors_iterator(L, [0], 4, 4))
  @test issetequal(first.(cl), Vector{fmpz}[[-1], [1]])

  cl = @inferred close_vectors(L, [0], 9//2, 9//2)
  @test isempty(cl)
  cl = @inferred collect(close_vectors_iterator(L, [0], 9//2, 9//2))
  @test isempty(cl)

  L = Zlattice(matrix(QQ, 1, 1, [2]); gram = matrix(QQ, 1, 1, [1//2]))
  cl = @inferred close_vectors(L, [0], 20)
  @test issetequal(first.(cl), Vector{fmpz}[[i] for i in -3:3])
  cl = @inferred collect(close_vectors_iterator(L, [0], 20))
  @test issetequal(first.(cl), Vector{fmpz}[[i] for i in -3:3])

  L = Zlattice(gram = identity_matrix(QQ, 6))
  v = [-1, 0, -1, 0, -2, 0]
  u = 14//3
  cl = close_vectors(L, v, u)
  @test length(unique(cl)) == 485
  @test all(x -> x[2] == inner_product(rational_span(L), QQ.(x[1] - v), QQ.(x[1] - v)) <= u, cl)
  cl = collect(close_vectors_iterator(L, v, u))
  @test length(unique(cl)) == 485
  @test all(x -> x[2] == inner_product(rational_span(L), QQ.(x[1] - v), QQ.(x[1] - v)) <= u, cl)

  L = Zlattice(gram = identity_matrix(QQ, 6))
  v = [-1, 0, -1, 0, -2, 0]
  u = 14//3
  cl = close_vectors(L, v, u)
  @test length(unique(cl)) == 485
  @test all(x -> x[2] == inner_product(rational_span(L), QQ.(x[1] - v), QQ.(x[1] - v)) <= u, cl)
  cl = collect(close_vectors_iterator(L, v, u))
  @test length(unique(cl)) == 485
  @test all(x -> x[2] == inner_product(rational_span(L), QQ.(x[1] - v), QQ.(x[1] - v)) <= u, cl)

  cl = close_vectors(L, v, u, u)
  @test length(cl) == 0
  cl = collect(close_vectors_iterator(L, v, u, u))
  @test length(cl) == 0

  cl = close_vectors(L, v, 3, 4)
  @test length(cl) == 412
  cl = collect(close_vectors_iterator(L, v, 3, 4))
  @test length(cl) == 412

  L = Zlattice(matrix(QQ, 2, 2, [1, 0, 0, 2]))
  v = [1, 1]
  u = 3
  cl = close_vectors(L, v, u)
  @test length(cl) == 3
  @test all(x -> x[2] == inner_product(rational_span(L), QQ.(x[1] - v), QQ.(x[1] - v)) <= u, cl)
  cl = collect(close_vectors_iterator(L, v, u))
  @test length(cl) == 3
  @test all(x -> x[2] == inner_product(rational_span(L), QQ.(x[1] - v), QQ.(x[1] - v)) <= u, cl)

  u = 4
  cl = close_vectors(L, v, u)
  @test length(cl) == 7
  @test all(x -> x[2] == inner_product(rational_span(L), QQ.(x[1] - v), QQ.(x[1] - v)) <= u, cl)
  cl = collect(close_vectors_iterator(L, v, u))
  @test length(cl) == 7
  @test all(x -> x[2] == inner_product(rational_span(L), QQ.(x[1] - v), QQ.(x[1] - v)) <= u, cl)

  L = Zlattice(;gram = QQ[0 0; 0 0])
  @test_throws ArgumentError close_vectors(L, [1, 1], 1)
  @test_throws ArgumentError close_vectors_iterator(L, [1, 1], 1)
  L = Zlattice(;gram = QQ[-1 0; 0 -1])
  @test_throws ArgumentError close_vectors(L, [1, 1], 1)
  @test_throws ArgumentError close_vectors_iterator(L, [1, 1], 1)
  L = Zlattice(;gram = QQ[1 0; 0 1])
  @test_throws ArgumentError close_vectors(L, [1, 1, 1], 1)
  @test_throws ArgumentError close_vectors_iterator(L, [1, 1, 1], 1)
  @test_throws ArgumentError close_vectors(L, [1], 1)
  @test_throws ArgumentError close_vectors_iterator(L, [1], 1)

  L = root_lattice(:A, 2)
  @test_throws ArgumentError short_vectors(L, -1)
  @test_throws ArgumentError short_vectors(L, -1, 1)
  @test_throws ArgumentError short_vectors(L, 1 , -1)
  v = fmpq[1, 1//2]
  @test_throws ArgumentError close_vectors(L, v, -1)
  Lm = rescale(L,-1)
  @test_throws ArgumentError close_vectors(Lm, v, 1)
  @test_throws ArgumentError short_vectors(Lm, 1)

  # Test the legacy interface

  Q = matrix(QQ, 4,4,[1 0 0 0; 0 1 0 0; 0 0 1 0; 0 0 0 1]);
  L = matrix(fmpq[1,1,1,1]);
  c = fmpq(3);
  @test Hecke.closest_vectors(Q, L, c, sorting=true)[1] == [-2, -1, -1, -1]
  @test size(Hecke.closest_vectors(Q, L, c), 1) == 9
  @test Hecke.closest_vectors(Q, L, c, equal=true, sorting=true)[1] == [-2, -1, -1, -1]
end
