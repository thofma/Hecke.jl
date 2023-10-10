@testset "Multi-sets" begin
  str = "A nice sentence"
  m = @inferred multiset(str)
  io = IOBuffer()
  show(io, MIME"text/plain"(), m)
  @test length(String(take!(io))) == 92
  show(io, m)
  @test length(String(take!(io))) == 44
  print(IOContext(io, :supercompact => true), m)
  @test length(String(take!(io))) == 39

  M = MSet(root_lattice(:A, i) for j in 1:10 for i in 1:100)
  show(io, MIME"text/plain"(), m)
  @test length(String(take!(io))) == 983

  m = @inferred multiset(Int[x^3%8 for x = 1:50])
  @test !isempty(m)
  @test length(m) == 50
  @test eltype(m) == Int
  @test !(2 in m)

  m2 = copy(m)
  @test m2 == m
  @test unique(m) == unique(collect(m))

  push!(m, 2, 4)
  pop!(m, 2)
  @test (2 in m)
  @test multiplicity(m, 2) == 3

  delete!(m, 2)
  @test multiplicity(m, 2) == 0

  @test pop!(m, 2, 0) == 0
  k = pop!(m2)
  @test multiplicity(m2, k) == multiplicity(m, k) - 1

  m = @inferred multiset(Dict("a" => 4, "b" => 1, "c" => 9))
  lis = @inferred collect(m)

  m2 = @inferred union(m, lis)
  for i in m
    @test multiplicity(m2, i) == 2*multiplicity(m, i)
  end

  @test union(m) == m
  @test length(filter(x -> multiplicity(m, x) != 1, m)) == length(m) - 1

  m = multiset(Int[x^3%8 for x = 1:50])
  filter!(isodd, m)
  @test length(m) == 25

  val = @inferred multiplicities(m)
  @test all(x -> x > 1, val)

  @test isempty(setdiff(m, m))
end

@testset "Sub-multi-set iterator" begin
  m = @inferred multiset(["a", "b", "c"], [4, 1, 9])
  M = @inferred subsets(m)
  io = IOBuffer()
  show(io, MIME"text/plain"(), M)
  @test length(String(take!(io))) == 61
  show(io, M)
  @test length(String(take!(io))) == 64
  print(IOContext(io, :supercompact => true), M)
  @test length(String(take!(io))) == 35
  @test eltype(M) == typeof(m)
  @test length(collect(M)) == length(M)
end

@testset "Sub-set iterators" begin
  s = Set(String["a", "b", "c"])
  S = @inferred subsets(s)
  io = IOBuffer()
  show(io, MIME"text/plain"(), S)
  @test length(String(take!(io))) == 58
  show(io, S)
  @test length(String(take!(io))) == 58
  print(IOContext(io, :supercompact => true), S)
  @test length(String(take!(io))) == 29
  @test eltype(S) == typeof(s)
  @test length(collect(S)) == length(S)

  S = @inferred subsets(s, 2)
  io = IOBuffer()
  show(io, MIME"text/plain"(), S)
  @test length(String(take!(io))) == 68
  show(io, S)
  @test length(String(take!(io))) == 68
  print(IOContext(io, :supercompact => true), S)
  @test length(String(take!(io))) == 39
  @test eltype(S) == typeof(s)
  @test length(collect(S)) == length(S)
  @test length(S[1]) == 2
end
