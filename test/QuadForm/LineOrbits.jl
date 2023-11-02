@testset "Random lines" begin
  P = Hecke.enumerate_lines(GF(5), 20)
  io = IOBuffer()
  show(io, MIME"text/plain"(), P)
  @test length(String(take!(io))) == 98
  show(IOContext(io, :supercompact => true), P)
  @test length(String(take!(io))) == 25
  show(io, P)
  @test length(String(take!(io))) == 33
  for i in 1:100
    v = rand(P)
    @test is_zero(v) || gcd(v) == 1
  end
end
