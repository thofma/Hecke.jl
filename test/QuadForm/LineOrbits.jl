@testset "Random lines" begin
  P = Hecke.enumerate_lines(GF(5), 20)
  io = IOBuffer()
  show(io, MIME"text/plain"(), P)
  show(IOContext(io, :supercompact => true), P)
  show(io, P)
  for i in 1:100
    v = rand(P)
    @test !iszero(v) && isone(v[findfirst(!iszero, v)])
  end
end
