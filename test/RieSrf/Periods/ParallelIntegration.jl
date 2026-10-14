@testset "ParallelIntegration" begin
  # every abscissa (node index 2, ..., N + 1) is owned by exactly one chunk
  for (N, chunk_len) in ((10, 4), (7, 16), (16, 16))
    chunks = RSM._chunk_bounds(N, chunk_len)
    @test chunks[1][1] == 1 && chunks[end][2] == N + 2
    @test all(chunks[c][2] == chunks[c + 1][1] for c in 1:length(chunks) - 1)
    owned = vcat([collect(max(a, 2):min(b - 1, N + 1)) for (a, b) in chunks]...)
    @test owned == collect(2:N + 1)
  end
  CC = AcbField(64)
  @test RSM._match_fibers([CC(1), CC(2), CC(3)], [CC(3), CC(1), CC(2)]) == [2, 3, 1]
  @test_throws ErrorException RSM._match_fibers([CC(1), CC(2)], [CC(1), CC(1)])
end
