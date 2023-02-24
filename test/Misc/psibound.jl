@testset "psibound" begin

  @testset "psi_lower" begin
    sp = PrimesSet(2, 100);
    fb = []; for x=sp push!(fb, ZZRingElem(x)); end;
    fb = FactorBase(fb)
    @test length(findall(x->is_smooth(fb, ZZRingElem(x)), 1:256)) == psi_lower(255, 100)[1][end]
  end
end

