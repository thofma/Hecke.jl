@testset "psibound" begin

  @testset "psi_lower" begin
    sp = PrimesSet(2, 100);
    fb = []; for x=sp push!(fb, fmpz(x)); end;
    fb = FactorBase(fb)
    @test length(find(x->issmooth(fb, fmpz(x)), 1:256)) == psi_lower(255, 100)[1][end]
  end
end

