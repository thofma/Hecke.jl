@testset "Differentials" begin
  @testset "Baker basis certified modulo p" begin
    f = FAST_CURVES[9][2]                                 # g6: y^4 + x^4 - 1, genus 3
    RS = _rs(f, 100)
    @test RSM.genus(RS) == 3
    C = RSM.computational_model(RS)
    @test C.baker_basis
    @test !isdefined(C, :basis_of_differentials)          # no maximal orders over Q needed
    # the modular genus certifies only an equality with the interior point count
    @test RSM._baker_certified(C.defining_polynomial, 3)
    @test !RSM._baker_certified(C.defining_polynomial, 4)
    test_sanity(_computed(RS); expected_genus = 3)
    @test length(RSM.basis_of_differentials(RS)) == 3     # still available on request
  end
end
