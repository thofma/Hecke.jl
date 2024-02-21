@testset "Rank computations using descent" begin
  E1 = elliptic_curve([1, 1, 1, -352, -2689])
  E2 = elliptic_curve([0, 1, 0, -41, -116])
  E3 = elliptic_curve([1, 0, 1, -231, -442])
  E4 = elliptic_curve([0, -1, 0, -289, 289])
  @testset "2-torsion descent" begin

    lower, upper, III_phi,_III_phi = @inferred Hecke.rank_2_torsion(E1)
    @test (lower <= 1 <= upper)
    @test (III_phi == 4 &&  _III_phi == 1)
    lower, upper, III_phi,_III_phi = @inferred Hecke.rank_2_torsion(E2)
    @test (lower <= 0 <= upper)
    @test (III_phi == 1 && _III_phi == 1)
    lower, upper, III_phi,_III_phi = @inferred Hecke.rank_2_torsion(E3)
    @test (lower <= 3 <= upper)
    @test (III_phi == 2 && _III_phi == 1)
    lower, upper, III_phi,_III_phi = @inferred Hecke.rank_2_torsion(E4)
    @test (lower <= 2 <= upper)
    @test III_phi == 2 && _III_phi == 1

  end

  @testset "local solubility" begin

    @test Hecke.quartic_local_solubility(3, 2, 3, 4, 5) == false
    @test Hecke.quartic_local_solubility(3437843, 24789579, 3122111, -424, 57) == true
    @test Hecke.quartic_local_solubility(-888, 5767, 2110, -424, 5128673) == false
  end
end
