
function gauss_binom_2(n::Int, k::Int)
  if k < 0 || k > n
    return big(0)
  end
  num = big(1)
  den = big(1)
  for i in 0:(k - 1)
    num *= (big(2)^(n - i) - 1)
    den *= (big(2)^(k - i) - 1)
  end
  return num ÷ den
end


@testset "line_orbits_mod_2" begin
  I3 = matrix(ZZ, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  orbs = line_orbits_mod_2(UInt64, [I3])
  @test length(orbs) == 8
  @test sort(first.(orbs)) == ones(Int, 8)

  P = matrix(ZZ, 3, 3, [0, 1, 0, 1, 0, 0, 0, 0, 1])
  @test sort(first.(line_orbits_mod_2(UInt64, [P]))) == [1, 1, 1, 1, 2, 2]
end

@testset "orbmod2 subspaces" begin
  I4 = matrix(ZZ, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  for k in 0:4
    got = orbmod2_subspaces(UInt64, [I4], k)
    @test sum(first.(got)) == UInt64(gauss_binom_2(4, k))
    @test all(first.(got) .== 1)
  end
  @test_throws ArgumentError line_orbits_mod_2(UInt64, ZZMatrix[])
end

