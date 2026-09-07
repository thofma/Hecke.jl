

@testset "line_orbits_mod_2" begin
  I3 = matrix(ZZ, 3, 3, [1, 0, 0, 0, 1, 0, 0, 0, 1])
  orbs = Hecke.line_orbits_mod_2(UInt64, [I3])
  @test length(orbs) == 8
  @test sort(first.(orbs)) == ones(Int, 8)

  P = matrix(ZZ, 3, 3, [0, 1, 0, 1, 0, 0, 0, 0, 1])
  @test sort(first.(Hecke.line_orbits_mod_2(UInt64, [P]))) == [1, 1, 1, 1, 2, 2]


  function test_mod2_line_orbits(L::ZZLat)
    L = lattice(rational_span(L))
    F2 = GF(2)
    GZ = [ZZ.(i) for i in automorphism_group_generators(L)]
    GF2 = [F2.(i) for i in GZ]
    orb_len2 = sort!(first.(Hecke.line_orbits_mod_2(UInt32, GZ)))[2:end]
    orb_len1 = [i[2] for i in Hecke._line_orbits(GF2)]
    sort!(orb_len1)
    return orb_len1 == orb_len2
  end
  LL = [integer_lattice(gram=matrix(QQ,i)) for i in [[2 0 1 -1 -1 0; 0 4 2 0 0 -1; 1 2 5 -2 -2 -1; -1 0 -2 4 0 0; -1 0 -2 0 5 2; 0 -1 -1 0 2 7], [2 0 0 0 -1 1; 0 2 1 0 -1 1; 0 1 3 1 0 0; 0 0 1 4 2 -1; -1 -1 0 2 5 -2; 1 1 0 -1 -2 16], [532 265 527 1 530 1054; 265 133 264 0 265 527; 527 264 528 0 527 1054; 1 0 0 1 0 0; 530 265 527 0 530 1054; 1054 527 1054 0 1054 2108], [1 0 0 0 0 0; 0 2 0 1 1 1; 0 0 2 1 -1 0; 0 1 1 4 0 2; 0 1 -1 0 9 -1; 0 1 0 2 -1 18], [1 0 0 0 0 0; 0 2 0 1 0 0; 0 0 2 1 0 1; 0 1 1 4 0 2; 0 0 0 0 9 1; 0 0 1 2 1 16]]]
  for L in LL
    @test test_mod2_line_orbits(L)
  end
end

@testset "orbmod2 subspaces" begin

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

  I4 = matrix(ZZ, 4, 4, [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1])
  for k in 0:4
    got = Hecke.orbmod2_subspaces(UInt64, [I4], k)
    @test sum(first.(got)) == UInt64(gauss_binom_2(4, k))
    @test all(first.(got) .== 1)
  end
  @test_throws ArgumentError Hecke.line_orbits_mod_2(UInt64, ZZMatrix[])

  F = GF(2)
  grp = [F[0 1 0 0; 0 0 1 0; 0 0 0 1; 1 0 0 0], F[0 1 0 0; 1 0 0 0; 0 0 1 0; 0 0 0 1]]  #S_4
  a = Hecke.orbit_representatives_and_stabilizers_mod_2(grp,2)
  b = Hecke.orbit_representatives_and_stabilizers_mod_2(grp,2; group_order=factorial(4))
  @test sort!([i[2] for i in a]) == sort!([i[2] for i in b]) == [3, 4, 4, 6, 6, 12] # same orbit sizes



end

