@testset "Torsion Units" begin
  l = Hecke.primes_up_to(20)
  for i = 2:length(l)
    p = l[i]
    K, a = cyclotomic_field(p)
    OK = maximal_order(K)
    @test is_torsion_unit(OK(a))
    @test Hecke.torsion_unit_order(OK(a), p) == p
    TU = Hecke.torsion_units(K)
    @test length(TU) == 2*p
    ST = Set([x.elem_in_nf for x in Hecke.torsion_units(OK)])
    STK = Set(TU)
    @assert ST == STK
    gen = Hecke.torsion_units_generator(OK)
    @test !isone(gen^p)
    @test !isone(gen^2)
  end

  K, a = cyclotomic_field(13, cached = false)
  O = maximal_order(K)
  @test (@inferred length(Hecke._torsion_units_lattice_enum(O)[1])) == 26

  let
    p = 2^9
    K, a = cyclotomic_field(p)
    l = Hecke._torsion_group_order_divisor(K)
    @test is_divisible_by(degree(K), euler_phi(l))
  end

  let
    for d in [2, 4, 10, 20, 3, 5, 7, 33]
      K, a = cyclotomic_field(d)
      A, f = torsion_unit_group(K)
      @test order(A) == (is_odd(d) ? 2d : d)
      b = f(A[1])
      @test is_one(b^order(A)) && all(i -> !is_one(b^i), 2:order(A)-1)
    end
  end
end
