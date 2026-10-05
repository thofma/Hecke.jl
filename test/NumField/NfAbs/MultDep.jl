@testset "Multiplicative groups" begin
  let
    k, a = quadratic_field(2)
    G, f = Hecke.multiplicative_group([a + 1])
    Ggens = f.(gens(G))
    @test all(x -> !is_one(evaluate(x)), Ggens)

    fl, _ = Hecke.MultDep._is_saturated(f, 2)
    @test fl

    G, f = Hecke.multiplicative_group([(a + 1)^2])
    fl, _ = Hecke.MultDep._is_saturated(f, 3; support = Vector{AbsSimpleNumFieldOrderIdeal}())
    @test fl
    fl, _ = Hecke.MultDep._is_saturated(f, 2; support = Vector{AbsSimpleNumFieldOrderIdeal}())
    @test !fl

    @testset "Preimages requiring more p-adic precision" begin
      # We want to trigger recomputing the conjugates at higher precision.
      # At precision 20, rational reconstruction fails for 2^70, while the
      # relation found for 101^20 does not pass verification.
      for task in (:all, :modulo_tor), exponent in (ZZ(2)^70, ZZ(101)^20)
        G, f = Hecke.multiplicative_group([a + 1]; task)
        u = f(G[1])
        @test preimage(f, u^exponent) == exponent * G[1]
        @test preimage(f, u^-exponent) == -exponent * G[1]
        @test preimage(f, FacElem((a + 1)^3)) == 3 * G[1]
      end
    end

    k, a = cyclotomic_real_subfield(5)
    cyc = [-a, -a - 2]
    G, f = Hecke.multiplicative_group(cyc;  task = :modulo_tor)
    fl, _ = Hecke.MultDep._is_saturated(f, 2; support = Vector{AbsSimpleNumFieldOrderIdeal}())
    @test fl
    fl, _ = Hecke.MultDep._is_saturated(f, 5; support = Vector{AbsSimpleNumFieldOrderIdeal}())
    @test fl
  end
end
