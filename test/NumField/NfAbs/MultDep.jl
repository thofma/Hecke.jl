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

    k, a = cyclotomic_real_subfield(5)
    cyc = [-a, -a - 2]
    G, f = Hecke.multiplicative_group(cyc;  task = :modulo_tor)
    fl, _ = Hecke.MultDep._is_saturated(f, 2; support = Vector{AbsSimpleNumFieldOrderIdeal}())
    @test fl
    fl, _ = Hecke.MultDep._is_saturated(f, 5; support = Vector{AbsSimpleNumFieldOrderIdeal}())
    @test fl
  end
end
