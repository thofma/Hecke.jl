@testset "Finite field paths" begin
  # Paths over FqField must work for prime fields and nonconstant coefficients.
  for q in (2, 9)
    F, a = finite_field(q)
    generators = [matrix(F, [1 a; 0 1]), matrix(F, [0 1; 1 0])]
    v = matrix(F, 2, 1, [1, 0])
    w = matrix(F, 2, 1, [a, 1])
    found, path = Hecke.find_path(generators, v, w)
    @test found
    u = v
    for i in path
      u = generators[i]*u
    end
    @test u == w

    found, path = Hecke.find_path(generators, v, v)
    @test found
    @test isempty(path)

    w = q == 9 ? matrix(F, 2, 1, [1 + a, 0]) : w
    found, path = Hecke.find_path([identity_matrix(F, 2)], v, w)
    @test !found
    @test isempty(path)
  end
end

@with_polymake @testset "Eichler" begin
  K, a = Hecke.rationals_as_number_field()
  A = Hecke.QuaternionAlgebra(K, K(1), K(1))
  A = Hecke.StructureConstantAlgebra(K, A.mult_table)
  OA = maximal_order(A)
  b = @inferred Hecke.principal_generator_eichler(2 * OA)
  @test b * OA == 2 * OA
end
