@testset "Maximal tori of algebras" begin
  let
    Kt, t = rational_function_field(GF(2), :s)
    A = matrix_algebra(Kt, 3)
    T, TtoA = Hecke.maximal_torus(A)
    @test is_separable(T)
    @test is_commutative(T)
    @test dim(T) == 3
  end

  let
    Kt, t = rational_function_field(GF(2), :s)
    A = group_algebra(Kt, abelian_group([3]))
    T, TtoA = Hecke.maximal_torus(A)
    @test is_separable(T)
    @test is_commutative(T)
    @test dim(T) == 3
  end
end
