@testset "Decomposition" begin
  F, s = rational_function_field(GF(3), :s)
  # Structure constants associated to the F-algebra E[x]/((x+1)(x+2))
  # over the purely inseparable extension E/F of degree 3.
  structure_constants = reshape(
    [1 0 0 0 0 0 0 1 0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0
      0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0 0 0 1 0 0 1 0 0
      0 0 0 2*s 0 0 0 0 1 0 0 0 0 2*s 0 0 0 0 0 0 0 0 1 0
      0 0 1 0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0 0 0 0 0 1
      0 2*s 0 0 0 0 1 0 0 0 0 0 0 0 0 2*s 1 0 0 0 0 0 0 0
      0 0 0 0 0 2*s 0 0 0 0 1 0 0 0 0 0 0 0 0 2*s 1 0 0 0
      0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0 0 0 1 0 0 1 0 0
      0 0 0 2*s 0 0 0 0 1 0 0 0 0 2*s 0 0 0 0 0 0 0 0 1 0
      2*s 0 0 0 0 0 0 2*s 0 0 0 0 0 0 2*s 0 0 2*s 0 0 0 0 0 0],
    (6, 6, 6))
  A = structure_constant_algebra(F, structure_constants)
  @test !is_separable(A)
  B = first(Hecke._separable_subalgebra(A))
  @test dim(B) == 2
  @test is_separable(B)

  (A1, i1), (A2, i2) = Hecke._dec_com_gen(A)
  @test i1(one(A1)) * i2(one(A2)) == zero(A)
  @test i1(one(A1)) + i2(one(A2)) == one(A)
  @test dim(A1) + dim(A2) == dim(A)

end

