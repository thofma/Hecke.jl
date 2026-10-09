@with_polymake @testset "Norm equations" begin
  A = matrix_algebra(QQ, 2)
  O = order(A, basis(A))

  # QQ(sqrt(5)) embedded such that its intersection with O is ZZ[sqrt(5)]
  K, KtoA = Hecke._as_subfield(A, A(QQ[0 5; 1 0]))
  fl, t = Hecke.__neq_find_sol_in_order(O, KtoA, [ZZ(11)], [1], Vector{Any}(undef, 2))
  @test fl
  @test t in O
  @test abs(normred(t)) == 11

  # The equation order ZZ[13*sqrt(5)] is strictly smaller than O intersect K.
  # It has no element of norm 11 or -11, since neither is a square modulo 13.
  K, KtoA = Hecke._as_subfield(A, 13*A(QQ[0 5; 1 0]))
  fl, t = Hecke.__neq_find_sol_in_order(O, KtoA, [ZZ(11)], [1], Vector{Any}(undef, 2))
  @test fl
  @test t in O
  @test abs(normred(t)) == 11

  # ZZ[sqrt(17)] has no element of norm 2 or -2
  K, KtoA = Hecke._as_subfield(A, A(QQ[0 17; 1 0]))
  fl, t = Hecke.__neq_find_sol_in_order(O, KtoA, [ZZ(2)], [1], Vector{Any}(undef, 2))
  @test !fl
end
