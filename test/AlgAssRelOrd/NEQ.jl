@with_polymake @testset "Norm equations" begin
  k, = Hecke.rationals_as_number_field()
  Ok = maximal_order(k)
  A = matrix_algebra(k, 2)
  O = order(A, basis(A))

  # k(sqrt(5)) embedded such that its intersection with O is Ok[sqrt(5)]
  L, LtoA = Hecke._as_subfield(A, A(matrix(k, 2, 2, [0, 5, 1, 0])))
  K, KtoL, ktoK = Hecke.simplified_absolute_field(L)
  P = prime_decomposition(Ok, 11)[1][1]
  fl, t = Hecke.__neq_find_sol_in_order(O, LtoA, KtoL, ktoK, [P], [1], Vector{Any}(undef, 3))
  @test fl
  @test t in O
  @test normred(t) * Ok == P

  # The equation order Ok[13*sqrt(5)] is strictly smaller than O intersect L.
  # It has no element of norm 11 or -11, since neither is a square modulo 13.
  L, LtoA = Hecke._as_subfield(A, 13*A(matrix(k, 2, 2, [0, 5, 1, 0])))
  K, KtoL, ktoK = Hecke.simplified_absolute_field(L)
  fl, t = Hecke.__neq_find_sol_in_order(O, LtoA, KtoL, ktoK, [P], [1], Vector{Any}(undef, 3))
  @test fl
  @test t in O
  @test normred(t) * Ok == P

  # Ok[sqrt(17)] has no element of norm 2 or -2
  L, LtoA = Hecke._as_subfield(A, A(matrix(k, 2, 2, [0, 17, 1, 0])))
  K, KtoL, ktoK = Hecke.simplified_absolute_field(L)
  P = prime_decomposition(Ok, 2)[1][1]
  fl, t = Hecke.__neq_find_sol_in_order(O, LtoA, KtoL, ktoK, [P], [1], Vector{Any}(undef, 3))
  @test !fl
end
