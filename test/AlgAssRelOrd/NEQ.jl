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

  # norm_equation for maximal orders: 2x2 and 3x3 matrix algebras, definite
  # and indefinite quaternion algebras, units, composite norms, a non-rational
  # base field with class number 2 and one with units of norm -1
  Qx, x = QQ["x"]
  k2, w = number_field(x^2 - 2, "w")
  k3, z = number_field(x^2 + 5, "z")
  for (A, as) in [(quaternion_algebra(k, -1, -1), [1, 2, 3, 21]),
                  (quaternion_algebra(k, -1, 3), [-1, 3, -6]),
                  (matrix_algebra(k, 2), [-1, 3, 6, -3]),
                  (matrix_algebra(k, 3), [2, -5]),
                  (quaternion_algebra(k2, -1, -1), [3 + 2*w, 2 + w]),
                  (matrix_algebra(k2, 2), [-1, 1 + w, -3]),
                  (matrix_algebra(k3, 2), [-1, 1 + z, 2])]
    O = maximal_order(A)
    Ok = base_ring(O)
    for a in as
      d, i = Hecke.norm_equation([O], Ok(a))
      @test i == 1
      @test d in O
      @test normred(d) == a
    end
  end

  # No solutions: the reduced norm of a definite quaternion algebra is
  # totally positive
  for (A, a) in [(quaternion_algebra(k, -1, -1), -3),
                 (quaternion_algebra(k2, -1, -1), 1 + w)]
    O = maximal_order(A)
    NC = Hecke.NormCache(A, [O], base_ring(O)(a))
    fl, _ = Hecke._norm_equation_relative(NC, 1)
    @test !fl
  end
end
