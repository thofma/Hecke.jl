@testset "Trafo" begin
  A = matrix(FlintZZ, [0 1 0 0 0;
                       0 0 4 0 0;
                       0 0 3 0 0;
                       0 0 0 4 0;
                       5 0 0 0 0])
  Asparse = sparse_matrix(A)

  v = ZZRingElem[1, 2, 3, 4, 5]


  T = @inferred Hecke.sparse_trafo_scale(2, ZZRingElem(-1))
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [0 1 0 0 0;
                                           0 0 -4 0 0;
                                           0 0 3 0 0;
                                           0 0 0 4 0;
                                           5 0 0 0 0])
  @inferred Hecke.apply_right!(v, T)
  @test v == ZZRingElem[1, -2, 3, 4, 5]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == ZZRingElem[1, 2, 3, 4, 5]

  v = ZZRingElem[1, -4, 3, 4, 5]

  T = @inferred Hecke.sparse_trafo_swap(ZZRingElem, 5, 4)
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [0 1 0 0 0;
                                           0 0 -4 0 0;
                                           0 0 3 0 0;
                                           5 0 0 0 0;
                                           0 0 0 4 0])
  @inferred Hecke.apply_right!(v, T)
  @test v == ZZRingElem[1, -4, 3, 5, 4]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == ZZRingElem[1, -4, 3, 4, 5]

  v = ZZRingElem[1, -4, 3, 5, 4]

  T = @inferred Hecke.sparse_trafo_add_scaled(3, 2, ZZRingElem(2))
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [0 1 0 0 0;
                                           0 0 2 0 0;
                                           0 0 3 0 0;
                                           5 0 0 0 0;
                                           0 0 0 4 0])
  @inferred Hecke.apply_right!(v, T)
  @test v == ZZRingElem[1, -4, -5, 5, 4]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == ZZRingElem[1, -4, 3, 5, 4]

  v = ZZRingElem[1, -4, -5, 5, 4]


  T = @inferred Hecke.sparse_trafo_para_add_scaled(2, 3, ZZRingElem(2), ZZRingElem(-1), ZZRingElem(3), ZZRingElem(-2))
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [0 1 0 0 0;
                                           0 0 1 0 0;
                                           0 0 0 0 0;
                                           5 0 0 0 0;
                                           0 0 0 4 0])
  @inferred Hecke.apply_right!(v, T)
  @test v == ZZRingElem[1, -23, 14, 5, 4]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == ZZRingElem[1, -4, -5, 5, 4]

  v = ZZRingElem[1, -23, 14, 5, 4]

  Asparse = sparse_matrix(FlintZZ, [1 1 0 0 0;
                                    0 1 2 0 0;
                                    0 0 1 2 1;
                                    0 0 0 4 0;
                                    0 0 0 0 1])
  Asparsec = copy(Asparse)

  B = matrix(FlintZZ, [1 2 5; 0 1 10; 0 0 -1])
  T = @inferred Hecke.sparse_trafo_partial_dense(3, 3:5, 3:5, B)
  @inferred Hecke.apply_left!(Asparse, T)

  @test Asparse == sparse_matrix(FlintZZ, [1 1 0 0 0;
                                           0 1 2 0 0;
                                           0 0 1 10 6;
                                           0 0 0 4 10;
                                           0 0 0 0 -1])
  @inferred Hecke.apply_right!(v, T)
  @test v == ZZRingElem[1, -23, 14, 33, 116]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @inferred Hecke.apply_left!(Asparse, Tinv)
  @test Asparse == Asparsec
  @test v == ZZRingElem[1, -23, 14, 5, 4]

  v = ZZRingElem[1, -23, 62, 85, 108]

  Asparse = sparse_matrix(FlintZZ, [1 1 0 0 0;
                                    0 0 0 0 0;
                                    0 0 1 10 4;
                                    0 0 4 28 10;
                                    0 0 7 46 16])

  Bsparse = sparse_matrix(FlintZZ, [1  0 0 1 0;
                                    0  0 0 0 0;
                                    0 10 1 0 4;
                                    0 28 4 0 10;
                                    0 46 7 0 16])


  Asparsec = copy(Asparse)

  T = @inferred Hecke.sparse_trafo_move_row(ZZRingElem, 2, 5)
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [1 1 0 0 0;
                                           0 0 1 10 4;
                                           0 0 4 28 10;
                                           0 0 7 46 16;
                                           0 0 0 0 0])

  @inferred Hecke.apply_right!(v, T)
  @test v == ZZRingElem[1, 108, -23, 62, 85]

  Tinv = inv(T)
  Hecke.apply_left!(Asparse, Tinv)
  @test Asparse == Asparsec
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == ZZRingElem[1, -23, 62, 85, 108]

  swap_cols!(Bsparse, 2, 4)
  @test Bsparse == Asparse
end
