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

  R, _ = residue_ring(ZZ, 12)

  Asparse = sparse_matrix(R, [6 1 0])
  @test scale_row!(Asparse, 1, R(2)) == sparse_matrix(R, [0 2 0])
  @test isone(Asparse.nnz)
  @test !(zero(R) in Asparse[1].values)

  Bsparse = sparse_matrix(R, [4 0; 1 0; 3 3; 2 6])
  @test Hecke.add_scaled_col!(Bsparse, 1, 2, R(3)) == sparse_matrix(R, [4 0; 1 3; 3 0; 2 0])
  @test Bsparse.nnz == 5
  for i = 1:nrows(Bsparse)
    @test !(zero(R) in Bsparse[i].values)
  end

  Csparse = sparse_matrix(R, [4 0 0 1 2 0 1; 0 1 6 2 3 1 1])
  @test Hecke.transform_row!(Csparse, 1, 2, R(3), R(2), R(3), zero(R)) == sparse_matrix(R, [0 2 0 7 0 2 5; 0 0 0 3 6 0 3])
  @test Csparse.nnz == 7
  for i = 1:nrows(Csparse)
    @test !(zero(R) in Csparse[i].values)
  end
end
