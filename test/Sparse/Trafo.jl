@testset "Trafo" begin
  A = matrix(FlintZZ, [0 1 0 0 0;
                       0 0 4 0 0;
                       0 0 3 0 0;
                       0 0 0 4 0;
                       5 0 0 0 0])
  Asparse = sparse_matrix(A)

  v = fmpz[1, 2, 3, 4, 5]


  T = @inferred sparse_trafo_scale(2, fmpz(-1))
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [0 1 0 0 0;
                                           0 0 -4 0 0;
                                           0 0 3 0 0;
                                           0 0 0 4 0;
                                           5 0 0 0 0])
  @inferred Hecke.apply_right!(v, T)
  @test v == fmpz[1, -2, 3, 4, 5]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == fmpz[1, 2, 3, 4, 5]

  v = fmpz[1, -4, 3, 4, 5]

  T = @inferred sparse_trafo_swap(fmpz, 5, 4)
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [0 1 0 0 0;
                                           0 0 -4 0 0;
                                           0 0 3 0 0;
                                           5 0 0 0 0;
                                           0 0 0 4 0])
  @inferred Hecke.apply_right!(v, T)
  @test v == fmpz[1, -4, 3, 5, 4]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == fmpz[1, -4, 3, 4, 5]

  v = fmpz[1, -4, 3, 5, 4]

  T = @inferred sparse_trafo_add_scaled(3, 2, fmpz(2))
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [0 1 0 0 0;
                                           0 0 2 0 0;
                                           0 0 3 0 0;
                                           5 0 0 0 0;
                                           0 0 0 4 0])
  @inferred Hecke.apply_right!(v, T)
  @test v == fmpz[1, -4, -5, 5, 4]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == fmpz[1, -4, 3, 5, 4]

  v = fmpz[1, -4, -5, 5, 4]


  T = @inferred sparse_trafo_para_add_scaled(2, 3, fmpz(2), fmpz(-1), fmpz(3), fmpz(-2))
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [0 1 0 0 0;
                                           0 0 1 0 0;
                                           0 0 0 0 0;
                                           5 0 0 0 0;
                                           0 0 0 4 0])
  @inferred Hecke.apply_right!(v, T)
  @test v == fmpz[1, -23, 14, 5, 4]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == fmpz[1, -4, -5, 5, 4]

  v = fmpz[1, -23, 14, 5, 4]

  Asparse = sparse_matrix(FlintZZ, [1 1 0 0 0;
                                    0 1 2 0 0;
                                    0 0 1 2 1;
                                    0 0 0 4 0;
                                    0 0 0 0 1])
  Asparsec = copy(Asparse)

  B = matrix(FlintZZ, [1 2 5; 0 1 10; 0 0 -1])
  T = @inferred sparse_trafo_partial_dense(3, 3:5, 3:5, B)
  @inferred Hecke.apply_left!(Asparse, T)

  @test Asparse == sparse_matrix(FlintZZ, [1 1 0 0 0;
                                           0 1 2 0 0;
                                           0 0 1 10 6;
                                           0 0 0 4 10;
                                           0 0 0 0 -1])
  @inferred Hecke.apply_right!(v, T)
  @test v == fmpz[1, -23, 14, 33, 116]

  Tinv = inv(T)
  @inferred Hecke.apply_right!(v, Tinv)
  @inferred Hecke.apply_left!(Asparse, Tinv)
  @test Asparse == Asparsec
  @test v == fmpz[1, -23, 14, 5, 4]

  v = fmpz[1, -23, 62, 85, 108]

  Asparse = sparse_matrix(FlintZZ, [1 1 0 0 0;
                                    0 0 0 0 0;
                                    0 0 1 10 4;
                                    0 0 4 28 10;
                                    0 0 7 46 16])
  Asparsec = copy(Asparse)

  T = @inferred sparse_trafo_move_row(fmpz, 2, 5)
  @inferred Hecke.apply_left!(Asparse, T)
  @test Asparse == sparse_matrix(FlintZZ, [1 1 0 0 0;
                                           0 0 1 10 4;
                                           0 0 4 28 10;
                                           0 0 7 46 16;
                                           0 0 0 0 0])

  @inferred Hecke.apply_right!(v, T)
  @test v == fmpz[1, 108, -23, 62, 85]

  Tinv = inv(T)
  Hecke.apply_left!(Asparse, Tinv)
  @test Asparse == Asparsec
  @inferred Hecke.apply_right!(v, Tinv)
  @test v == fmpz[1, -23, 62, 85, 108]
end
