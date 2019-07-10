@testset "Matrix algebras" begin

  @testset "Construction" begin

    M1 = matrix(FlintQQ, [ 1 1; 0 1])
    M2 = matrix(FlintQQ, [ 1 0; 1 1])
    A = matrix_algebra(FlintQQ, [ M1, M2 ])
    @test dim(A) == 4

    QG = group_algebra(FlintQQ, small_group(2, 1))
    M1 = matrix(QG, [ 1 1; 0 1])
    M2 = matrix(QG, [ 1 0; 1 1])
    A = matrix_algebra(FlintQQ, QG, [ M1, M2 ])
    @test dim(A) == 4
  end

end
