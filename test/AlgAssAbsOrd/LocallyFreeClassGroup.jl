@testset "Locally free class group of group algebras" begin
  G = small_group(8, 4)
  A = AlgAss(AlgGrp(FlintQQ, G))[1]
  O = Order(A, basis(A))
  C = Hecke.locally_free_class_group(O)
  @test C.snf == fmpz[ 2 ]

  G = small_group(10, 2)
  A = AlgAss(AlgGrp(FlintQQ, G))[1]
  O = Order(A, basis(A))
  C = Hecke.locally_free_class_group(O)
  @test C.snf == fmpz[]

  G = small_group(12, 3)
  A = AlgAss(AlgGrp(FlintQQ, G))[1]
  O = Order(A, basis(A))
  C = Hecke.locally_free_class_group(O)
  @test C.snf == fmpz[]
end


@testset "Locally free class group of matrix algebras" begin
  Qx, x = FlintQQ["x"]
  f = x^2 + 47
  K, a = number_field(f, "a")
  A = AlgAss(MatrixAlgebra(K, 2))
  A, _, _ = Hecke.restrict_scalars(A, FlintQQ)
  O = MaximalOrder(A)
  C = Hecke.locally_free_class_group(O) # == class_group(K)
  @test C.snf == fmpz[ 5 ]

  f = x^2 + 26
  K, a = number_field(f, "a")
  A = AlgAss(MatrixAlgebra(K, 2))
  A, _, _ = Hecke.restrict_scalars(A, FlintQQ)
  O = MaximalOrder(A)
  C = Hecke.locally_free_class_group(O) # == class_group(K)
  @test C.snf == fmpz[ 6 ]
end
