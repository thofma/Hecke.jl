@testset "Misc/PartitionsWithCondition" begin
  x = Hecke.partitions_with_condition(5, 3, 7)
  y = iterate(x)
  y = iterate(x, y[2])
  @test y[1] == [1, 1, 3]

  a = Hecke.partitions_with_condition(2, 1, 0)
  @test iterate(a,iterate(a)[2]) == nothing

  @test iterate(Hecke.partitions_with_condition(2,1,1)) == nothing

  L = [copy(i) for i in Hecke.partitions_with_condition(7, 4, 12)]
  @test length(L) == 10
  @test all(sum(i)==7 for i in L)
  @test all(sum(i[j]*(j-1) for j in 1:4)==12 for i in L)

  n = 0
  for i in Hecke.partitions_with_condition(2, 2, 1)
    n += 1
  end
  @test n == 1
end
