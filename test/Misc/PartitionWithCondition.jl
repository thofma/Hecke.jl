@testset "Misc/PartitionWithCondition" begin
  x = partitions_with_condition(5, 3, 7)
  y = iterate(x)
  y = iterate(x,y[2])
  @test y[1] == [1, 1, 3]

  a = partitions_with_condition(2, 1, 0)
  @test iterate(a,iterate(a)[2]) == nothing

  @test iterate(partitions_with_condition(2,1,1)) == nothing

  n = 0
  for i in partitions_with_condition(7, 4, 12)
    n += 1
  end
  @test n == 5
end
