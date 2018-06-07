@testset "MultiQuad" begin

  include(Pkg.dir("Hecke") * "/examples/MultiQuad.m")

  c = MultiQuad.multi_quad(fmpz[3,5,7], 10)
  d = MultiQuad.simplify(c)
  @test Hecke.class_group_get_pivot_info(d) == (4, IntSet([2, 4]))
  e = MultiQuad.saturate(d, 2)
  @test Hecke.class_group_get_pivot_info(e) == (4, IntSet([2, 4]))
  f = MultiQuad.saturate(e, 2)
  @test Hecke.class_group_get_pivot_info(f) == (1, IntSet([]))

end  


