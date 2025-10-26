@testset "Norm equation" begin
  k, = quadratic_field(-2)
  fl, a = is_norm(k, 2)
  @test parent(a) === k && norm(a) == 2
  fl, a = Hecke.is_norm_fac_elem(k, 2)
  @test a isa FacElem && norm(a) == 2
end
