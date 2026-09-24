@testset "module namespace" begin
  @test parentmodule(Hecke.EmbeddedModule) === Hecke.EmbeddedModules
  @test Hecke.EmbeddedModules.EmbeddedModule === Hecke.EmbeddedModule
  @test Hecke.EmbeddedModules.EmbeddedModuleElem === Hecke.EmbeddedModuleElem
  @test Hecke.EmbeddedModules.basis_matrix === Hecke.basis_matrix
  @test Hecke.EmbeddedModules.embedded_module === Hecke.embedded_module
  @test Hecke.EmbeddedModules.fractional_ideal === Hecke.fractional_ideal
  @test Hecke.EmbeddedModules.index === Hecke.index
  @test Hecke.EmbeddedModules.ring === Hecke.ring
end
