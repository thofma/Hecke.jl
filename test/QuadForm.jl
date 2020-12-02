@testset "Quadratic and hermitian forms" begin
  @time include("QuadForm/Basic.jl")
  @time include("QuadForm/Lattices.jl")
  @time include("QuadForm/Genus.jl")
  @time include("QuadForm/Morphism.jl")
  @time include("QuadForm/Enumeration.jl")
  @time include("QuadForm/MassQuad.jl")
  @time include("QuadForm/MassHerm.jl")
  @time include("QuadForm/Quad.jl")
  @time include("QuadForm/QuadBin.jl")
end
