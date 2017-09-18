@testset "Finitely generated abelian groups" begin
  include("GrpAb/GrpAbFinGen.jl")
  include("GrpAb/Elem.jl")
  include("GrpAb/SubgroupEnum.jl")
  include("GrpAb/Map.jl")
end

#Base.Test.print_test_results(r, 3) 
