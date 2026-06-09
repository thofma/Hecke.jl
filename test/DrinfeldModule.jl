################################################################################
#
#  test/DrinfeldModule.jl : Tests for Drinfeld modules
#
################################################################################

@testset "DrinfeldModule" begin
  include("DrinfeldModule/ore_poly_ring.jl")
  include("DrinfeldModule/drinfeld_module.jl")
  include("DrinfeldModule/morphism.jl")
  include("DrinfeldModule/finite_drinfeld_module.jl")
  include("DrinfeldModule/carlitz_module.jl")
end
