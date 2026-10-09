@testset "Embedded module maps" begin
  include("Map/Basics.jl")
  include("Map/Embedding.jl")
  include("Map/PID.jl")
  include("Map/PIDQuotient.jl")
  include("Map/QuotientEmbeddedModule.jl")
  include("Map/PIDReduction.jl")
end
