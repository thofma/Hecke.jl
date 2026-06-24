@testset "Hyperelliptic curves" begin
  include("HypellCrv/HypellCrv.jl")
  include("HypellCrv/G2Invs.jl")  
  include("HypellCrv/G2Rec.jl")
  include("HypellCrv/G2Twists.jl")
  include("HypellCrv/Auxiliary.jl")
  include("HypellCrv/Isomorphisms.jl")
end
