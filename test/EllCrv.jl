@testset "Elliptic curves" begin
  include("EllCrv/EllCrv.jl")
  include("EllCrv/Finite.jl")
  include("EllCrv/Heights.jl")
  include("EllCrv/Isogeny.jl")
  include("EllCrv/Isomorphisms.jl")
  include("EllCrv/MinimalModels.jl")
  include("EllCrv/Models.jl")
  include("EllCrv/MordellWeilRank.jl")
  include("EllCrv/Torsion.jl")
  include("EllCrv/Twists.jl")
end
