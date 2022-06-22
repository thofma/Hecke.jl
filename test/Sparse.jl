@testset "Sparse" begin
  include("Sparse/Row.jl")
  include("Sparse/Matrix.jl")
  include("Sparse/Trafo.jl")
  include("Sparse/HNF.jl")
  include("Sparse/Rref.jl")
  include("Sparse/Solve.jl")
  include("Sparse/DiscLog.jl")
  include("Sparse/IndexCalculus.jl")
end
