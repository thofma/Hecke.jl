@testset "NfAbs" begin
  include("NfAbs/Conjugates.jl")
  include("NfAbs/NonSimple.jl")
  include("NfAbs/Hilbert.jl")
  include("NfAbs/Subfields.jl")
  include("NfAbs/Elem.jl")
  include("NfAbs/Simplify.jl")
  include("NfAbs/NormRelation.jl")
  include("NfAbs/MPolyGcd.jl")
end
