@testset "Number fields" begin
  include("NumField/Elem.jl")
  include("NumField/Hilbert.jl")
  include("NumField/NfRel.jl")
  include("NumField/NfAbs.jl")
  include("NumField/QQ.jl")
  include("NumField/NonSimpleNumField.jl")
  include("NumField/CM.jl")
  include("NumField/Embedded.jl")
  include("NumField/Selmer.jl")
  include("NumField/InfinitePlaces.jl")
end
