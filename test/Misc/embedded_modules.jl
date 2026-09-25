@testset "Embedded modules" begin
  include("embedded_modules/Types.jl")
  include("embedded_modules/Elements.jl")
  include("embedded_modules/Basics.jl")
  include("embedded_modules/Arithmetic.jl")
  include("embedded_modules/Containment.jl")
  include("embedded_modules/Quotients.jl")
end
