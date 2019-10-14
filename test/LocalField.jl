@testset "LocalField ..." begin
  println("Conjugates.jl")
  @time include("LocalField/Conjugates.jl")
  @time include("LocalField/Eisenstein.jl")  
  #println("Poly.jl")
  #@time include("LocalField/Poly.jl")
end
