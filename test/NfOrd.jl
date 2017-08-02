r = @testset "Orders in absolute number fields" begin
  include("NfOrd/NfOrd.jl")
  include("NfOrd/Elem.jl")
  include("NfOrd/Ideal.jl")
  include("NfOrd/FracIdl.jl")
  include("NfOrd/ResidueRing.jl")
end

# for 0.6
#Base.Test.print_test_results(r, 1) 
