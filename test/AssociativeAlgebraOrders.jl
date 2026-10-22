@testset "Associative algebra orders" begin
  include("AssociativeAlgebraOrders/setup_tests.jl")
  include("AssociativeAlgebraOrders/Basics.jl")
  include("AssociativeAlgebraOrders/Elements.jl")
  include("AssociativeAlgebraOrders/Arithmetic.jl")
  include("AssociativeAlgebraOrders/Multipliers.jl")
  include("AssociativeAlgebraOrders/Invariants.jl")
  include("AssociativeAlgebraOrders/Ideals.jl")
end
