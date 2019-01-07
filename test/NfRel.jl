@testset "NfRel" begin
  println("NfRel/NfRelOrd.jl")
  @time include("NfRel/NfRelOrd.jl")
  println("NfRel/NfRelOrdIdl.jl")
  @time include("NfRel/NfRelOrdIdl.jl")
  println("NfRel/NfRelOrdFracIdl.jl")
  @time include("NfRel/NfRelOrdFracIdl.jl")
  println("NfRel/NfRel.jl")
  @time include("NfRel/NfRel.jl")
end
