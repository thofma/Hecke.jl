@testset "NfRel" begin
  println("NfRel/NfRelOrd.jl")
  @time include("NfRel/NfRelOrd.jl")
  println("NfRel/Ideal.jl")
  @time include("NfRel/Ideal.jl")
  println("NfRel/FracIdeal.jl")
  @time include("NfRel/FracIdeal.jl")
  println("NfRel/NfRel.jl")
  @time include("NfRel/NfRel.jl")
  println("NfRel/Elem.jl")
  @time include("NfRel/Elem.jl")
  println("NfRel/NEQ_Kirschmer.jl")
  @time include("NfRel/NEQ_Kirschmer.jl")
end
