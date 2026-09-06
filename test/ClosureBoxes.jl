# Captured variables that are reassigned force Julia to allocate a `Core.Box`,
# which defeats type inference. `Test.detect_closure_boxes` exists since
# Julia 1.14.
if isdefined(Test, :detect_closure_boxes)
  @testset "Closure boxes" begin
    mods = Module[Hecke]
    for ext in (:GAPExt, :PolymakeExt)
      m = Base.get_extension(Hecke, ext)
      m === nothing || push!(mods, m)
    end
    boxes = Test.detect_closure_boxes(mods...)
    for (m, vars) in boxes
      println("Boxed variable(s) ", join(vars, ", "), " in ", m)
    end
    @test length(boxes) == 0
  end
end
