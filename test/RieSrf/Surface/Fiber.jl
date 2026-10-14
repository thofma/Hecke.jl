@testset "Fiber" begin
  @testset "Fibers with multiplicities" begin
    for (f, x0, expected) in [
        (y^2 - x^2*(x + 1)*(x - 2)*(x - 3),   0, [2]),     # node (genus 1)
        (y^2 - x^3*(x - 1)*(x - 2),           0, [2]),     # cusp (genus 1)
        (y^3 - x^2*(x - 1)*(x + 1)*(x - 2),   0, [3]),     # triple root (genus 3)
        (x*y^3 + y^2 - x^5 - 1,               0, [1, 1]),  # one root goes to infinity
        (y^3 - x^4 + 1,                       1, [3])]     # ordinary branch point
      RS = _rs(f, 100)
      ys, mults = RSM.fiber_with_multiplicities(RS, RSM.complex_field(RS)(x0))
      @test sort(mults) == sort(expected)
    end
    # every discriminant point: multiplicities add up to the y-degree there
    for (name, f, g) in FAST_CURVES
      RS = _rs(f, 100)
      m = RSM.original_model(RS).degree[1]
      for xk in RSM.discriminant_points(RS)
        ys, mults = RSM.fiber_with_multiplicities(RS, xk)
        @test sum(mults) <= m        # the rest lies at infinity
      end
    end
  end
end
