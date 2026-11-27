using Test

using Hecke.LinearAlgebra

using Hecke.Random
using Hecke.RandomExtensions

import Hecke.AbstractAlgebra

import Hecke: mul!

const rng = MersenneTwister()

# tests if rand(rng, args...) gives reproducible results
function reproducible(args...)
  rng1 = copy(rng)
  x = rand(rng1, args...)
  rng2 = copy(rng)
  return x == rand(rng2, args...)
end

enable_assertions = get(ENV, "HECKE_TEST_ASSERTIONS",
                        get(ENV, "CI", "false") == "true" ? "false" : "true")
Hecke.assertions(enable_assertions in ["1", "true"])

if (isdefined(Hecke, :long_test) && Hecke.long_test) ||
   (isdefined(Main, :long_test) && Main.long_test)
  macro long_test(ex)
    ex
  end
else
  macro long_test(ex)
    return :nothing
  end
end

if (isdefined(Hecke, :_with_gap) && Hecke._with_gap) ||
   (isdefined(Main, :_with_gap) && Main._with_gap)
  macro with_gap(ex)
    ex
  end
else
  macro with_gap(ex)
    return :nothing
  end
end

if (isdefined(Hecke, :_with_polymake) && Hecke._with_polymake) ||
   (isdefined(Main, :_with_polymake) && Main._with_polymake)
  macro with_polymake(ex)
    ex
  end
else
  macro with_polymake(ex)
    return :nothing
  end
end

# The ring interface requires divexact by zero to throw DivideError.
# TODO: remove once the ring interface tests this
function test_divexact_by_zero(R)
  is_trivial(R) && return
  for check in (true, false)
    @test_throws DivideError divexact(one(R), zero(R); check)
    @test_throws DivideError divexact(zero(R), zero(R); check)
  end
end
