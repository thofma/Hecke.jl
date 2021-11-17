using Test

using LinearAlgebra

using Random
using RandomExtensions

const rng = MersenneTwister()
const rand_seed = rand(UInt128)

# tests if rand(rng, args...) gives reproducible results
function reproducible(args...)
  Random.seed!(rng)
  x = rand(rng, args...)
  Random.seed!(rng, rng.seed)
  x == rand(rng, args...)
end

Hecke.assertions(true)

if long_test
  macro long_test(ex)
    ex
  end
else
  macro long_test(ex)
    return :nothing
  end
end

if _with_gap
  macro with_gap(ex)
    ex
  end
else
  macro with_gap(ex)
    return :nothing
  end
end
