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

short_test = false

if "short" in ARGS || get(ENV, "HECKE_TESTSHORT", "false") in ["1", "true"]
  short_test = true
end

long_test = false

if "long" in ARGS || get(ENV, "HECKE_TESTLONG", "false") in ["1", "true"]
  long_test = true
end

if long_test
  macro long(ex)
    ex
  end
else
  macro long(ex)
    return :nothing
  end
end
