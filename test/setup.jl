using Test

using LinearAlgebra

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
