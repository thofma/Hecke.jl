module hecke

using Nemo

################################################################################
#
#  Import/export nightmare
#
################################################################################

# The following functions/types are not exported or
# we want to extend them
# So we have to import them explicitely



import Nemo: nf_elem, PariIdeal, NfNumberField, FmpzPolyRing, degree,
  denominator, den, num, lg, prime_decomposition,
  parent, length, norm, real, imag, inv, rows,
  getindex!, lll, hnf, cols, basis, trace, factor, mod, zero,
  pari_load, PariPolyRing, PariRationalField, PariQQ,
  pari_vec, hash, PolynomialRing, coeff, var, abs, min, iszero, one, sqrt, isone, deepcopy, rank

export NfNumberField, hash

import Base: show, minimum, rand, prod, copy, rand!

# To make all exported Nemo functions visible to someone using "using hecke"
# we have to export everything again

for i in names(Nemo)
  eval(Expr(:export, i))
end

export @vprint, @hassert, @vtime, add_verbose_scope, get_verbose_level,
       set_verbose_level, add_assert_scope, get_assert_level, set_assert_level

################################################################################
#
#  Verbose printing
#
################################################################################

VERBOSE_SCOPE = Symbol[]

VERBOSE_LOOKUP = Dict{Symbol, Int}()

function add_verbose_scope(s::Symbol)
  !(s in VERBOSE_SCOPE) && push!(VERBOSE_SCOPE, s)
  nothing
end

macro vprint(args...)
  if length(args) == 2
    quote
      if get_verbose_level($(args[1])) >= 1
        print($(args[2]))
      end
    end
  elseif length(args) == 3
    quote
      if get_verbose_level($(args[1])) >= $(args[2])
        print($(args[3]))
      end
    end
  end
end

macro v_do(args...)
  if length(args) == 2
    quote
      if get_verbose_level($(args[1])) >= 1
       $(args[2])
      end
    end
  elseif length(args) == 3
    quote
      if get_verbose_level($(args[1])) >= $(args[2])
        $(args[3])
      end
    end
  end
end


function set_verbose_level(s::Symbol, l::Int)
  !(s in VERBOSE_SCOPE) && error("Not a valid symbol")
  VERBOSE_LOOKUP[s] = l
end

function get_verbose_level(s::Symbol)
  !(s in VERBOSE_SCOPE) && error("Not a valid symbol")
  return get(VERBOSE_LOOKUP, s, 0)::Int
end

################################################################################
#
#  Assertions
#
################################################################################

ASSERT_SCOPE = Symbol[]

ASSERT_LOOKUP = Dict{Symbol, Int}()

function add_assert_scope(s::Symbol)
  !(s in ASSERT_SCOPE) && push!(ASSERT_SCOPE, s)
  nothing
end

function set_assert_level(s::Symbol, l::Int)
  !(s in ASSERT_SCOPE) && error("Not a valid symbol")
  ASSERT_LOOKUP[s] = l
end

function get_assert_level(s::Symbol)
  !(s in ASSERT_SCOPE) && error("Not a valid symbol")
  return get(ASSERT_LOOKUP, s, 0)::Int
end

macro hassert(args...)
  if length(args) == 2
    quote
      if get_assert_level($(args[1])) >= 1
        @assert $(args[2])
      end
    end
  elseif length(args) == 3
    quote
      if get_assert_level($(args[1])) >= $(args[2])
        @assert $(args[3])
      end
    end
  end
end

################################################################################
#
#  Verbose time printing
#
################################################################################

macro vtime(args...)
  if length(args) == 2
    msg = string(args[2])
    quote
      if get_verbose_level($(args[1])) >= 1
        local t0 = time_ns()
        local val = $(esc(args[2]))
        println((time_ns()-t0)/1e9, " @ ", $msg)
        val
      else
        local val2 = $(esc(args[2]))
        val2
      end
    end
  elseif length(args) == 3
    msg = string(args[3])
    quote
      if get_verbose_level($(args[1])) >= $(args[2])
        local t0 = time_ns()
        local val = $(esc(args[3]))
        println((time_ns()-t0)/1e9, " @ ", $msg)
        val
      else
        local val2 = $(esc(args[3]))
        val2
      end
    end
  end
end

################################################################################
#
#  "Submodules"
#
################################################################################

include("LinearAlgebra.jl")
include("Sparse.jl")
include("Misc.jl")
include("BigComplex.jl")
include("conjugates.jl")
include("MaximalOrderIdeals.jl")
include("NfMaximalOrder/GenNfOrd.jl")
include("NfOrder.jl")
include("misc.jl")
include("NfMaximalOrder.jl")
#include("PrimeDec.jl")
#include("Clgp.jl")
end
