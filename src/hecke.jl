module hecke

using Nemo

################################################################################
#
#  Import/export nightmare
#
################################################################################

# The following functions/types are not exported or we want to extend them
# So we have to import them explicitely

import Nemo: nf_elem, PariIdeal, NfNumberField, FmpzPolyRing, degree,
             denominator, den, num, lg, prime_decomposition, parent, length,
             norm, real, imag, inv, rows, getindex!, lll, hnf, cols, basis,
             trace, factor, mod, zero, pari_load, PariPolyRing,
             PariRationalField, PariQQ, pari_vec, hash, PolynomialRing, coeff,
             var, abs, min, iszero, one, sqrt, isone, deepcopy, rank, in,
             discriminant, log, sub, lift, FlintQQ, FlintZZ, elem_type

export NfNumberField, hash

import Base: show, minimum, rand, prod, copy, rand!, call, rand, ceil, round, 
             size, dot, in, powermod, ^, getindex, ==, <, >, +, *, /, -,
             getindex, setindex!, transpose, getindex, //, colon, div

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

###############################################################################
#
#   Library initialisation message
#
###############################################################################

function __init__()
   println("")
   print("Welcome to \n")
   print_with_color(:red, "
    ('-. .-.   ('-.             .-. .-')     ('-.   
   ( OO )  / _(  OO)            \\  ( OO )  _(  OO)  
   ,--. ,--.(,------.   .-----. ,--. ,--. (,------. 
   |  | |  | |  .---'  '  .--./ |  .'   /  |  .---' 
   |   .|  | |  |      |  |('-. |      /,  |  |     
   |       |(|  '--.  /_) |OO  )|     ' _)(|  '--.  
   |  .-.  | |  .--'  ||  |`-'| |  .   \\   |  .--'  
   |  | |  | |  `---.(_'  '--'\\ |  |\\   \\  |  `---. 
   `--' `--' `------'   `-----' `--' '--'  `------' 
   ")
   println()
   print("hecke version")
   print_with_color(:green, " 0.1 ")
   print("... \n ... which comes with absolutely ")
   print_with_color(:red, "no")
   print_with_color(:blue, " warranty")
   println(" whatsoever")
   println("")
   println("(c) 2015 by Claus Fieker and Tommy Hofmann")
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

type LowPrecisionCholesky <: Exception end
Base.showerror(io::IO, e::LowPrecisionCholesky) = print(io, e.var, "negative diagonaly in Cholesky, probably precision issue")

type LowPrecisionLLL <: Exception end
Base.showerror(io::IO, e::LowPrecisionLLL) = print(io, e.var, "trafo matrix has too large entries relative to precision in LLL")

function checkbounds(a::Int, b::Int) nothing; end;

################################################################################
#
#  "Submodules"
#
################################################################################

include("Sparse.jl")
include("Misc.jl")
include("LinearAlgebra.jl")
include("BigComplex.jl")
include("conjugates.jl")
include("NfMaximalOrder/GenNfOrd.jl")
include("NfOrder.jl")
include("misc.jl")
include("analytic.jl")
include("NfMaximalOrder.jl")

################################################################################
#
#  Extending Nemo types
#
################################################################################

const hecke_handle = get_handle()

const _get_nf_conjugate_data_arb, _set_nf_conjugate_data_arb =
            create_accessors(NfNumberField, acb_root_ctx, hecke_handle)

function conjugate_data_arb(K::NfNumberField)
  try
    c = _get_nf_conjugate_data_arb(K)
    return c
  catch
    c = acb_root_ctx(K.pol)
    _set_nf_conjugate_data_arb(K, c)
    return c
  end
end

################################################################################
#
#  (Temporary) global dictionaries
#
################################################################################

const _conjugate_data_dict = Dict{NfNumberField, acb_root_ctx}()

#function conjugate_data(K::NfNumberField)
#  if haskey(_conjugate_data_dict, K)
#    return _conjugate_data_dict[K]
#  else
#    z = acb_root_ctx(K.pol)
#    _conjugate_data_dict[K] = z
#    return z
#  end
#end
    
end

