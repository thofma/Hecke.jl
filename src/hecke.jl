module hecke

# package code goes here

using Nemo

# The following functions/types are not exported or
# we want to extend them
# So we have to import them explicitely

import Nemo: nf_elem, PariIdeal, NfNumberField, FmpzPolyRing, degree,
  denominator, den, __prime_ideal_components, num, lg, prime_decomposition,
  parent, _factor, length, _lift, norm, prod, varstring, real, imag, inv, rows,
  getindex!, lll, hnf, cols, MaximalOrder, basis, trace, factor, mod, zero,
  representation_mat

import Base: show  


# To make all exported Nemo functions visible to someone using "using hecke"
# we have to export everything again

for i in names(Nemo)
  eval(Expr(:export, i))
end

export setverbose, getverbose, @vprint, @assertl, setassert, getassert

VERBOSE_LEVEL = [1]

function setverbose(i::Int)
  VERBOSE_LEVEL[end] = i
  if i == 1
    eval(parse("macro vprint(x); :(print(\$x)); end;"))
  else
    eval(parse("macro vprint(x); nothing; end;"))
  end
end

function getverbose()
  return VERBOSE_LEVEL[end]
end

setverbose(VERBOSE_LEVEL[end])

ASSERT_LEVEL = [0]

function setassert(i::Int)
  ASSERT_LEVEL[end] = i
end

function getassert()
  return ASSERT_LEVEL[end]
end

function setassert(i::Int)
  ASSERT_LEVEL[end] = i
  eval(parse("macro assertl(lvl, ex, msgs...)
  if lvl <= getassert()
    msg = isempty(msgs) ? ex : msgs[1]                              
    if !isempty(msgs) && isa(msg, Expr)                             
      msg = :(string(\$(esc(msg))))                                
    else
      msg = string(msg)                                           
    end                                                             
    :(\$(esc(ex)) ? \$(nothing) : throw(AssertionError(\$msg)))        
  end
  end"))
end

setassert(ASSERT_LEVEL[end])

include("Sparse.jl")
include("BigComplex.jl")
include("conjugates.jl")
include("misc.jl")
include("PrimeDec.jl")
include("MaximalOrderIdeals.jl")
include("LinearAlgebra.jl")
include("Clgp.jl")
include("NfOrder.jl")


end # module
