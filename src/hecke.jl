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
