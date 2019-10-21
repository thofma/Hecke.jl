using Hecke

using Test

using LinearAlgebra

Hecke.assertions(true)

k, a = quadratic_field(5)
@assert fmpz(1) - a == -(a - 1)
@assert 1 - a == -(a - 1)

@time include("NumField.jl")
@time include("AlgAss.jl")
@time include("AlgAssAbsOrd.jl")
@time include("AlgAssRelOrd.jl")
@time include("EllCrv.jl")
@time include("GrpAb.jl")
@time include("Grp.jl")
@time include("LinearAlgebra.jl")
@time include("Map.jl")
@time include("Misc.jl")
@time include("NfAbs.jl")
@time include("NfOrd.jl")
@time include("NfRel.jl")
@time include("RCF.jl")
@time include("Examples.jl")
@time include("Sparse.jl")
@time include("QuadForm.jl")
@time include("LocalField.jl")
