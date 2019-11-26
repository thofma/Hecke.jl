include("LocalField/pAdic.jl")
include("LocalField/qAdic.jl")
include("LocalField/Ring.jl")

# Stuff that should honestly be somewhere else...
include("LocalField/MoveSomewhereElse.jl")

# New Eisenstein stuff.
include("LocalField/EisensteinTypes.jl")
include("LocalField/Eisenstein.jl")
include("LocalField/Eisenstein_elem.jl")
include("LocalField/Eisenstein_roots.jl")

# NALocalField abstract methods.
include("LocalField/NALocalField_elem.jl")

# NACompletionMap map type
include("LocalField/CompletionMap.jl")

# Conjugates, regulators, and local polynomials.
include("LocalField/Conjugates.jl")
include("LocalField/LocalRegulator.jl")
include("LocalField/Poly.jl")
include("LocalField/Completions.jl")
