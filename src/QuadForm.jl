# Types
include("QuadForm/Types.jl")
include("QuadForm/Quad/Types.jl")
include("QuadForm/Herm/Types.jl")

# Binary quadratic forms
include("QuadForm/QuadBin.jl")

# Misc things that need to be sorted
include("QuadForm/Misc.jl")

# Functionality for spaces
include("QuadForm/Spaces.jl")

# Functionality for lattices
include("QuadForm/Lattices.jl")

# Functionality for pseudo matrices
include("QuadForm/PseudoMatrices.jl")

# Torsion
include("QuadForm/Torsion.jl")

# Quadratic
include("QuadForm/Quad/Spaces.jl")
include("QuadForm/Quad/Lattices.jl")
include("QuadForm/Quad/ZLattices.jl")
include("QuadForm/Quad/NormalForm.jl")
include("QuadForm/Quad/Genus.jl")
include("QuadForm/Quad/GenusRep.jl")
include("QuadForm/Quad/Legacy.jl")
include("QuadForm/Quad/ZGenus.jl")
include("QuadForm/Quad/PadicLift.jl")
include("QuadForm/Quad/ZGenusRep.jl")

# Hermitian
include("QuadForm/Herm/Spaces.jl")
include("QuadForm/Herm/Lattices.jl")
include("QuadForm/Herm/Genus.jl")
include("QuadForm/Herm/GenusRep.jl")
include("QuadForm/Herm/Mass.jl")
include("QuadForm/Herm/Legacy.jl")
include("QuadForm/Herm/LocallyIsometricSublattice.jl")

include("QuadForm/Morphism.jl")
include("QuadForm/ShortVectors.jl")
include("QuadForm/Database.jl")
include("QuadForm/Enumeration.jl")
include("QuadForm/LineOrbits.jl")
include("QuadForm/MassQuad.jl")

# Close vectors
include("QuadForm/CloseVectors.jl")

# indefinite LLL
include("QuadForm/indefiniteLLL.jl")

# Functionality for IO with Hecke/Magma
include("QuadForm/IO.jl")
