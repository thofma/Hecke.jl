add_verbosity_scope(:AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})
add_assertion_scope(:AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem})

#set_verbosity_level(:AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}, 1)

include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/NfMaxOrd.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Ideal.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Zeta.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/FracIdl.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Clgp.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Unit.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/ResidueField.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/ResidueRing.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/ResidueRingMultGrp.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/FactorBaseBound.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/FacElem.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/LinearAlgebra.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/IdealLLL.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/Narrow.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/norm_eqn.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/RayClass.jl")
include("AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}/RayClassFacElem.jl")
