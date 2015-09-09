add_verbose_scope(:NfMaximalOrder)
add_assert_scope(:NfMaximalOrder)

set_verbose_level(:NfMaximalOrder, 1)

include("NfMaximalOrder/NfMaximalOrder.jl")
include("NfMaximalOrder/Ideal.jl")
include("NfMaximalOrder/Zeta.jl")
include("NfMaximalOrder/FracIdeal.jl")
include("NfMaximalOrder/Clgp.jl")
include("NfMaximalOrder/GenNfOrdUnit.jl")
include("NfMaximalOrder/ResidueField.jl")
