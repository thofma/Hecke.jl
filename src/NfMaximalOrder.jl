add_verbose_scope(:NfMaximalOrder)
add_assert_scope(:NfMaximalOrder)

set_verbose_level(:NfMaximalOrder, 1)

include("NfMaximalOrder/NfMaximalOrder.jl")
include("NfMaximalOrder/NfMaximalOrderIdeal.jl")
include("NfMaximalOrder/NfMaxOrdZeta.jl")
include("NfMaximalOrder/NfMaximalOrderFracIdeal.jl")
include("NfMaximalOrder/NfMaximalOrderClgp.jl")
include("NfMaximalOrder/GenNfOrdUnit.jl")
