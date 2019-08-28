@module{Hecke}
# Orders

## Creation

@{MaximalOrder(::AnticNumberField)}
@{MaximalOrder(::AnticNumberField, ::Array{fmpz, 1})}

## Basic invariants

@{nf(::NfMaximalOrder)}
@{degree(::NfMaximalOrder)}
@{basis(::NfMaximalOrder)}
@{basis(::NfMaximalOrder, ::AnticNumberField)}
@{basis_matrix(::NfMaximalOrder)}
@{basis_mat_inv(::NfMaximalOrder)}
@{index(::NfMaximalOrder)}
@{signature(::NfMaximalOrder)}
@{isindex_divisor(::NfMaximalOrder, ::fmpz)}
@{minkowski_mat(::NfMaximalOrder, ::Int)}

