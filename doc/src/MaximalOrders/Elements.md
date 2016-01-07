@module{Hecke}

## Creation

@{call(::NfMaximalOrder, ::nf_elem, ::Bool)}
@{call(::NfMaximalOrder, ::fmpz)}
@{call(::NfMaximalOrder, ::Array{fmpz, 1})}
@{call(::NfMaximalOrder, ::Array{Int, 1})}
@{call(::NfMaximalOrder, ::nf_elem, ::Array{fmpz, 1})}
@{call(::NfMaximalOrder)}
@{zero(::NfMaximalOrder)}
@{one(::NfMaximalOrder)}

## Basic invariants

@{parent(::NfOrderElem)}
@{elem_in_nf(::NfOrderElem)}
@{elem_in_basis(::NfOrderElem)}
@{==(::NfOrderElem, ::NfOrderElem)}
@{deepcopy(::NfOrderElem)}
@{in(::nf_elem, ::NfMaximalOrder)}
@{den(::nf_elem, ::NfMaximalOrder)}

## Binary and unary operations

@{-(::NfOrderElem)}
@{*(::NfOrderElem, ::NfOrderElem)}
@{+(::NfOrderElem, ::NfOrderElem)}
@{-(::NfOrderElem, ::NfOrderElem)}
@{*(::NfOrderElem, ::fmpz)}
@{+(::NfOrderElem, ::fmpz)}
@{-(::NfOrderElem, ::fmpz)}
@{^(::NfOrderElem, ::Int)}
@{mod(::NfOrderElem, ::Int)}
@{powermod(::NfOrderElem, ::Int, ::fmpz)}

## Representation matrices

@{representation_mat(::NfOrderElem)}
@{representation_mat(::NfOrderElem, ::AnticNumberField)}

## Trace and norm

@{trace(::NfOrderElem)}
@{norm(::NfOrderElem)}

## Random elements

@{rand(::NfMaximalOrder, ::UnitRange{Int})}
@{rand(::NfMaximalOrder, ::Int)}

## Conjugates

@{conjugates_arb(::NfOrderElem, ::Int)}
@{minkowski_map(::NfOrderElem, ::Int)}
@{conjugates_log(::NfOrderElem)}
