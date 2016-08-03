
@module{Hecke}


<a id='Creation-1'></a>

## Creation


@{call(::NfMaximalOrder, ::nf_elem, ::Bool)} @{call(::NfMaximalOrder, ::fmpz)} @{call(::NfMaximalOrder, ::Array{fmpz, 1})} @{call(::NfMaximalOrder, ::Array{Int, 1})} @{call(::NfMaximalOrder, ::nf_elem, ::Array{fmpz, 1})} @{call(::NfMaximalOrder)} @{zero(::NfMaximalOrder)} @{one(::NfMaximalOrder)}


<a id='Basic-invariants-1'></a>

## Basic invariants


@{parent(::NfOrderElem)} @{elem_in_nf(::NfOrderElem)} @{elem_in_basis(::NfOrderElem)} @{==(::NfOrderElem, ::NfOrderElem)} @{deepcopy(::NfOrderElem)} @{in(::nf_elem, ::NfMaximalOrder)} @{den(::nf_elem, ::NfMaximalOrder)}


<a id='Binary-and-unary-operations-1'></a>

## Binary and unary operations


@{-(::NfOrderElem)} @{*(::NfOrderElem, ::NfOrderElem)} @{+(::NfOrderElem, ::NfOrderElem)} @{-(::NfOrderElem, ::NfOrderElem)} @{*(::NfOrderElem, ::fmpz)} @{+(::NfOrderElem, ::fmpz)} @{-(::NfOrderElem, ::fmpz)} @{^(::NfOrderElem, ::Int)} @{mod(::NfOrderElem, ::Int)} @{powermod(::NfOrderElem, ::Int, ::fmpz)}


<a id='Representation-matrices-1'></a>

## Representation matrices


@{representation_mat(::NfOrderElem)} @{representation_mat(::NfOrderElem, ::AnticNumberField)}


<a id='Trace-and-norm-1'></a>

## Trace and norm


@{trace(::NfOrderElem)} @{norm(::NfOrderElem)}


<a id='Random-elements-1'></a>

## Random elements


@{rand(::NfMaximalOrder, ::UnitRange{Int})} @{rand(::NfMaximalOrder, ::Int)}


<a id='Conjugates-1'></a>

## Conjugates


@{conjugates_arb(::NfOrderElem, ::Int)} @{minkowski_map(::NfOrderElem, ::Int)} @{conjugates_log(::NfOrderElem)}

