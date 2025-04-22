# Todo list for rainy days

## General
 * [ ] Provide (prototype) documentation in the following formats: REPL using @doc, html, as well as pdf
 * [ ] Copyright information (BSD 2-clause) in each file
 * [ ] Build a (user)sysimage to speed up starting time

## Orders in number fields

 * [ ] implement Montes--Nart algorithm
 * [ ] composite Dedekind criterion
 * [ ] composite Round Two algorithm
 * [ ] implement information about containment (O_1 \sub O_2)
 * [ ] save prime factors of discriminant
 * [x] `princ_gen` should be cached
 * [ ] Clean up uniformizer (p-uniformizer? strong uniformizer?)
 * [x] Residue fields of degree one
 * [ ] Parent checks for `(::Order)(::NumFieldElem)`.
 * [ ] Coercion of AbsSimpleNumFieldElem in AbsSimpleNumFieldOrder

## Number fields
 * [ ] Overhaul the morphisms
 * [ ] Test functionality for non-monic defining polynomials
 * [x] Torsion unit functionality for number fields
 * [ ] Better algorithm for normal closure
 * [ ] weak and strong approximation
 * [ ] `absolute_field` is inconsistent and needs keyword for `simplify`
 * [ ] Remove the type `nf_elem_or_fac_elem`
 * [ ] Clean up the clever `princ_gen_special` code
 * [ ] Implement Arakelov and/or divisor type
 * [ ] Finite places
 * [ ] Need `is_maximal_order_known` and `isautomorphism_group_known`
 * [x] `relative_extension`
 * [ ] `is_locally_power` (at given primes or up to given bound)
 * [x] Frobenius automorphism of a field at a prime ideal
 * [ ] Redo the `automorphism_group` properly.
 * [ ] `coeff(z, i)` and `coefficients(z)` "inconsistencies"

 ## Renaming

 * [x] `DiagonalGroup` and `AbelianGroup` to `abelian_group`.
 * [x] `princ_gen` to `principal_generator`
 * [ ] `nf` to `number_field`
 * [x] Group algebra renaming
 * [ ] Make `has*` and `*_known` consistent.

 ## Misc
 * [ ] `exp_map_unit_grp_mod`
 * [ ] `charpoly` should have `parent = ` keyword.
 * [ ] Squarefree factorization over number fields (?)
 * [ ] Make FF robust for the use of `ZZRingElem`.
 * [ ] `next_prime(::ZZRingElem, ::Bool)`
 * [x] `round(::Type{QQFieldElem}, ::ZZRingElem)` is doing funky things. Also needs the `RoundUp/RoundDown` versions.
 * [x] Parent checks for factored elements
 * [ ] Primitive element for all finite fields
