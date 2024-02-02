# Deprecated during 0.7.*

@deprecate principal_gen principal_generator

@deprecate principal_gen_fac_elem principal_generator_fac_elem

@deprecate right_principal_gen right_principal_generator

@deprecate left_principal_gen left_principal_generator

@deprecate principal_gen_eichler principal_generator_eichler

# Deprecated during 0.10.*

@deprecate subgroup sub

@deprecate upper_bound(x::ArbFieldElem, y::Type{ZZRingElem}) upper_bound(y, x)

@deprecate abs_upper_bound(x::ArbFieldElem, y::Type{ZZRingElem}) abs_upper_bound(y, x)

@deprecate is_equivalent is_isometric

@deprecate is_equivalent_with_isometry is_isometric_with_isometry

# Deprecated during 0.15.*

@deprecate automorphisms(x::NumField, y::NumField) automorphism_list(x, y)

@deprecate automorphisms(x::NumField) automorphism_list(x)

@deprecate automorphisms(x::Union{PadicField, QadicField, LocalField}) automorphism_list(x)

@deprecate automorphisms(x::LocalField, y::Union{PadicField, QadicField, LocalField}) automorphism_list(x, y)

# Deprecated during 0.18.*

@deprecate orthogonal_sum(x::T, y::T) where T <: Union{AbstractSpace, ZZGenus, ZZLocalGenus, HermGenus, HermLocalGenus, QuadGenus, QuadLocalGenus, JorDec, LocalQuadSpaceCls, QuadSpaceCls} direct_sum(x, y)

@deprecate ideal(A::AbstractAssociativeAlgebra{S}, M::PMat{S, T}, M_in_hnf::Bool) where { S <: NumFieldElem, T } ideal(A, M; M_in_hnf)

@deprecate ideal(A::AbstractAssociativeAlgebra{QQFieldElem}, O::AlgAssAbsOrd, M::FakeFmpqMat, side::Symbol, M_in_hnf::Bool = false) ideal(A, O, M; side, M_in_hnf)

@deprecate ideal(A::AbstractAssociativeAlgebra, M::MatElem, side::Symbol, M_in_rref::Bool = false) ideal(A, M; side, M_in_rref)

@deprecate ideal(A::AbstractAssociativeAlgebra{S}, O::AlgAssRelOrd{S, T, U}, M::PMat{S, T}, side::Symbol, M_in_hnf::Bool = false) where { S <: NumFieldElem, T, U } ideal(A, O, M; side, M_in_hnf)

@deprecate ideal(A::AbstractAssociativeAlgebra{QQFieldElem}, M::FakeFmpqMat, M_in_hnf::Bool) ideal(A, M; M_in_hnf)

@deprecate ideal(O::RelNumFieldOrder{T, S, U}, M::PMat{T, S}, check::Bool, M_in_hnf::Bool = false) where {T, S, U} ideal(O, M; check, M_in_hnf)

@deprecate ideal(O::RelNumFieldOrder{T, S}, x::NumFieldElem{T}, y::NumFieldElem{T}, a::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, b::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, check::Bool) where {T, S} ideal(O, x, y, a, b; check)

@deprecate ideal(O::RelNumFieldOrder{T, S}, x::NumFieldElem{T}, y::NumFieldElem{T}, a::RelNumFieldOrderIdeal, b::RelNumFieldOrderIdeal, check::Bool) where {T, S} ideal(O, x, y, a, b; check)

@deprecate ideal(O::RelNumFieldOrder{T, S}, M::Generic.Mat{T}, check::Bool) where {T, S} ideal(O, M; check)

@deprecate ideal(O::RelNumFieldOrder{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}, a::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, check::Bool) ideal(O, a; check)

@deprecate ideal(O::RelNumFieldOrder, a::RelNumFieldOrderIdeal, check::Bool) ideal(O, a; check)

@deprecate ideal(O::RelNumFieldOrder{T, S, U}, a::S, check::Bool) where {T, S, U} ideal(O, a; check)

@deprecate ideal(O::RelNumFieldOrder{T, S, U}, x::U, y::U, a::S, b::S, check::Bool) where {T, S, U} ideal(O, x, y, a, b; check)

@deprecate ideal(O::AbsNumFieldOrder, M::ZZMatrix, check::Bool, M_in_hnf::Bool = false) ideal(O, M; check, M_in_hnf)

@deprecate fractional_ideal(O::AbsNumFieldOrder, M::FakeFmpqMat, M_in_hnf::Bool) fractional_ideal(O, M; M_in_hnf)

@deprecate fractional_ideal(O::AbsNumFieldOrder, M::ZZMatrix, b::ZZRingElem, M_in_hnf::Bool) fractional_ideal(O, M, b; M_in_hnf)

@deprecate fractional_ideal(O::RelNumFieldOrder{T, S, U}, M::PMat{T, S}, M_in_hnf::Bool) where {T, S, U} fractional_ideal(O, M; M_in_hnf)

@deprecate PseudoMatrix pseudo_matrix

@deprecate factor(a::QQFieldElem, Z::ZZRing) factor(Z, a)

@deprecate factor(f::QQPolyRingElem, K::AbsSimpleNumField) factor(K, f)

@deprecate factor(f::ZZPolyRingElem, K::AbsSimpleNumField) factor(K, f)

@deprecate factor(a::AbsSimpleNumFieldElem, I::AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}) factor(I, a)

@deprecate factor(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, I::AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}) factor(I, a)

@deprecate factor(a::Generic.RationalFunctionFieldElem{T}, R::S) where {T, S<:PolyRing{T}} factor(R, a)

@deprecate factor(a::Generic.RationalFunctionFieldElem, R::HessQR) factor(R, a)

@deprecate factor(f::Generic.Poly{<:Generic.RationalFunctionFieldElem{T}}, F::Generic.FunctionField{T}) where {T} factor(F, f)

@deprecate factor(f::Union{QQMPolyRingElem, ZZMPolyRingElem}, R::ArbField) factor(R, f)

@deprecate factor(f::Union{QQMPolyRingElem, ZZMPolyRingElem}, C::AcbField) factor(C, f)

@deprecate factor(f::Union{ZZPolyRingElem, QQPolyRingElem}, R::ArbField, abs_tol::Int=R.prec, initial_prec::Int...) factor(R, f, abs_tol, initial_prec...)

@deprecate factor(f::Union{ZZPolyRingElem, QQPolyRingElem}, R::AcbField, abs_tol::Int=R.prec, initial_prec::Int...) factor(R, f, abs_tol, initial_prec...)

@deprecate factor_coprime(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}, I::AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}; refine::Bool = false) factor_coprime(I, a, refine = refine)

@deprecate roots(f::QQPolyRingElem, K::AbsSimpleNumField; kw...) roots(K, f; kw...)
@deprecate roots(f::ZZPolyRingElem, K::AbsSimpleNumField; kw...) roots(K, f; kw...)

@deprecate roots(f::Union{fpPolyRingElem, fqPolyRepPolyRingElem}, F::Union{fqPolyRepField, Hecke.RelFinField}) roots(F, f)

@deprecate roots(f::Union{ZZPolyRingElem, QQPolyRingElem}, R::ArbField, abs_tol::Int=R.prec, initial_prec::Int...) roots(R, f, abs_tol, initial_prec...)

@deprecate roots(f::Union{ZZPolyRingElem, QQPolyRingElem}, R::AcbField, abs_tol::Int=R.prec, initial_prec::Int...) roots(R, f, abs_tol, initial_prec...)

@deprecate roots(f::ZZPolyRingElem, Q::QadicField; max_roots::Int = degree(f)) roots(Q, f; max_roots = max_roots)

@deprecate roots(f::ZZPolyRingElem, Q::QQField; max_roots::Int = degree(f)) roots(Q, f; max_roots = max_roots)

@deprecate any_root(f::Union{fpPolyRingElem, fqPolyRepPolyRingElem}, F::Union{fqPolyRepField, Hecke.RelFinField}) any_root(F, f)

@deprecate any_root(f::Hecke.AbstractAlgebra.Generic.Poly, F::Hecke.RelFinField) any_root(F, f)

# Deprecated during 0.22.*

@deprecate mul(A::SMat{T}, b::AbstractVector{T}) where T A*b

@deprecate mul(A::SMat{T}, b::AbstractMatrix{T}) where T A*b

@deprecate mul(A::SMat{T}, b::MatElem{T}) where T A*b

@deprecate mul(A::SRow{T}, B::SMat{T}) where T A*B

@deprecate field_of_fractions(O::GenOrd) function_field(O::GenOrd)

# Deprecated during 0.23.*

@deprecate divexact_right(a::T, b::T, check::Bool) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } } divexact(a, b, :right, check)
@deprecate divexact_left(a::T, b::T, check::Bool) where { T <: Union{ AlgAssAbsOrdElem, AlgAssRelOrdElem } } divexact(a, b, :left, check)
@deprecate divexact(a::NumFieldOrderElem, b::Integer, check::Bool) divexact(a, b; check=check)
@deprecate divexact(a::NumFieldOrderElem, b::ZZRingElem, check::Bool) divexact(a, b; check=check)
@deprecate divexact(x::T, y::T, check::Bool) where T <: NumFieldOrderElem divexact(x, y; check=check)

# Deprecated during 0.24.*

@deprecate hasimage has_image_with_image

@deprecate has_image has_image_with_image

@deprecate haspreimage has_preimage_with_preimage

@deprecate has_preimage has_preimage_with_preimage

@deprecate TorQuadModuleMor TorQuadModuleMap

# Things that moved to Nemo

# > 0.18.1
simplest_inside(x::ArbFieldElem) = simplest_rational_inside(x)

# Deprecated during 0.18.*

@deprecate abelian_fields abelian_extensions

# Deprecated during 0.24.*

@deprecate psylow_subgroup sylow_subgroup
