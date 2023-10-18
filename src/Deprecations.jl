# Deprecated during 0.7.*

@deprecate principal_gen principal_generator

@deprecate principal_gen_fac_elem principal_generator_fac_elem

@deprecate right_principal_gen right_principal_generator

@deprecate left_principal_gen left_principal_generator

@deprecate principal_gen_eichler principal_generator_eichler

# Deprecated during 0.10.*

@deprecate subgroup sub

@deprecate upper_bound(x::arb, y::Type{ZZRingElem}) upper_bound(y, x)

@deprecate abs_upper_bound(x::arb, y::Type{ZZRingElem}) abs_upper_bound(y, x)

@deprecate is_equivalent is_isometric

@deprecate is_equivalent_with_isometry is_isometric_with_isometry

# Deprecated during 0.15.*

@deprecate automorphisms(x::NumField, y::NumField) automorphism_list(x, y)

@deprecate automorphisms(x::NumField) automorphism_list(x)

@deprecate automorphisms(x::Union{FlintPadicField, FlintQadicField, LocalField}) automorphism_list(x)

@deprecate automorphisms(x::LocalField, y::Union{FlintPadicField, FlintQadicField, LocalField}) automorphism_list(x, y)

# Deprecated during 0.18.*

@deprecate orthogonal_sum(x::T, y::T) where T <: Union{AbstractSpace, ZZGenus, ZZLocalGenus, HermGenus, HermLocalGenus, QuadGenus, QuadLocalGenus, JorDec, LocalQuadSpaceCls, QuadSpaceCls} direct_sum(x, y)

@deprecate ideal(A::AbsAlgAss{S}, M::PMat{S, T}, M_in_hnf::Bool) where { S <: NumFieldElem, T } ideal(A, M; M_in_hnf)

@deprecate ideal(A::AbsAlgAss{QQFieldElem}, O::AlgAssAbsOrd, M::FakeFmpqMat, side::Symbol, M_in_hnf::Bool = false) ideal(A, O, M; side, M_in_hnf)

@deprecate ideal(A::AbsAlgAss, M::MatElem, side::Symbol, M_in_rref::Bool = false) ideal(A, M; side, M_in_rref)

@deprecate ideal(A::AbsAlgAss{S}, O::AlgAssRelOrd{S, T, U}, M::PMat{S, T}, side::Symbol, M_in_hnf::Bool = false) where { S <: NumFieldElem, T, U } ideal(A, O, M; side, M_in_hnf)

@deprecate ideal(A::AbsAlgAss{QQFieldElem}, M::FakeFmpqMat, M_in_hnf::Bool) ideal(A, M; M_in_hnf)

@deprecate ideal(O::NfRelOrd{T, S, U}, M::PMat{T, S}, check::Bool, M_in_hnf::Bool = false) where {T, S, U} ideal(O, M; check, M_in_hnf)

@deprecate ideal(O::NfRelOrd{T, S}, x::NumFieldElem{T}, y::NumFieldElem{T}, a::NfOrdIdl, b::NfOrdIdl, check::Bool) where {T, S} ideal(O, x, y, a, b; check)

@deprecate ideal(O::NfRelOrd{T, S}, x::NumFieldElem{T}, y::NumFieldElem{T}, a::NfRelOrdIdl, b::NfRelOrdIdl, check::Bool) where {T, S} ideal(O, x, y, a, b; check)

@deprecate ideal(O::NfRelOrd{T, S}, M::Generic.Mat{T}, check::Bool) where {T, S} ideal(O, M; check)

@deprecate ideal(O::NfRelOrd{nf_elem, NfOrdFracIdl}, a::NfOrdIdl, check::Bool) ideal(O, a; check)

@deprecate ideal(O::NfRelOrd, a::NfRelOrdIdl, check::Bool) ideal(O, a; check)

@deprecate ideal(O::NfRelOrd{T, S, U}, a::S, check::Bool) where {T, S, U} ideal(O, a; check)

@deprecate ideal(O::NfRelOrd{T, S, U}, x::U, y::U, a::S, b::S, check::Bool) where {T, S, U} ideal(O, x, y, a, b; check)

@deprecate ideal(O::NfAbsOrd, M::ZZMatrix, check::Bool, M_in_hnf::Bool = false) ideal(O, M; check, M_in_hnf)

@deprecate fractional_ideal(O::NfAbsOrd, M::FakeFmpqMat, M_in_hnf::Bool) fractional_ideal(O, M; M_in_hnf)

@deprecate fractional_ideal(O::NfAbsOrd, M::ZZMatrix, b::ZZRingElem, M_in_hnf::Bool) fractional_ideal(O, M, b; M_in_hnf)

@deprecate fractional_ideal(O::NfRelOrd{T, S, U}, M::PMat{T, S}, M_in_hnf::Bool) where {T, S, U} fractional_ideal(O, M; M_in_hnf)

@deprecate PseudoMatrix pseudo_matrix

@deprecate factor(a::QQFieldElem, Z::ZZRing) factor(Z, a)

@deprecate factor(f::QQPolyRingElem, K::AnticNumberField) factor(K, f)

@deprecate factor(f::ZZPolyRingElem, K::AnticNumberField) factor(K, f)

@deprecate factor(a::nf_elem, I::NfOrdIdlSet) factor(I, a)

@deprecate factor(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet) factor(I, a)

@deprecate factor(a::Generic.RationalFunctionFieldElem{T}, R::S) where {T, S<:PolyRing{T}} factor(R, a)

@deprecate factor(a::Generic.RationalFunctionFieldElem, R::HessQR) factor(R, a)

@deprecate factor(f::Generic.Poly{<:Generic.RationalFunctionFieldElem{T}}, F::Generic.FunctionField{T}) where {T} factor(F, f)

@deprecate factor(f::Union{QQMPolyRingElem, ZZMPolyRingElem}, R::ArbField) factor(R, f)

@deprecate factor(f::Union{QQMPolyRingElem, ZZMPolyRingElem}, C::AcbField) factor(C, f)

@deprecate factor(f::Union{ZZPolyRingElem, QQPolyRingElem}, R::ArbField, abs_tol::Int=R.prec, initial_prec::Int...) factor(R, f, abs_tol, initial_prec...)

@deprecate factor(f::Union{ZZPolyRingElem, QQPolyRingElem}, R::AcbField, abs_tol::Int=R.prec, initial_prec::Int...) factor(R, f, abs_tol, initial_prec...)

@deprecate factor_coprime(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet; refine::Bool = false) factor_coprime(I, a, refine = refine)

@deprecate roots(f::QQPolyRingElem, K::AnticNumberField; kw...) roots(K, f; kw...)
@deprecate roots(f::ZZPolyRingElem, K::AnticNumberField; kw...) roots(K, f; kw...)

@deprecate roots(f::Union{fpPolyRingElem, fqPolyRepPolyRingElem}, F::Union{fqPolyRepField, Hecke.RelFinField}) roots(F, f)

@deprecate roots(f::Union{ZZPolyRingElem, QQPolyRingElem}, R::ArbField, abs_tol::Int=R.prec, initial_prec::Int...) roots(R, f, abs_tol, initial_prec...)

@deprecate roots(f::Union{ZZPolyRingElem, QQPolyRingElem}, R::AcbField, abs_tol::Int=R.prec, initial_prec::Int...) roots(R, f, abs_tol, initial_prec...)

@deprecate roots(f::ZZPolyRingElem, Q::FlintQadicField; max_roots::Int = degree(f)) roots(Q, f; max_roots = max_roots)

@deprecate roots(f::ZZPolyRingElem, Q::QQField; max_roots::Int = degree(f)) roots(Q, f; max_roots = max_roots)

@deprecate any_root(f::Union{fpPolyRingElem, fqPolyRepPolyRingElem}, F::Union{fqPolyRepField, Hecke.RelFinField}) any_root(F, f)

@deprecate any_root(f::Hecke.AbstractAlgebra.Generic.Poly, F::Hecke.RelFinField) any_root(F, f)

# Deprecated during 0.22.*

@deprecate mul(A::SMat{T}, b::AbstractVector{T}) where T A*b

@deprecate mul(A::SMat{T}, b::AbstractMatrix{T}) where T A*b

@deprecate mul(A::SMat{T}, b::MatElem{T}) where T A*b

@deprecate mul(A::SRow{T}, B::SMat{T}) where T A*B

@deprecate field_of_fractions(O::GenOrd) function_field(O::GenOrd)

# Things that moved to Nemo

# > 0.18.1
if isdefined(Nemo, :simplest_between)
  simplest_inside(x::arb) = simplest_rational_inside(x)
else
  function _fmpq_simplest_between(l_num::ZZRingElem, l_den::ZZRingElem,
                                  r_num::ZZRingElem, r_den::ZZRingElem)
     n = ZZRingElem()
     d = ZZRingElem()

     ccall((:_fmpq_simplest_between, libflint), Nothing,
           (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}),
           n, d, l_num, l_den, r_num, r_den)

     return n//d
  end

  @doc raw"""
        simplest_between(l::QQFieldElem, r::QQFieldElem)

  > Return the simplest fraction in the closed interval `[l, r]`. A canonical >
  > fraction `a_1/b_1` is defined to be simpler than `a_2/b_2` iff `b_1 < b_2` or
  > `b_1 = b_2` and `a_1 < a_2`.
  """
  function simplest_between(l::QQFieldElem, r::QQFieldElem)
     z = QQFieldElem()
     ccall((:fmpq_simplest_between, libflint), Nothing,
           (Ref{QQFieldElem}, Ref{QQFieldElem}, Ref{QQFieldElem}), z, l, r)
     return z
  end

  function simplest_inside(x::arb)
    a = ZZRingElem()
    b = ZZRingElem()
    e = ZZRingElem()

    ccall((:arb_get_interval_fmpz_2exp, libarb), Nothing, (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{arb}), a, b, e, x)
    @assert fits(Int, e)
    _e = Int(e)
    if e >= 0
      return a << _e
    end
    _e = -_e
    d = one(ZZRingElem) << _e
    return _fmpq_simplest_between(a, d, b, d)
  end
end
