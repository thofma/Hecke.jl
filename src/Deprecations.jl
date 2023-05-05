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

@deprecate orthogonal_sum(x::T, y::T) where T <: Union{AbstractSpace, ZZGenus, LocalZZGenus, HermGenus, HermLocalGenus, QuadGenus, QuadLocalGenus, JorDec, LocalQuadSpaceCls, QuadSpaceCls} direct_sum(x, y)

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
