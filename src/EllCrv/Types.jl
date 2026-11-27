################################################################################
#
#  Elliptic curves
#
################################################################################

@attributes mutable struct EllipticCurve{T}
  base_field::Ring
  short::Bool
  a_invariants::Tuple{T, T, T, T, T}
  b_invariants::Tuple{T, T, T, T}
  c_invariants::Tuple{T, T}
  disc::T
  j::T

  torsion_points#::Vector{EllipticCurvePoint}

  function EllipticCurve{T}(a::Tuple{T, T, T, T, T}) where {T}
    E = new{T}()
    E.base_field = parent(a[1])
    E.a_invariants = a
    E.short = iszero(a[1]) && iszero(a[2]) && iszero(a[3])
    return E
  end
end

mutable struct EllipticCurvePoint{T}
  coordx::T
  coordy::T
  is_infinite::Bool
  parent::EllipticCurve{T}

  function EllipticCurvePoint{T}(E::EllipticCurve{T}, x::T, y::T) where {T}
    return new{T}(x, y, false, E)
  end

  function EllipticCurvePoint{T}(E::EllipticCurve{T}) where {T}
    P = new{T}()
    P.parent = E
    P.is_infinite = true
    return P
  end
end

mutable struct EllCrvIso{T <: RingElem} <: Map{EllipticCurve, EllipticCurve, HeckeMap, EllCrvIso}
  header::MapHeader{EllipticCurve{T}, EllipticCurve{T}}
  domain::EllipticCurve{T}
  codomain::EllipticCurve{T}
  data::Tuple{T, T, T, T}

  function EllCrvIso(E::EllipticCurve{T}, F::EllipticCurve{T}, data::Tuple{T, T, T, T}) where {T}
    return new{T}(MapHeader(E, F), E, F, data)
  end
end

struct Isogeny{T <: RingElem} <: Map{EllipticCurve, EllipticCurve, HeckeMap, Isogeny}
  header::MapHeader{EllipticCurve{T}, EllipticCurve{T}}
  domain::EllipticCurve{T}
  codomain::EllipticCurve{T}
  coordx::RingElem  # x-coordinate map, in the fraction field of K[x]
  coordy::RingElem  # y-coordinate map, in the fraction field of K[x][y]
  psi::RingElem     # kernel polynomial, in K[x]
  degree::Int

  function Isogeny(E::EllipticCurve{T}, F::EllipticCurve{T}, coordx::RingElem,
                   coordy::RingElem, psi::RingElem, d::IntegerUnion) where {T}
    return new{T}(MapHeader(E, F), E, F, coordx, coordy, psi, d)
  end
end

################################################################################
#
#  Local Data
#
################################################################################

@doc raw"""
    KodairaSymbol

Represents the Kodaira symbol of a fiber of a Neron model of an elliptic
curve. The symbol encodes the reduction type at a prime.

The internal encoding uses a single integer (PARI/GP convention):
- `I0` = 1, `II` = 2, `III` = 3, `IV` = 4, `In` (n >= 1) = 4 + n
- `I0*` = -1, `II*` = -2, `III*` = -3, `IV*` = -4, `In*` (n >= 1) = -(4 + n)

Kodaira symbols can be constructed from strings:

```jldoctest
julia> KodairaSymbol("I5")
I5

julia> KodairaSymbol("IV*")
IV*
```
"""
struct KodairaSymbol
  ksymbol::Int

  function KodairaSymbol(n::Int)
    @req n != 0 "0 does not correspond to any Kodaira symbol."
    return new(n)
  end
end

@doc raw"""
    EllipticCurveReduction

Submodule holding the [`ReductionType`](@ref) enumeration used by
[`EllipticCurveLocalData`](@ref). Short names are scoped here to avoid
polluting the top-level namespace.
"""
module EllipticCurveReduction
  export ReductionType, good, split_multiplicative, nonsplit_multiplicative, additive

  @doc raw"""
    EllipticCurveReduction.ReductionType

Enumeration of the reduction types of an elliptic curve at a place of
its base field, as produced by Tate's algorithm.

The values are scoped in the `EllipticCurveReduction` submodule; reference
them with the module prefix:

- `EllipticCurveReduction.good`
- `EllipticCurveReduction.split_multiplicative`
- `EllipticCurveReduction.nonsplit_multiplicative`
- `EllipticCurveReduction.additive`

# Examples
```jldoctest
julia> E = elliptic_curve([1, 1, 0, 40050, 7557750]);

julia> ld = tates_algorithm_local(E, 5, EllipticCurveLocalData);

julia> ld.reduction_type == EllipticCurveReduction.additive
true
```
See also [`EllipticCurveLocalData`](@ref).
  """
  @enum ReductionType begin
    good
    split_multiplicative
    nonsplit_multiplicative
    additive
  end
end

@doc raw"""
    EllipticCurveLocalData

Local data of an elliptic curve at a prime, as computed by Tate's algorithm.

# Fields
- `minimal_model::EllipticCurve{T}`: local minimal model
- `isomorphism::EllCrvIso{T}`: isomorphism from the input curve to the (local) minimal model
- `kodaira_symbol::KodairaSymbol`: Kodaira symbol of the fiber
- `conductor_valuation::ZZRingElem`: conductor valuation
- `discriminant_valuation::ZZRingElem`: discriminant valuation
- `tamagawa_number::ZZRingElem`: local Tamagawa number
- `reduction_type::EllipticCurveReduction.ReductionType`: the type of reduction
"""
struct EllipticCurveLocalData{T}
  minimal_model::EllipticCurve{T}
  isomorphism::EllCrvIso{T}
  kodaira_symbol::KodairaSymbol
  conductor_valuation::ZZRingElem
  discriminant_valuation::ZZRingElem
  tamagawa_number::ZZRingElem
  reduction_type::EllipticCurveReduction.ReductionType
end
