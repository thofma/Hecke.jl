# Basics

```@meta
CurrentModule = Hecke
DocTestSetup = quote
    using Hecke
end

```

## Creation

```@docs
elliptic_curve
elliptic_curve_from_j_invariant
```

## Basic properties

```@docs
base_field(::EllipticCurve)
base_change(::Field, ::EllipticCurve)
base_change(::Any, ::EllipticCurve)
coefficients(::EllipticCurve)
a_invariants(::EllipticCurve)
b_invariants(::EllipticCurve)
c_invariants(::EllipticCurve)
discriminant(::EllipticCurve)
j_invariant(::EllipticCurve)
equation(::EllipticCurve)
hyperelliptic_polynomials(::EllipticCurve)
```

## Points

```julia
    (E::EllipticCurve)(coords::Vector; check::Bool = true)
```

Return the point $P$ of $E$ with coordinates specified by `coords`, which can
be either affine coordinates (`length(coords) == 2`) or projective coordinates
(`length(coords) == 3`).

Per default, it is checked whether the point lies on $E$. This can be disabled
by setting `check = false`.

##### Examples

```jldoctest
julia> E = elliptic_curve(QQ, [1, 2]);

julia> E([1, -2])
Point  (1 : -2 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2

julia> E([2, -4, 2])
Point  (1 : -2 : 1)  of Elliptic curve with equation
y^2 = x^3 + x + 2
```

```@docs
infinity(::EllipticCurve)
parent(::EllipticCurvePoint)
is_on_curve(::EllipticCurve, ::Vector)
+(P::EllipticCurvePoint{T}, Q::EllipticCurvePoint{T}) where {T}
division_points(::EllipticCurvePoint, ::Int)
```
