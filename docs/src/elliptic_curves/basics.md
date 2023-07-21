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
base_field(::EllCrv)
base_change(::Field, ::EllCrv)
base_change(::Any, ::EllCrv)
coefficients(::EllCrv)
a_invars(::EllCrv)
b_invars(::EllCrv)
c_invars(::EllCrv)
discriminant(::EllCrv)
j_invariant(::EllCrv)
equation(::EllCrv)
hyperelliptic_polynomials(::EllCrv)
```

## Points

```julia
    (E::EllCrv)(coords::Vector; check::Bool = true)
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
infinity(::EllCrv)
parent(::EllCrvPt)
is_on_curve(::EllCrv, ::Vector)
+(P::EllCrvPt{T}, Q::EllCrvPt{T}) where {T}
division_points(::EllCrvPt, ::Int)
```
