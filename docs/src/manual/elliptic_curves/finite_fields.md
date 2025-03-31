```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Elliptic curves over finite fields


## Random points

```
  rand(E::EllipticCurve{<: FinFieldElem})
```

Return a random point on the elliptic curve $E$ defined over a finite field.

```jldoctest; filter = r"\(.*"
julia> E = elliptic_curve(GF(3), [1, 2]);

julia> rand(E)
(2 : 0 : 1)
```

## Cardinality and orders

```@docs
order(::EllipticCurve{<:FinFieldElem})
order(::EllipticCurvePoint{<:FinFieldElem})
```

## Frobenius

```@docs
trace_of_frobenius(::EllipticCurve{<:FinFieldElem})
trace_of_frobenius(::EllipticCurve{<:FinFieldElem}, ::Int)
```

## Group structure of rational points

```@docs
gens(::EllipticCurve{T}) where {T <: FinFieldElem}
abelian_group(::EllipticCurve{<:FinFieldElem})
```

## Discrete logarithm

```@docs
disc_log(::EllipticCurvePoint, ::EllipticCurvePoint)
```
