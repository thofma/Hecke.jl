################################################################################
#
#  Base field
#
################################################################################

@doc Markdown.doc"""
    base_field(L::NumField) -> NumField

> Given a number field $L/K$ this function returns the base field $K$.
> For absolute extensions this returns `QQ`.
"""
base_field(::NumField)

_base_ring(K::NumField) = base_field(K)

_base_ring(::FlintRationalField) = FlintQQ

################################################################################
#
#  Degree
#
################################################################################

#@doc Markdown.doc"""
#    degree(L::NumField) -> Int 
#
#> Given a number field $L/K$, this function returns the degree of $L$ over $K$.
#"""
#degree(A::NumField)

dim(K::NumField) = degree(K)

################################################################################
#
#  Absolute degree
#
################################################################################

@doc Markdown.doc"""
    absolute_degree(L::NumField) -> Int 

> Given a number field $L/K$, this function returns the degree of $L$ over
> $\mathbf Q$.
"""
function absolute_degree(A::NumField)
  return absolute_degree(base_field(A)) * degree(A)
end

################################################################################
#
#  Is simple extension
#
################################################################################

@doc Markdown.doc"""
    issimple(L::NumField) -> Bool

> Given a number field $L/K$ this function returns whether $L$ is absolute,
> that is, whether $K$ is equal to $\mathbf{QQ`.
"""
issimple(a::NumField)

################################################################################
#
#  Number field creation
#
################################################################################

@doc Markdown.doc"""
    NumberField(f::Poly{NumFieldElem}, s::String;
                cached::Bool = false, check::Bool = false) -> NumField, NumFieldElem

> Given an irreducible polynomial $f \in K[t]$ over some number field $K$, this
> function creates the simple number field $L = K[t]/(f)$ and returns $(L, b)$,
> where $b$ is the class of $t$ in $L$. The string `s` is used only for
> printing the primitive element $b$.
>
> Testing that $f$ is irreducible can be disabled by setting the ketword
> argument to `false`.
"""
NumberField(f::PolyElem{<:NumFieldElem}, s::String; cached::Bool = false, check::Bool = false) 

################################################################################
#
#  Is commutative
#
################################################################################

iscommutative(K::NumField) = true
