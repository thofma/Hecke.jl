```@meta
CurrentModule = Hecke
CollapsedDocStrings = true
DocTestSetup = Hecke.doctestsetup()
```
# Class Field Theory

## Introduction

This chapter deals with abelian extensions of number fields and the rational numbers.

Class Field Theory, here specifically, class field theory of global number fields, deals
with abelian extension, ie. fields where the group of automorphisms is abelian.
For extensions of $\mathbb Q$, the famous Kronecker-Weber theorem classifies all such fields:
a field is abelian if and only if it is contained in some cyclotomic field. For general
number fields this is more involved and even for extensions of $\mathbb Q$ is is not practical.

In Hecke, abelian extensions are parametrized by quotients of so called ray class groups.
The language of ray class groups while dated is more applicable to algorithms than the
modern language of idel class groups and quotients.

## Ray Class Groups

Given an integral ideal $m_0 \le Z_K$ and a list of real places $m_\infty$, the
ray class group modulo $(m_0, m_\infty)$, $C(m)$ is defined as the group
of ideals coprime to $m_0$ modulo the elements $a\in K^*$ s.th.
$v_p(a-1) \ge v_p(m_0)$ and for all $v\in m_\infty$, $a^{(v)} >0$.
This is a finite abelian group. For $m_0 = Z_K$ and $m_\infty = \{\}$ we
get $C()$ is the class group, if $m_\infty$ contains all real places, we obtain
the narrow class group, or strict class group.

```@docs
ray_class_group(m::Hecke.AbsNumFieldOrderIdeal{Nemo.AbsSimpleNumField,Nemo.AbsSimpleNumFieldElem}, inf_plc::Vector{Hecke.InfPlc}; p_part, n_quo)
class_group(K::Nemo.AbsSimpleNumField)
norm_group(f::Nemo.PolyRingElem, mR::Hecke.MapRayClassGrp, is_abelian::Bool)
norm_group(K::RelSimpleNumField{AbsSimpleNumFieldElem}, mR::Hecke.MapRayClassGrp, is_abelian::Bool)
```


## Ray Class Fields

In general, the construction of a class field starts with a (ray) class group. Each quotient
of a ray class group then defines a ray class field, the defining property is that the
(relative) automorphism group is canonically isomorphic to the quotient of the ray class group
where the isomorphism is given by the Artin (or Frobenius) map. Since, in Hecke, the
(ray) class groups have no link to the field, actually this has to be specified using the
maps.

It should be noted that this is a _lazy_ construction: nothing is computed at this point.

```@docs
ray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp})
ray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp}, quomap::Hecke.FinGenAbGroupHom)
ray_class_field(I::Hecke.AbsNumFieldOrderIdeal; n_quo, p_part)
ray_class_field(I::Hecke.AbsNumFieldOrderIdeal, ::Vector{InfPlc}; n_quo, p_part)
hilbert_class_field(k::AbsSimpleNumField)
ring_class_field(::AbsNumFieldOrder)
cyclotomic_field(::Type{ClassField}, n::Int)
```

### Example

```jldoctest
julia> Qx, x = polynomial_ring(QQ, :x);

julia> K, a = number_field(x^2 - 10, :a);

julia> c, mc = class_group(K)
(Z/2, Class group map of set of ideals of O_K)

julia> A = ray_class_field(mc)
Class field
  over number field with defining polynomial x^2 - 10
    over rational field
with modulus
  finite part <1>
  infinite part
    []
with structure
  Z/2
```

## Conversions

Given a ray class field, it is possible to actually compute defining equation(s) for this field.
In general, the number field constructed this way will be non-simple by type and is defined
by a polynomial for each maximal cyclic quotient of prime power order in the defining group.

The algorithm employed is based on Kummer-theory and requires the addition of a suitable
root of unity. Progress can be monitored by setting `set_verbose_level(:ClassField, n)`
where $0\le n\le 3$

```@docs
number_field(C::ClassField)
number_field(::Type{SimpleNumField}, C::ClassField)
number_field(::Type{AbsSimpleNumField}, C::ClassField)
```

```jldoctest
julia> Qx, x = polynomial_ring(QQ, :x);

julia> k, a = number_field(x^2 - 10, :a);

julia> c, mc = class_group(k);

julia> A = ray_class_field(mc)
Class field
  over number field with defining polynomial x^2 - 10
    over rational field
with modulus
  finite part <1>
  infinite part
    []
with structure
  Z/2

julia> K = number_field(A)
Relative non-simple number field with defining polynomials [x^2 - 2]
  over number field with defining polynomial x^2 - 10
    over rational field

julia> ZK = maximal_order(K)
Maximal order
  of relative non-simple number field with defining polynomials [x^2 - 2]
    over number field of degree 2 over QQ
with pseudo-basis
  (1, <1, 1>//1)
  (_$1 + a, <2, a>//4)

julia> isone(discriminant(ZK))
true
```

```@docs
ray_class_field(K::RelSimpleNumField{AbsSimpleNumFieldElem})
genus_field(A::ClassField, k::AbsSimpleNumField)
maximal_abelian_subfield(A::ClassField, k::AbsSimpleNumField)
maximal_abelian_subfield(K::RelSimpleNumField{AbsSimpleNumFieldElem})
decomposition_field(C::ClassField, p::AbsSimpleNumFieldOrderIdeal)
inertia_field(C::ClassField, p::AbsSimpleNumFieldOrderIdeal)
fixed_field(A::ClassField, U::FinGenAbGroup)
grunwald_wang(dp::Dict{<:NumFieldOrderIdeal, Int64}, di::Dict{<:Hecke.NumFieldEmb, Int64})
cyclotomic_extension(::ClassField, ::Int)
cyclotomic_extension(::Type{ClassField}, k::AbsSimpleNumField, n::Int)
```

## Invariants
```@docs
degree(C::ClassField)
exponent(C::ClassField)
base_ring(A::Hecke.ClassField)
base_field(A::Hecke.ClassField)
discriminant(C::Hecke.ClassField)
conductor(C::Hecke.ClassField)
signature(C::Hecke.ClassField)
defining_modulus(C::ClassField)
is_cyclic(C::ClassField)
is_conductor(C::Hecke.ClassField, m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, inf_plc::Vector{InfPlc})
is_normal(C::ClassField)
is_central(C::ClassField)
automorphism_group(C::ClassField)
absolute_automorphism_group(C::ClassField)
decomposition_group(C::ClassField, p::InfPlc)
frobenius_map(C::ClassField)
complex_conjugation(C::ClassField, p::InfPlc)
```

## Operations
```@docs
*(a::Hecke.ClassField, b::Hecke.ClassField)
compositum(a::Hecke.ClassField, b::Hecke.ClassField)
==(a::Hecke.ClassField, b::Hecke.ClassField)
intersect(a::Hecke.ClassField, b::Hecke.ClassField)
prime_decomposition_type(C::Hecke.ClassField, p::Hecke.AbsNumFieldOrderIdeal)
Hecke.is_subfield(a::ClassField, b::ClassField)
Hecke.is_local_norm(r::Hecke.ClassField, a::Hecke.AbsNumFieldOrderElem)
Hecke.is_local_norm(r::Hecke.ClassField, a::Hecke.AbsNumFieldOrderElem, p::Hecke.AbsNumFieldOrderIdeal)
normal_closure(r::Hecke.ClassField)
subfields(r::ClassField)
```

