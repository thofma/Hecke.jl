# Class Field Theory

```@meta
CurrentModule = Hecke
```

## Introduction

This chapter deals with abelian extensions of number fields and the rational numbers.

Class Field Theory, here specifically, class field theory of global number fields, deals
with abelian extension, ie. fields where the group of automorphisms is abelian.
For extensions of $\mathbb Q$, the famous Kronnecker-Weber theorem classifies all such fields:
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

```@docs; canonical=false
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

```@docs; canonical=false
ray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp})
ray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp}, quomap::Hecke.FinGenAbGroupHom)
ray_class_field(I::Hecke.AbsNumFieldOrderIdeal; n_quo, p_part)
ray_class_field(I::Hecke.AbsNumFieldOrderIdeal, ::Vector{InfPlc}; n_quo, p_part)
hilbert_class_field(k::AbsSimpleNumField)
ring_class_field(::AbsNumFieldOrder)
```

### Example

```@repl
using Hecke # hide
Qx, x = polynomial_ring(FlintQQ, "x");
K, a = number_field(x^2 - 10, "a");
c, mc = class_group(K)
A = ray_class_field(mc)
```

## Conversions

Given a ray class field, it is possible to actually compute defining equation(s) for this field.
In general, the number field constructed this way will be non-simple by type and is defined
by a polynomial for each maximal cyclic quotient of prime power order in the defining group.

The algorithm employed is based on Kummer-theory and requires the addition of a suitable
root of unity. Progress can be monitored by setting `set_verbose_level(:ClassField, n)`
where $0\le n\le 3$

```@docs; canonical=false
number_field(C::ClassField)
```

```@repl
using Hecke; # hide
Qx, x = polynomial_ring(FlintQQ, "x");
k, a = number_field(x^2 - 10, "a");
c, mc = class_group(k);
A = ray_class_field(mc)
K = number_field(A)
ZK = maximal_order(K)
isone(discriminant(ZK))
```

```@docs; canonical=false
ray_class_field(K::RelSimpleNumField{AbsSimpleNumFieldElem})
genus_field(A::ClassField, k::AbsSimpleNumField)
maximal_abelian_subfield(A::ClassField, k::AbsSimpleNumField)
maximal_abelian_subfield(K::RelSimpleNumField{AbsSimpleNumFieldElem})
```

## Invariants
```@docs; canonical=false
degree(C::ClassField)
base_ring(A::Hecke.ClassField)
base_field(A::Hecke.ClassField)
discriminant(C::Hecke.ClassField)
conductor(C::Hecke.ClassField)
defining_modulus(C::ClassField)
is_cyclic(C::ClassField)
is_conductor(C::Hecke.ClassField, m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, inf_plc::Vector{InfPlc})
is_normal(C::ClassField)
is_central(C::ClassField)
```

## Operations
```@docs; canonical=false
*(a::Hecke.ClassField, b::Hecke.ClassField)
compositum(a::Hecke.ClassField, b::Hecke.ClassField)
==(a::Hecke.ClassField, b::Hecke.ClassField)
intersect(a::Hecke.ClassField, b::Hecke.ClassField)
prime_decomposition_type(C::Hecke.ClassField, p::Hecke.AbsNumFieldOrderIdeal)
Hecke.is_subfield(a::ClassField, b::ClassField)
Hecke.is_local_norm(r::Hecke.ClassField, a::Hecke.AbsNumFieldOrderElem)
Hecke.is_local_norm(r::Hecke.ClassField, a::Hecke.AbsNumFieldOrderElem, p::Hecke.AbsNumFieldOrderIdeal)
Hecke.normal_closure(r::Hecke.ClassField)
subfields(r::ClassField)
```

