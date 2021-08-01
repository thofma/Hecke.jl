# Class Field Theory

```@meta
CurrentModule = Hecke
```

## Introduction

This chapter deals with abelian extensions of number fields and the rational numbers.

Class Field Theory, here specifically, class field theory of global number fields, deals
with abelian extension, ie. fields where the group of automorphisms is abelian.
For extensions of {\Q}, the famous Kronnecker-Weber theorem classifies all such fields:
a field is abelian if and only if it is contained in some cyclotomic field. For general
number fields this is more involved and even for extensions of {\Q} is is not practical.

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
ray_class_group(m::Hecke.NfAbsOrdIdl{Nemo.AnticNumberField,Nemo.nf_elem}, inf_plc::Vector{Hecke.InfPlc}; p_part, n_quo)
class_group(K::Nemo.AnticNumberField)
norm_group(f::Nemo.PolyElem, mR::Hecke.MapRayClassGrp, isabelian::Bool)
norm_group(K::NfRel{nf_elem}, mR::Hecke.MapRayClassGrp, isabelian::Bool)
```


## Ray Class Fields

In general, the construction of a class field starts with a (ray) class group. Each quotient
of a ray class group then defines a ray class field, the defining property is that the
(relative) automorphism group is canonically isomorphic to the quotient of the ray class group
where the isomorphism is given by the Artin (or Frobenius) map. Since, in Hecke, the
(ray) class groups have no link to the field, actually this has to be specified using the
maps.

It should be noted that this is a {\em lazy} construction: nothing is computed at this point.

```@docs
ray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp})
ray_class_field(m::Union{Hecke.MapClassGrp, Hecke.MapRayClassGrp}, quomap::Hecke.GrpAbFinGenMap)
ray_class_field(I::Hecke.NfAbsOrdIdl; n_quo, p_part)
ray_class_field(I::Hecke.NfAbsOrdIdl, ::Vector{InfPlc}; n_quo, p_part)
hilbert_class_field(k::AnticNumberField)
ring_class_field(::NfAbsOrd)
```

### Example

```@repl
using Hecke # hide
Qx, x = PolynomialRing(FlintQQ, "x");
K, a = NumberField(x^2 - 10, "a");
c, mc = class_group(K)
A = ray_class_field(mc)
```

## Conversions

Given a ray class field, it is possible to actually compute defining equation(s) for this field.
In general, the number field constructed this way will be non-simple by type and is defined
by a polynomial for each maximal cyclic quotient of prime power order in the defining group.

The algorithm employed is based on Kummer-theory and requires the addition of a suitable
root of unity. Progress can be monitored by setting {{{set_verbose_level(:ClassField, n)}}}
where $0\le n\le 3$

```@docs
number_field(C::ClassField)
```

```@repl
using Hecke; # hide
Qx, x = PolynomialRing(FlintQQ, "x");
k, a = NumberField(x^2 - 10, "a");
c, mc = class_group(k);
A = ray_class_field(mc)
K = number_field(A)
ZK = maximal_order(K)
isone(discriminant(ZK))
```

```@docs
ray_class_field(K::NfRel{nf_elem})
genus_field(A::ClassField, k::AnticNumberField)
maximal_abelian_subfield(A::ClassField, k::AnticNumberField)
maximal_abelian_subfield(K::NfRel{nf_elem})
```

## Invariants
```@docs
degree(C::ClassField)
base_ring(A::Hecke.ClassField) 
base_field(A::Hecke.ClassField) 
discriminant(C::Hecke.ClassField)
conductor(C::Hecke.ClassField) 
defining_modulus(C::ClassField)
iscyclic(C::ClassField)
isconductor(C::Hecke.ClassField, m::NfOrdIdl, inf_plc::Vector{InfPlc})
isnormal(C::ClassField)
iscentral(C::ClassField)
```

## Operations
```@docs
*(a::Hecke.ClassField, b::Hecke.ClassField)
compositum(a::Hecke.ClassField, b::Hecke.ClassField)
==(a::Hecke.ClassField, b::Hecke.ClassField)
intersect(a::Hecke.ClassField, b::Hecke.ClassField)
prime_decomposition_type(C::Hecke.ClassField, p::Hecke.NfAbsOrdIdl)
Hecke.issubfield(a::ClassField, b::ClassField)
Hecke.islocal_norm(r::Hecke.ClassField, a::Hecke.NfAbsOrdElem)
Hecke.islocal_norm(r::Hecke.ClassField, a::Hecke.NfAbsOrdElem, p::Hecke.NfAbsOrdIdl)
Hecke.normal_closure(r::Hecke.ClassField) 
subfields(r::ClassField)
subfields(r::ClassField, d::Int)
```

