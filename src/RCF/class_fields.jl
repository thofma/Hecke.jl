function Base.show(io::IO, C::ClassField_pp{S, T}) where {S, T}
  println(IOContext(io, :compact => true), "Cyclic class field of degree $(degree(C)) defined modulo $(defining_modulus(C))")
  if isdefined(C, :a)
    println(io, "Kummer generator ", C.a)
  end
  if isdefined(C, :K)
    println(io, "Kummer extension: ", C.K)
  end
  if isdefined(C, :A)
    println(io, "Defining  polynomial ", C.A.pol)
  end
end

function Base.show(io::IO, CF::ClassField)
  @show_name(io, CF)
  @show_special(io, CF)
  print(IOContext(io, :compact => true), "Class field defined mod ",
                   defining_modulus(CF), " of structure ",
                   codomain(CF.quotientmap))
end

###############################################################################
#
#  Modulus function
#
###############################################################################

@doc Markdown.doc"""
    defining_modulus(CF::ClassField)

The modulus, i.e. an ideal of the set of real places, used to create the
class field.
"""
function defining_modulus(CF::ClassField)
  return _modulus(CF.rayclassgroupmap)
end

function defining_modulus(CF::ClassField_pp)
  return _modulus(CF.rayclassgroupmap)
end

function _modulus(mq::MapRayClassGrp)
  return mq.defining_modulus::Tuple{NfOrdIdl, Vector{InfPlc}}
end

function _modulus(mq::MapClassGrp)
  return (ideal(order(codomain(mq)), 1), InfPlc[])::Tuple{NfOrdIdl, Vector{InfPlc}}
end

###############################################################################
#
#  Base ring and Base field
#
###############################################################################

@doc Markdown.doc"""
    base_ring(A::ClassField)

The maximal order of the field that $A$ is defined over.
"""
function base_ring(A::ClassField)
  return order(codomain(A.rayclassgroupmap))
end

@doc Markdown.doc"""
    base_field(A::ClassField)

The number field that $A$ is defined over.
"""
function base_field(A::ClassField)
  return number_field(base_ring(A))
end

function base_ring(A::ClassField_pp)
  return order(codomain(A.rayclassgroupmap))
end

function base_field(A::ClassField_pp)
  return number_field(base_ring(A))
end

###############################################################################
#
#  Degree
#
###############################################################################

@doc Markdown.doc"""
    degree(A::ClassField)

The degree of $A$ over its base field, i.e. the size of the defining ideal group.
"""
function degree(A::ClassField)
  if A.degree == -1
    A.degree = Int(order(codomain(A.quotientmap)))
  end
  return A.degree
end

function degree(A::ClassField_pp{S, T}) where {S, T}
  if A.degree == -1
    A.degree = Int(order(codomain(A.quotientmap)))
  end
  return A.degree
end

###############################################################################
#
#  Exponent
#
###############################################################################

@doc Markdown.doc"""
    exponent(A::ClassField)

The exponent of $A$ over its base field, i.e. the exponent of the Galois
group of the extension.
"""
function exponent(A::ClassField{S, T}) where {S, T}
  return Int(exponent(codomain(A.quotientmap)))
end

function exponent(A::ClassField_pp{S, T}) where {S, T}
  return Int(exponent(codomain(A.quotientmap)))
end

###############################################################################
#
#  Compositum
#
###############################################################################

@doc Markdown.doc"""
    compositum(a::ClassField, b::ClassField) -> ClassField

The compositum of $a$ and $b$ as a (formal) class field.
"""
function compositum(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  d = lcm(degree(a), degree(b))
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  r, mr = ray_class_group(c, c_inf, n_quo = Int(d))
  C = ray_class_field(mr)
  @assert domain(C.rayclassgroupmap) == r
  h = norm_group_map(C, [a,b])
  U = intersect(kernel(h[1])[1], kernel(h[2])[1])
  q, mq = quo(codomain(C.quotientmap), U)
  return ray_class_field(mr, GrpAbFinGenMap(C.quotientmap * mq))
end

@doc Markdown.doc"""
    *(A::ClassField, B::ClassField) -> ClassField

The compositum of $a$ and $b$ as a (formal) class field.
"""
*(a::ClassField, b::ClassField) = compositum(a, b)

###############################################################################
#
#  Intersection
#
###############################################################################

@doc Markdown.doc"""
    intersect(a::ClassField, b::ClassField) -> ClassField

The intersection of $a$ and $b$ as a class field.
"""
function Base.intersect(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  d = lcm(degree(a), degree(b))

  r, mr = ray_class_group(c, c_inf, n_quo = Int(d))
  C = ray_class_field(mr)
  h = norm_group_map(C, [a,b])
  U = kernel(h[1])[1] + kernel(h[2])[1]
  q, mq = quo(codomain(C.quotientmap), U)
  return ray_class_field(mr, GrpAbFinGenMap(C.quotientmap * mq))
end

###############################################################################
#
#  Subfield
#
###############################################################################

@doc Markdown.doc"""
    is_subfield(a::ClassField, b::ClassField) -> Bool

Determines if $a$ is a subfield of $b$.
"""
function is_subfield(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  d = lcm(degree(a), degree(b))

  r, mr = ray_class_group(c, c_inf, n_quo = Int(d))
  C = ray_class_field(mr)
  h = norm_group_map(C, [a,b])
  return issubset(kernel(h[2])[1], kernel(h[1])[1])
end

###############################################################################
#
#  Equality
#
###############################################################################

@doc Markdown.doc"""
    ==(a::ClassField, b::ClassField)

Tests if $a$ and $b$ are equal.
"""
function ==(a::ClassField, b::ClassField)
  @assert base_ring(a) == base_ring(b)
  mq1 = a.quotientmap
  mq2 = b.quotientmap
  if !is_isomorphic(codomain(mq1), codomain(mq2))
    return false
  end
  expo = Int(exponent(codomain(mq1)))
  c = lcm(defining_modulus(a)[1], defining_modulus(b)[1])
  c_inf = union(defining_modulus(a)[2], defining_modulus(b)[2])
  r, mr = ray_class_group(c, c_inf, n_quo = expo)
  C = ray_class_field(mr)
  @assert defining_modulus(C) == (c, c_inf)
  h = norm_group_map(C, [a,b])
  return is_eq(kernel(h[2])[1], kernel(h[1])[1])
end


###############################################################################
#
#  IsCyclic
#
###############################################################################

@doc Markdown.doc"""
    is_cyclic(C::ClassField)

Tests if the (relative) automorphism group of $C$ is cyclic (by checking
the defining ideal group).
"""
function is_cyclic(C::ClassField)
  mp = C.quotientmap
  return is_cyclic(codomain(mp))
end

###############################################################################
#
#  Maximal p-subfield
#
###############################################################################

@doc Markdown.doc"""
    maximal_p_subfield(C::ClassField, p::Int)

Returns the class field corresponding to the maximal subextension of
prime power degree.
"""
function maximal_p_subfield(C::ClassField, p::Int)
  mg = C.quotientmap
  v = valuation(degree(C), p)
  q, mq = quo(codomain(mg), p^v, false)
  s, ms = snf(q)
  mg1 = mg*mq*inv(ms)
  return ray_class_field(C.rayclassgroupmap, mg1)
end


@doc Markdown.doc"""
    is_local_norm(r::ClassField, a::NfAbsOrdElem, p::NfAbsOrdIdl) -> Bool

Tests if $a$ is a local norm at $p$ in the extension implictly given by $r$.
Currently the conductor cannot have infinite places.
"""
function is_local_norm(r::ClassField, a::NfAbsOrdElem, p::NfAbsOrdIdl)
  m0, minf = conductor(r)
  if length(minf) > 0
    error("not implemented yet")
  end
  m0 = defining_modulus(r)[1] #need the maps...
  @assert is_prime(p)
  v1 = valuation(a, p)
  v2 = valuation(m0, p)
  n0 = divexact(m0, p^v2)
  o0 = p^(v1 + v2)
  y = crt(order(p)(1), n0, a, o0)
  y = y*order(p)
  y = divexact(y, p^v1)

  return isone(r.quotientmap(preimage(r.rayclassgroupmap, y)))
end

################################################################################
#
#  Some applications
#
################################################################################

@doc Markdown.doc"""
    is_local_norm(r::ClassField, a::NfAbsOrdElem) -> Bool

Tests if $a$ is a local norm at all finite places in the extension implictly given by $r$.
"""
function is_local_norm(r::ClassField, a::NfAbsOrdElem)
  K = base_field(r)
  m0, minf = conductor(r)
  if !is_positive(a, minf)
    return false
  end
  fl = factor(m0*a)
  return all(x -> is_local_norm(r, a, x), keys(fl))
end

@doc Markdown.doc"""
    prime_decomposition_type(C::ClassField, p::NfAbsOrdIdl) -> (Int, Int, Int)

For a prime $p$ in the base ring of $r$, determine the splitting type of $p$
in $r$. ie. the tuple $(e, f, g)$ giving the ramification degree, the inertia
and the number of primes above $p$.
"""
function prime_decomposition_type(C::T, p::NfAbsOrdIdl) where T <: Union{ClassField, ClassField_pp}
  @hassert :ClassField 1 is_prime(p)
  mR = C.rayclassgroupmap
  m0 = defining_modulus(C)[1]
  R = domain(mR)

  v = valuation(m0, p)
  if v == 0
    f = Int(order(C.quotientmap(mR\p)))
    return (1, f, divexact(degree(C), f))
  end
  r, mr = ray_class_group(divexact(m0, p^v), defining_modulus(C)[2], n_quo = Int(exponent(R)))
  lp, sR = find_gens(mR, coprime_to = minimum(m0))
  h = hom(sR, [preimage(mr, p) for p = lp])
  k, mk = kernel(GrpAbFinGenMap(C.quotientmap), false)
  q, mq = cokernel(mk*h, false)
  f = Int(order(mq(preimage(mr, p))))
  e = Int(divexact(degree(C), Int(order(q))))
  return (e, f, Int(divexact(order(q), f)))
end


###############################################################################
#
#  Ray Class Field interface
#
###############################################################################

@doc Markdown.doc"""
    ray_class_field(m::MapClassGrp) -> ClassField
    ray_class_field(m::MapRayClassGrp) -> ClassField

Creates the (formal) abelian extension defined by the map $m: A \to I$
where $I$ is the set of ideals coprime to the modulus defining $m$ and $A$
is a quotient of the ray class group (or class group). The map $m$
must be the map returned from a call to {class_group} or {ray_class_group}.
"""
function ray_class_field(m::Union{MapClassGrp, MapRayClassGrp})
  return ray_class_field(m, id_hom(domain(m)))
end

@doc Markdown.doc"""
    ray_class_field(m::Union{MapClassGrp, MapRayClassGrp}, quomap::GrpAbFinGenMap) -> ClassField

For $m$ a map computed by either {ray_class_group} or {class_group} and
$q$ a canonical projection (quotient map) as returned by {quo} for q
quotient of the domain of $m$ and a subgroup of $m$, create the
(formal) abelian extension where the (relative) automorphism group
is canonically isomorphic to the codomain of $q$.
"""
function ray_class_field(m::S, quomap::T) where {S <: Union{MapClassGrp, MapRayClassGrp}, T}
  domain(quomap) == domain(m) || error("1st map must be a (ray)class group map, and the 2nd must be a projection of the domain of the 1st")
  CF = ClassField{S, T}()
  CF.rayclassgroupmap = m
  D = codomain(quomap)
  S1, mS1 = snf(D)
  iS1 = inv(mS1)#GrpAbFinGenMap(D, S1, mS1.imap, mS1.map)
  CF.quotientmap = Hecke.compose(quomap, iS1)
  return CF
end

@doc Markdown.doc"""
    hilbert_class_field(k::AnticNumberField) -> ClassField

The Hilbert class field of $k$ as a formal (ray-) class field.
"""
function hilbert_class_field(k::AnticNumberField)
  return ray_class_field(class_group(k)[2])
end

@doc Markdown.doc"""
    ray_class_field(I::NfAbsOrdIdl; n_quo = 0) -> ClassField

The ray class field modulo $I$. If `n_quo` is given, then the largest
subfield of exponent $n$ is computed.
"""
function ray_class_field(I::NfAbsOrdIdl; n_quo = -1)
  return ray_class_field(ray_class_group(I, n_quo = n_quo)[2])
end

@doc Markdown.doc"""
    ray_class_field(I::NfAbsOrdIdl, inf::Vector{InfPlc}; n_quo = 0) -> ClassField

The ray class field modulo $I$ and the infinite places given. If `n_quo` is given, then the largest
subfield of exponent $n$ is computed.
"""
function ray_class_field(I::NfAbsOrdIdl, inf::Vector{InfPlc}; n_quo = -1)
  return ray_class_field(ray_class_group(I, inf, n_quo = n_quo)[2])
end
