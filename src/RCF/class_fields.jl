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

@doc raw"""
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
  return mq.defining_modulus::Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}}}
end

function _modulus(mq::MapClassGrp)
  return (ideal(order(codomain(mq)), 1), InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}[])::Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Vector{InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}}}
end

###############################################################################
#
#  Base ring and Base field
#
###############################################################################

@doc raw"""
    base_ring(A::ClassField)

The maximal order of the field that $A$ is defined over.
"""
function base_ring(A::ClassField)
  return order(codomain(A.rayclassgroupmap))
end

base_ring_type(::Type{ClassField}) = AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}

@doc raw"""
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

@doc raw"""
    degree(A::ClassField)

The degree of $A$ over its base field, i.e. the size of the defining ideal group.
"""
function degree(A::ClassField)
  if A.degree == -1
    A.degree = Int(order(codomain(A.quotientmap)))
  end
  return A.degree
end

function degree(::Type{ZZRingElem}, A::ClassField)
  if A.degree != -1
    return ZZRingElem(A.degree)
  end
  o = order(codomain(A.quotientmap))
  if fits(Int, o)
    A.degree = Int(o)
  end
end

function degree(A::ClassField, QQ::QQField)
  return Int(degree(ZZRingElem, A, QQ))
end

function degree(::Type{ZZRingElem}, A::ClassField, ::QQField)
  return degree(ZZRingElem, A) * absolute_degree(base_field(A))
end

absolute_degree(A::ClassField) = degree(A, QQ)

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

@doc raw"""
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

@doc raw"""
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
  _, mU = intersect(kernel(h[1], false)[2], kernel(h[2], false)[2], false)
  q, mq = quo(codomain(C.quotientmap), mU, false)
  return ray_class_field(mr, FinGenAbGroupHom(C.quotientmap * mq))
end

@doc raw"""
    *(A::ClassField, B::ClassField) -> ClassField

The compositum of $a$ and $b$ as a (formal) class field.
"""
*(a::ClassField, b::ClassField) = compositum(a, b)

###############################################################################
#
#  Intersection
#
###############################################################################

@doc raw"""
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
  return ray_class_field(mr, FinGenAbGroupHom(C.quotientmap * mq))
end

###############################################################################
#
#  Subfield
#
###############################################################################

@doc raw"""
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

@doc raw"""
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

function Base.hash(a::ClassField, h::UInt)
  return hash(base_ring(a), h)
end

###############################################################################
#
#  IsCyclic
#
###############################################################################

@doc raw"""
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

@doc raw"""
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


@doc raw"""
    is_local_norm(r::ClassField, a::AbsNumFieldOrderElem, p::AbsNumFieldOrderIdeal) -> Bool

Tests if $a$ is a local norm at $p$ in the extension implicitly given by $r$.
Currently the conductor cannot have infinite places.
"""
function is_local_norm(r::ClassField, a::AbsNumFieldOrderElem, p::AbsNumFieldOrderIdeal)
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

@doc raw"""
    is_local_norm(r::ClassField, a::AbsNumFieldOrderElem) -> Bool

Tests if $a$ is a local norm at all finite places in the extension implicitly given by $r$.
"""
function is_local_norm(r::ClassField, a::AbsNumFieldOrderElem)
  K = base_field(r)
  m0, minf = conductor(r)
  if !isempty(minf) && !is_positive(a, _embedding.(minf))
    return false
  end
  fl = factor(m0*a)
  return all(x -> is_local_norm(r, a, x), keys(fl))
end

@doc raw"""
    prime_decomposition_type(C::ClassField, p::AbsNumFieldOrderIdeal) -> (Int, Int, Int)

For a prime $p$ in the base ring of $r$, determine the splitting type of $p$
in $r$. ie. the tuple $(e, f, g)$ giving the ramification degree, the inertia
and the number of primes above $p$.
"""
function prime_decomposition_type(C::T, p::AbsNumFieldOrderIdeal) where T <: Union{ClassField, ClassField_pp}
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
  h = hom(parent(first(sR)), domain(mr), sR, [preimage(mr, p) for p = lp])
  k, mk = kernel(FinGenAbGroupHom(C.quotientmap), false)
  q, mq = cokernel(mk*h, false)
  f = Int(order(mq(preimage(mr, p))))
  e = Int(divexact(degree(C), Int(order(q))))
  return (e, f, Int(divexact(order(q), f)))
end

@doc raw"""
    decomposition_group(C::ClassField, p::[InfPlc | AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}]) -> FinGenAbGroup

Compute the decomposition group of any infinite place or prime ideal of the
base field (ring) as a subgroup of the norm group.
"""
function decomposition_group(C::ClassField, p::InfPlc)
  D, Dinf = defining_modulus(C)
  if !(p in Dinf)
    return norm_group(C)[1]
  end

  DDinf = [x for x = Dinf if x != p]
  RR = ray_class_field(D, DDinf, n_quo = exponent(C))
  CC = ray_class_field(C.rayclassgroupmap)
  h = norm_group_map(CC, RR)
  return C.quotientmap(preimage(CC.quotientmap, kernel(h)[1])[1])[1]
end

function decomposition_group(C::ClassField, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  @assert is_prime(p)
  @assert order(p) == base_ring(C)
  R, mR = norm_group(C)
  D, Dinf  = defining_modulus(C)
  if valuation(D, p) == 0 #easy case
    return sub(R, [preimage(mR, p)])[1]
  end

  DD = divexact(D, p^valuation(D,p))
  RR, mRR = ray_class_group(DD, Dinf, n_quo = exponent(C))
  CC = ray_class_field(mRR)
  X = ray_class_field(C.rayclassgroupmap)
  h = norm_group_map(X, CC)
  x = preimage(h, CC.quotientmap(preimage(mRR, p)))
  k, ik = kernel(h)
  g = gens(k)
  g = map(ik, g)
  @assert parent(x) == domain(h)
  push!(g, x)
  @assert parent(x) == norm_group(X)[1]
  h = norm_group_map(X, C)
  return sub(R, map(h, g))[1]
end

@doc raw"""
    inertia_subgroup(C::ClassField, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> FinGenAbGroup

Compute the inertia subgroup of any prime ideal of the
base ring as a subgroup of the norm group.
"""
function inertia_subgroup(C::ClassField, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  #same as above, just the element p is missing...
  @assert is_prime(p)
  @assert order(p) == base_ring(C)
  R, mR = norm_group(C)
  D, Dinf  = defining_modulus(C)
  if valuation(D, p) == 0 #easy case
    return R
  end

  DD = divexact(D, p^valuation(D,p))
  RR, mRR = ray_class_group(DD, Dinf, n_quo = exponent(C))
  CC = ray_class_field(mRR)
  X = ray_class_field(C.rayclassgroupmap)
  h = norm_group_map(X, CC)
  k, ik = kernel(h)
  g = gens(k)
  g = map(ik, g)
  h = norm_group_map(X, C)
  return sub(R, map(h, g))[1]
end

@doc raw"""
    decomposition_field(C::ClassField, p::[InfPlc | AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}]) -> ClassField

Compute the decomposition field, ie. the field fixed by the decomposition group
as a class field.
"""
function decomposition_field(C::ClassField, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return fixed_field(C, decomposition_group(C, p))
end

@doc raw"""
    inertia_field(C::ClassField, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) -> ClassField

Compute the inertia field, ie. the field fixed by the decomposition group
as a class field.
"""
function inertia_field(C::ClassField, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return fixed_field(C, inertia_subgroup(C, p))
end

function decomposition_field(C::ClassField, p::InfPlc)
  return fixed_field(C, decomposition_group(C, p))
end

@doc raw"""
    knot(C::ClassField)

The knot (or number knot) defined by Scholz is the obstruction to the
Hasse norm theorem: the quotient of local norms modulo global norms.
For abelian extensions this is can easily be computed.

Computes the obstruction as an abstract abelian group, ie. the Hasse norm
theorem holds for `C` over the base field iff this group is trivial.
"""
function knot(C::ClassField)
  c, ci = conductor(C)
  G = norm_group(C)[1]
  if norm(c) == 1 && length(ci) == 0 #unramifed
    return snf(H2_G_QmodZ(G))[1]
  end
  U = vcat(FinGenAbGroup[decomposition_group(C, p) for p = keys(factor(c))],
           FinGenAbGroup[decomposition_group(C, i) for i = ci])
  phi = H2_G_QmodZ_restriction(G, U)
  k = kernel(phi[1])[1]
  for i=2:length(phi)
    k = intersect(k, kernel(phi[i])[1])
  end
  return snf(k)[1]
end



###############################################################################
#
#  Ray Class Field interface
#
###############################################################################

@doc raw"""
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

@doc raw"""
    ray_class_field(m::Union{MapClassGrp, MapRayClassGrp}, quomap::FinGenAbGroupHom) -> ClassField

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
  iS1 = inv(mS1)#FinGenAbGroupHom(D, S1, mS1.imap, mS1.map)
  CF.quotientmap = Hecke.compose(quomap, iS1)
  return CF
end

@doc raw"""
    hilbert_class_field(k::AbsSimpleNumField) -> ClassField

The Hilbert class field of $k$ as a formal (ray-) class field.
"""
function hilbert_class_field(k::AbsSimpleNumField)
  return ray_class_field(class_group(k)[2])
end

@doc raw"""
    ray_class_field(I::AbsNumFieldOrderIdeal; n_quo = 0) -> ClassField

The ray class field modulo $I$. If `n_quo` is given, then the largest
subfield of exponent $n$ is computed.
"""
function ray_class_field(I::AbsNumFieldOrderIdeal; n_quo = -1)
  return ray_class_field(ray_class_group(I, n_quo = n_quo)[2])
end

@doc raw"""
    ray_class_field(I::AbsNumFieldOrderIdeal, inf::Vector{InfPlc}; n_quo = 0) -> ClassField

The ray class field modulo $I$ and the infinite places given. If `n_quo` is given, then the largest
subfield of exponent $n$ is computed.
"""
function ray_class_field(I::AbsNumFieldOrderIdeal, inf::Vector{<: InfPlc}; n_quo = -1)
  return ray_class_field(ray_class_group(I, inf, n_quo = n_quo)[2])
end


prime_decomposition(::ZZRing, p::Int) = [[p*ZZ, 1]]

"""
    grunwald_wang(dp::Dict{<:NumFieldOrderIdeal, Int})
    grunwald_wang(dp::Dict{<:NumFieldOrderIdeal, Int}, di::Dict{<:NumFieldEmb, Int})

For a collection of places given via ideals as keys of `dp` and embeddings
given as keys of `di` find a cyclic extension where the completions at
the places have the degrees as the values of the dictionaries.

The degree will be the `lcm` of the local degree (values), the extension will
be unramified at the places in `dp` unless they involve primes above `2`.

The field will be constructed as a `ray_class_field`.

# EXAMPLES
```julia
julia> A = grunwald_wang(Dict(3*ZZ => 3, 5*ZZ => 2))
Class field defined mod (<13, 13>, InfPlc{AbsSimpleNumField, AbsSimpleNumFieldEmbedding}[]) of structure Abelian group with structure: Z/6

julia> K = absolute_simple_field(number_field(A))[1];

julia> prime_decomposition_type(maximal_order(K), 5)
3-element Vector{Tuple{Int64, Int64}}:
 (2, 1)
 (2, 1)
 (2, 1)


julia> prime_decomposition_type(maximal_order(K), 3)
2-element Vector{Tuple{Int64, Int64}}:
 (3, 1)
 (3, 1)

```
"""
function grunwald_wang(dp::Dict{<:NumFieldOrderIdeal, Int}, di::Dict{<:NumFieldEmb, Int} = Dict{NumFieldEmb, Int}())
  lp = collect(keys(dp))
  li = collect(keys(di))
  if length(li) == 0
    if length(lp) == 0
      error("no data specified, giving up")
    end
    k = number_field(order(lp[1]))
  else
    k = number_field(li[1])
  end

  if k == QQ
    kk = rationals_as_number_field()[1]
    zz = maximal_order(kk)
    d = Dict{Any, Int}(gen(p)*zz => dp[p] for p = keys(dp))
    if length(di) > 0
      push!(d, complex_embeddings(kk)[1] => first(values(di)))
    end
  else
    d = Dict{Any, Int}()
    for i = dp
      push!(d, i)
    end
    for i = di
      push!(d, i)
    end
  end
  A = _grunwald_wang(d)
  return A
end

function _grunwald_wang(d::Dict{<:Any, Int})
  lp = collect(keys(d))
  li = [x for x = lp if isa(x, NumFieldEmb)]
  lp = [x for x = lp if isa(x, NumFieldOrderIdeal)]
  @assert length(lp) + length(li) == length(d)

  if length(li) == 0
    if length(lp) == 0
      error("no data specified, giving up")
    end
    k = number_field(order(lp[1]))
  else
    k = number_field(li[1])
  end
  @assert all(x->k === number_field(x), li)
  @assert all(x->k === number_field(order(x)), lp)

  deg = lcm([x for x = values(d)]...)
  ld = factor(deg).fac
  if length(keys(ld)) == 1
    return _grunwald_wang_pp(d)
  end
  S = ray_class_field(1*maximal_order(k))
  for p = keys(ld)
    dp = Dict(x => Int(gcd(v, p^ld[p])) for (x, v) = d)
    S *= _grunwald_wang_pp(dp)
  end
  return rewrite_with_conductor(S)
end

function _grunwald_wang_pp(d::Dict{<:Any, Int})
  #we'll try to be as unramified as possible at the ideals in d
  #which means:
  # - potential ramification at 2 (if 2 in d)
  # - unram elsewhere.

  lp = collect(keys(d))
  li = [x for x = lp if isa(x, NumFieldEmb)]
  lp = [x for x = lp if isa(x, NumFieldOrderIdeal)]

  if length(li) == 0
    if length(lp) == 0
      error("no data specified, giving up")
    end
    k = number_field(order(lp[1]))
  else
    k = number_field(li[1])
  end

  li = [x for x = li if isreal(x)]
  @assert all(x->d[x] in [1,2], li)

  li = InfPlc[infinite_place(x) for x = li] #for the conductor

  zk = maximal_order(k)

  deg = lcm([x for x = values(d)]...)

  @assert is_prime_power(deg) #for now, to keep things simple

  con = prod(lp)
  #complication:
  # if deg = 2^l, l >= 3 then, since there are no unramifed
  # extensions of Q_2 of this degree, 2 has to divide the conductor
  # From Carlo's PhD, Thm 1.41: (for all primes, but here used for 2)
  # P a prime above 2 in k/ zk, then
  # v_P(con) <= p/(p-1) * (1+ l * e(P/p))
  if iseven(deg) #2^l
    l = valuation(deg, 2)
    l2 = [p for p = lp if minimum(p) == 2]
    if length(l2) > 0
      con *= prod(p^(2*(1+l*ramification_index(p)-1)) for p = l2)
    end
    #the -1 at the end is since p is already once in con
    lp = [p for p = lp if minimum(p) != 2]
  else
    l2 = []
  end

  #in general: if the classgroup has a p^s and deg = p^l,
  #then we need ideals with a p^(l-s) might yield a p^l at then end
  c, _ = class_group(zk)
  if order(c) > 1
    s = gcd(deg, elementary_divisors(c)[end])
  else
    s = 1
  end
  P = PrimesSet(2, -1, Int(divexact(deg, s)), 1)
  st = iterate(P)
  PP = prime_decomposition(zk, st[1])
  iP = 1
  cnt = 0
  #need to check the degree of the completion at p
  #for p unramified this is "just" the order in the ray class group
  #for p ramified this is unfortunately
  #  the order in the ray class group of the modulus coprime to p
  #  time the index of this group in the full (ramified) one
  while true
    R, mR = ray_class_group(con, li, n_quo = deg)
    val = FinGenAbGroupElem[preimage(mR, p) for p = lp]

    if length(lp) > 0 && any(x->order(val[x]) % d[lp[x]] != 0, 1:length(lp))
#      @show "too small"
    else
      if iseven(deg) && length(l2) > 0
        S1 = ray_class_field(mR)
        S2 = [ray_class_field(divexact(con, p^valuation(con, p)), n_quo = deg) for p = l2]
        ngp = norm_group_map(S1, S2)
        s, _ = sub(R, [val[i] for i = 1:length(lp)])
        s += preimage(S1.quotientmap, sum(kernel(x)[1] for x = ngp))[1]
      else
        s, _ = sub(R, [val[i] for i = 1:length(lp)])
      end
      s = saturate(s, R)
      fl, s = has_complement(s, R)
      @assert fl
      c, mc = quo(R, s)
      c, _mc = quo(c, FinGenAbGroupElem[d[lp[i]] * mc(val[i]) for i = 1:length(lp)])
      mc = mc * _mc
      if all(i->order(mc(val[i])) == d[lp[i]], 1:length(lp))
#        @show :cyc, snf(c)[1]
        for (u, mu) = subgroups(c, quotype = [deg])
          q, mq = quo(c, u)
          A = ray_class_field(mR, mc*mq)
          if all(vcat(lp, l2)) do p
              y = prime_decomposition_type(A, p)
              y[1]*y[2] == d[p]
            end
#            @show :place
            _, mi = conductor(A)
            if all(x in mi for x = li if d[_embedding(x)] == 2) &&
                  !any(x in mi for x = li if d[_embedding(x)] == 1)
              return A
            end
          end
        end
      end
    end
    con *= PP[iP][1]
    iP += 1
    if length(PP) < iP
      st = iterate(P, st[2])
      PP = prime_decomposition(zk, st[1])
      iP = 1
    end
    cnt += 1
    if cnt > 20
#      error("bla")
    end
  end
end
