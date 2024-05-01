################################################################################
#
#  Construction
#
################################################################################

# compute the torsion quadratic module M/N

@doc raw"""
    torsion_quadratic_module(M::ZZLat, N::ZZLat; gens::Union{Nothing, Vector{<:Vector}} = nothing,
                                                 snf::Bool = true,
                                                 modulus::RationalUnion = QQFieldElem(0),
                                                 modulus_qf::RationalUnion = QQFieldElem(0),
                                                 check::Bool = true) -> TorQuadModule

Given a Z-lattice $M$ and a sublattice $N$ of $M$, return the torsion quadratic
module $M/N$.

If `gens` is set, the images of `gens` will be used as the
generators of the abelian group $M/N$.

If `snf` is `true`, the underlying abelian group will be in Smith normal form.
Otherwise, the images of the basis of $M$ will be used as the generators.

One can decide on the modulus for the associated finite bilinear and quadratic
forms by setting `modulus` and `modulus_qf` respectively to the desired values.
"""
function torsion_quadratic_module(M::ZZLat, N::ZZLat; gens::Union{Nothing, Vector{<:Vector}} = nothing,
                                                      snf::Bool = true,
                                                      modulus::RationalUnion = QQFieldElem(0),
                                                      modulus_qf::RationalUnion = QQFieldElem(0),
                                                      check::Bool = true)
  @req ambient_space(M) === ambient_space(N) """
      Lattices must have same ambient space
      """
  fl, _rels = is_sublattice_with_relations(M, N)
  @req fl "Second lattice must be a sublattice of first lattice"
  rels = change_base_ring(FlintZZ, _rels)
  A = abelian_group(rels)
  n = dim(ambient_space(M))
  BM = basis_matrix(M)
  if gens !== nothing && length(gens) > 0
    gens_in_A = elem_type(A)[]
    for g in gens
      @req length(g) == n "Generator not an element of the ambient space"
      fl, v = can_solve_with_solution(BM,
                                      matrix(FlintQQ, 1, n, g);
                                      side = :left)
      @req denominator(v) == 1 "Generator not an element of the lattice"
      ginA = A(change_base_ring(FlintZZ, v))
      push!(gens_in_A, ginA)
    end
    S, mS = sub(A, gens_in_A, false)
    if check
      if order(S) != order(A)
        throw(ArgumentError("Generators do not generate the torsion module"))
      end
    end
  else
    if snf
      S, mS = Hecke.snf(A)
    else
      S, mS = A, id_hom(A)
    end
  end
  # mS : S -> A
  # generators of S lifted along M -> M/N = A -> S
  if gens !== nothing  && length(gens) > 0
    gens_lift = gens
  else
    gens_lift = Vector{QQFieldElem}[reshape(collect(change_base_ring(FlintQQ, mS(s).coeff) * BM), :) for s in Hecke.gens(S)]
  end

  num = basis_matrix(M) * gram_matrix(ambient_space(M)) * transpose(basis_matrix(N))
  if iszero(modulus)
    _modulus = reduce(gcd, num; init = zero(QQFieldElem))
  else
    _modulus = QQ(modulus)
  end
  norm = reduce(gcd, diagonal(gram_matrix(N)); init = zero(QQFieldElem))

  if iszero(modulus_qf)
    _modulus_qf = gcd(norm, 2 * _modulus)
  else
    _modulus_qf = QQ(modulus_qf)
  end

  T = TorQuadModule()
  T.cover = M
  T.rels = N
  T.ab_grp = S
  T.proj = inv(mS).map
  T.gens_lift = gens_lift
  T.gens_lift_mat = matrix(FlintQQ, length(gens_lift), degree(M), reduce(vcat, gens_lift; init = QQFieldElem[]))
  T.modulus = _modulus
  T.modulus_qf = _modulus_qf
  T.value_module = QmodnZ(_modulus)
  T.value_module_qf = QmodnZ(_modulus_qf)
  T.is_normal = false
  return T
end

@doc raw"""
    discriminant_group(L::ZZLat) -> TorQuadModule

Return the discriminant group of `L`.

The discriminant group of an integral lattice `L` is the finite abelian
group `D = dual(L)/L`.

It comes equipped with the discriminant bilinear form

$$D \times D \to \mathbb{Q} / \mathbb{Z} \qquad (x,y) \mapsto \Phi(x,y) + \mathbb{Z}.$$

If `L` is even, then the discriminant group is equipped with the discriminant
quadratic form $D \to \mathbb{Q} / 2 \mathbb{Z}, x \mapsto \Phi(x,x) + 2\mathbb{Z}$.
"""
@attr TorQuadModule function discriminant_group(L::ZZLat)
  @req is_integral(L) "The lattice must be integral"
  if rank(L) == 0
    T = torsion_quadratic_module(dual(L), L; modulus = one(QQ), modulus_qf = QQ(2))
  else
    T = torsion_quadratic_module(dual(L), L)
  end
  set_attribute!(T, :is_degenerate => false)
  return T
end

@doc raw"""
    order(T::TorQuadModule) -> ZZRingElem

Return the order of `T`
"""
function order(T::TorQuadModule)
  return order(abelian_group(T))
end

@doc raw"""
    exponent(T::TorQuadModule) -> ZZRingElem

Return the exponent of `T`
"""
function exponent(T::TorQuadModule)
  return exponent(abelian_group(T))
end

@doc raw"""
    elementary_divisors(T::TorQuadModule) -> Vector{ZZRingElem}

Return the elementary divisors of underlying abelian group of `T`.
"""
function elementary_divisors(T::TorQuadModule)
  return elementary_divisors(abelian_group(T))
end

################################################################################
#
#  Basic field access
#
################################################################################

@doc raw"""
    abelian_group(T::TorQuadModule) -> FinGenAbGroup

Return the underlying abelian group of `T`.
"""
abelian_group(T::TorQuadModule) = T.ab_grp

@doc raw"""
    cover(T::TorQuadModule) -> ZZLat

For $T=M/N$ this returns $M$.
"""
cover(T::TorQuadModule) = T.cover

@doc raw"""
    relations(T::TorQuadModule) -> ZZLat

For $T=M/N$ this returns $N$.
"""
relations(T::TorQuadModule) = T.rels

@doc raw"""
    value_module(T::TorQuadModule) -> QmodnZ

Return the value module `Q/nZ` of the bilinear form of `T`.
"""
value_module(T::TorQuadModule) = T.value_module

@doc raw"""
    value_module_quadratic_form(T::TorQuadModule) -> QmodnZ

Return the value module `Q/mZ` of the quadratic form of `T`.
"""
value_module_quadratic_form(T::TorQuadModule) = T.value_module_qf

@doc raw"""
    modulus_bilinear_form(T::TorQuadModule) -> QQFieldElem

Return the modulus of the value module of the bilinear form of`T`.
"""
modulus_bilinear_form(T::TorQuadModule) = T.modulus

@doc raw"""
    modulus_quadratic_form(T::TorQuadModule) -> QQFieldElem

Return the modulus of the value module of the quadratic form of `T`.
"""
modulus_quadratic_form(T::TorQuadModule) = T.modulus_qf

################################################################################
#
#  Gram matrices
#
################################################################################

@doc raw"""
    gram_matrix_bilinear(T::TorQuadModule) -> QQMatrix

Return the gram matrix of the bilinear form of `T`.
"""
function gram_matrix_bilinear(T::TorQuadModule)
  if isdefined(T, :gram_matrix_bilinear)
    return T.gram_matrix_bilinear
  end
  g = gens(T)
  G = zero_matrix(FlintQQ, length(g), length(g))
  for i in 1:length(g)
    for j in 1:i
      G[i, j] = G[j, i] = lift(g[i] * g[j])
    end
  end
  T.gram_matrix_bilinear = G
  return G
end

@doc raw"""
    gram_matrix_quadratic(T::TorQuadModule) -> QQMatrix

Return the 'gram matrix' of the quadratic form of `T`.

The off diagonal entries are given by the bilinear form whereas the
diagonal entries are given by the quadratic form.
"""
function gram_matrix_quadratic(T::TorQuadModule)
  if isdefined(T, :gram_matrix_quadratic)
    return T.gram_matrix_quadratic
  end
  g = gens(T)
  r = length(g)
  G = zero_matrix(FlintQQ, r, r)
  for i in 1:r
    for j in 1:(i - 1)
      G[i, j] = G[j, i] = lift(g[i] * g[j])
    end
    G[i, i] = lift(quadratic_product(g[i]))
  end
  T.gram_matrix_quadratic = G
  return G
end

################################################################################
#
#  I/O
#
################################################################################

# TODO: Print like abelian group
function Base.show(io::IO, ::MIME"text/plain" , T::TorQuadModule)
  io = pretty(io)
  println(io, "Finite quadratic module")
  println(io, Indent(), "over integer ring")
  print(io, Dedent())
  print(io, "Abelian group: ")
  show_snf_structure(io, snf(abelian_group(T))[1])
  println(io)
  println(io, "Bilinear value module: ", value_module(T))
  println(io, "Quadratic value module: ", value_module_quadratic_form(T))
  println(io, "Gram matrix quadratic form: ")
  show(io, MIME"text/plain"() , gram_matrix_quadratic(T))
end

function Base.show(io::IO, T::TorQuadModule)
  if is_terse(io)
    print(io, "Finite quadratic module")
  else
    print(io, "Finite quadratic module: ")
    show_snf_structure(io, snf(abelian_group(T))[1])
    print(io, " -> ", value_module_quadratic_form(T))
  end
end

################################################################################
#
#  Elements
#
################################################################################

elem_type(::Type{TorQuadModule}) = TorQuadModuleElem

###############################################################################
#
#  Creation
#
###############################################################################

@doc raw"""
    (T::TorQuadModule)(a::FinGenAbGroupElem) -> TorQuadModuleElem

Coerce `a` to `T`.

```jldoctest
julia> R = rescale(root_lattice(:D,4),2);

julia> T = discriminant_group(R);

julia> A = abelian_group(T)
(Z/2)^2 x (Z/4)^2

julia> a = rand(A);

julia> A(T(a)) == a
true
```
"""
function (T::TorQuadModule)(a::FinGenAbGroupElem)
  @req abelian_group(T) === parent(a) "Parents do not match"
  return TorQuadModuleElem(T, a)
end

# Coerces an element of the ambient space of cover(T) to T
@doc raw"""
    (T::TorQuadModule)(v::Vector) -> TorQuadModuleElem

Coerce `v` to `T`.

For `T = M/N` this assumes that `v` lives in the ambient space of `M`
and $v \in M$.
"""
function (T::TorQuadModule)(v::Vector)
  @req length(v) == dim(ambient_space(cover(T))) "Vector of wrong length"
  vv = map(FlintQQ, v)
  if eltype(vv) != QQFieldElem
    error("Cannot coerce elements to the rationals")
  end
  return T(vv::Vector{QQFieldElem})
end

function (T::TorQuadModule)(v::Vector{QQFieldElem})
  @req length(v) == degree(cover(T)) "Vector of wrong length"
  vv = matrix(FlintQQ, 1, length(v), v)
  vv = change_base_ring(ZZ, solve(basis_matrix(cover(T)), vv; side = :left))
  return T(abelian_group(T)(vv * T.proj))
end

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, ::MIME"text/plain", a::TorQuadModuleElem)
  io = pretty(io)
  T = parent(a)
  println(io, "Element")
  print(io, Indent(), "of ", Lowercase(), T)
  println(io, Dedent())
  comps = a.data.coeff
  if length(comps) == 1
    print(io, "with component ", comps)
  else
    print(io, "with components ", comps)
  end
end

function show(io::IO, a::TorQuadModuleElem)
  if is_terse(io)
    print(io, "Element of finite quadratic module")
  else
    print(terse(io), a.data.coeff)
  end
end

################################################################################
#
#  Equalities and hashes
#
################################################################################

# To compare torsion quadratic module defined by quotients of lattices (defined
# in a same quadratic space), we just compare the top and the bottom lattices as
# embedded in the fixed ambient space.
# Of course, for a similar quotient one could mix up change the moduli for the
# given form, so we require those moduli to agree on both sides.
function Base.:(==)(S::TorQuadModule, T::TorQuadModule)
  modulus_bilinear_form(S) != modulus_bilinear_form(T) && return false
  modulus_quadratic_form(S) != modulus_quadratic_form(T) && return false
  relations(S) != relations(T) && return false
  return cover(S) == cover(T)
end

# Follow precisely the equlity test above
function Base.hash(T::TorQuadModule, u::UInt)
  u = Base.hash(modulus_bilinear_form(T), u)
  u = Base.hash(modulus_quadratic_form(T), u)
  u = Base.hash(relations(T), u)
  return Base.hash(cover(T), u)
end

function Base.:(==)(a::TorQuadModuleElem, b::TorQuadModuleElem)
  if parent(a) !== parent(b)
    return false
  else
    return data(a) == data(b)
  end
end

# Elements in the same parents and with the same data. Even though the equality
# of the parents is soft, the "data" comparison enforces strong equality of the
# parents (`===`) because of we want strong equality on the underlying abelian
# group structure.
function Base.hash(a::TorQuadModuleElem, u::UInt)
  h = xor(hash(parent(a)), hash(data(a)))
  return xor(h, u)
end

iszero(a::TorQuadModuleElem) = iszero(a.data)

################################################################################
#
#  Generators
#
################################################################################

function gens(T::TorQuadModule)
  if isdefined(T, :gens)
    return T.gens::Vector{TorQuadModuleElem}
  else
    _gens = TorQuadModuleElem[T(g) for g in gens(abelian_group(T))]
    T.gens = _gens
    return _gens
  end
end

number_of_generators(T::TorQuadModule) = length(T.gens_lift)

function gen(T::TorQuadModule, i::Int)
  if isdefined(T, :gens)
    return gens(T)[i]
  end
  return T(gen(abelian_group(T), i))
end

@doc raw"""
    getindex(T::TorQuadModule, i::Int) -> TorQuadModuleElem

Return the `i`-th generator of `T`.

This is equivalent to `gens(T)[i]`.

# Example
```jldoctest
julia> R = rescale(root_lattice(:D,4),2);

julia> D = discriminant_group(R);

julia> D[1]
Element
  of finite quadratic module: (Z/2)^2 x (Z/4)^2 -> Q/2Z
with components [1 0 0 0]

julia> D[2]
Element
  of finite quadratic module: (Z/2)^2 x (Z/4)^2 -> Q/2Z
with components [0 1 0 0]
```
"""
getindex(T::TorQuadModule, i::Int) = gen(T, i)

parent(a::TorQuadModuleElem) = a.parent

@doc raw"""
    data(a::TorQuadModuleElem) -> FinGenAbGroupElem

Return `a` as an element of the underlying abelian group.
"""
data(a::TorQuadModuleElem) = a.data

@doc raw"""
    (A::FinGenAbGroup)(a::TorQuadModuleElem)

Return `a` as an element of the underlying abelian group.

# Example
```jldoctest
julia> R = rescale(root_lattice(:D,4),2);

julia> D = discriminant_group(R);

julia> A = abelian_group(D)
(Z/2)^2 x (Z/4)^2

julia> d = D[1]
Element
  of finite quadratic module: (Z/2)^2 x (Z/4)^2 -> Q/2Z
with components [1 0 0 0]

julia> d == D(A(d))
true
```
"""
function (A::FinGenAbGroup)(a::TorQuadModuleElem)
  @req A === abelian_group(parent(a)) "Parents do not match"
  return a.data
end

@doc raw"""
    id(T::TorQuadModule) -> TorQuadModuleElem

Return the identity element for the abelian group structure on `T`.
"""
id(T::TorQuadModule) = T(id(abelian_group(T)))

################################################################################
#
#  Arithmetic of elements
#
################################################################################

function Base.:(+)(a::TorQuadModuleElem, b::TorQuadModuleElem)
  @req parent(a) === parent(b) "Parents do not match"
  T = parent(a)
  return T(a.data + b.data)
end

function Base.:(-)(a::TorQuadModuleElem)
  T = parent(a)
  return T(-a.data)
end

function Base.:(-)(a::TorQuadModuleElem, b::TorQuadModuleElem)
  @req parent(a) === parent(b) "Parents do not match"
  T = parent(a)
  return T(a.data - b.data)
end

function Base.:(*)(a::TorQuadModuleElem, b::ZZRingElem)
  T = parent(a)
  return T(a.data * b)
end

Base.:(*)(a::ZZRingElem, b::TorQuadModuleElem) = b * a

Base.:(*)(a::Integer, b::TorQuadModuleElem) = ZZRingElem(a) * b

Base.:(*)(a::TorQuadModuleElem, b::Integer) = b * a

################################################################################
#
#  Inner product
#
################################################################################

function Base.:(*)(a::TorQuadModuleElem, b::TorQuadModuleElem)
  T = parent(a)
  z = inner_product(ambient_space(cover(T)), lift(a), lift(b))
  return value_module(T)(z)
end

@doc raw"""
    inner_product(a::TorQuadModuleElem, b::TorQuadModuleElem) -> QmodnZElem

Return the inner product of `a` and `b`.
"""
inner_product(a::TorQuadModuleElem, b::TorQuadModuleElem)=(a*b)

################################################################################
#
#  Quadratic product
#
################################################################################

@doc raw"""
    quadratic_product(a::TorQuadModuleElem) -> QmodnZElem

Return the quadratic product of `a`.

It is defined in terms of a representative:
for $b + M \in M/N=T$, this returns
$\Phi(b,b) + n \mathbb{Z}$.
"""
function quadratic_product(a::TorQuadModuleElem)
  T = parent(a)
  al = lift(a)
  z = inner_product(ambient_space(cover(T)), al, al)
  return value_module_quadratic_form(T)(z)
end

################################################################################
#
#  Order
#
################################################################################

order(a::TorQuadModuleElem) = order(a.data)

################################################################################
#
#  Lift
#
################################################################################

@doc raw"""
    lift(a::TorQuadModuleElem) -> Vector{QQFieldElem}

Lift `a` to the ambient space of `cover(parent(a))`.

For $a + N \in M/N$ this returns the representative $a$.
"""
function lift(a::TorQuadModuleElem)
  T = parent(a)
  z = change_base_ring(FlintQQ, a.data.coeff) * T.gens_lift_mat
  return QQFieldElem[z[1, i] for i in 1:ncols(z)]
end

@doc raw"""
    representative(a::TorQuadModuleElem) -> Vector{QQFieldElem}

For $a + N \in M/N$ this returns the representative $a$.
An alias for `lift(a)`.
"""
representative(x::TorQuadModuleElem) = lift(x)

################################################################################
#
#  Iterator
#
################################################################################

Base.length(T::TorQuadModule) = Int(order(T))

Base.IteratorSize(::Type{TorQuadModule}) = Base.HasLength()

Base.eltype(::Type{TorQuadModule}) = TorQuadModuleElem

function Base.iterate(T::TorQuadModule)
  a, st = iterate(abelian_group(T))
  return T(a), st
end

function Base.iterate(T::TorQuadModule, st::UInt)
  st >= order(T) && return nothing
  a, st = iterate(abelian_group(T), st)
  return T(a), st
end

################################################################################
#
#  Map between torsion quadratic modules
#
################################################################################

@doc raw"""
    hom(T::TorQuadModule, S::TorQuadModule, M::ZZMatrix) -> TorQuadModuleMap

Given two torsion quadratic modules `T` and `S`, and a matrix `M` representing
an abelian group homomorphism between the underlying groups of `T` and `S`,
return the corresponding abelian group homomorphism between `T` and `S`.
"""
function hom(T::TorQuadModule, S::TorQuadModule, M::ZZMatrix)
  map_ab = hom(abelian_group(T), abelian_group(S), M)
  return TorQuadModuleMap(T, S, map_ab)
end

@doc raw"""
    hom(T::TorQuadModule, s::TorQuadModule, img::Vector{TorQuadModuleElem})
                                              -> TorQuadModuleMap

Given two torsion quadratic modules `T` and `S`, and a set of elements of `S`
containing as many elements as `ngens(T)`, return the abelian group homomorphism
between `T` and `S` mapping the generators of `T` to the elements of `img`.
"""
function hom(T::TorQuadModule, S::TorQuadModule, img::Vector{TorQuadModuleElem})
  _img = FinGenAbGroupElem[]
  @req length(img) == ngens(T) "Wrong number of elements"
  for g in img
    @req parent(g) === S "Elements have the wrong parent"
    push!(_img, abelian_group(S)(g))
  end
  map_ab = hom(abelian_group(T), abelian_group(S), _img)
  return TorQuadModuleMap(T, S, map_ab)
end

@doc raw"""
    abelian_group_homomorphism(f::TorQuadModuleMap) -> FinGenAbGroupHom

Return the underlying abelian group homomorphism of `f`.
"""
abelian_group_homomorphism(f::TorQuadModuleMap) = f.map_ab

@doc raw"""
    matrix(f::TorQuadModuleMap) -> ZZMatrix

Return the matrix defining the underlying abelian group homomorphism of `f`.
"""
matrix(f::TorQuadModuleMap) = matrix(abelian_group_homomorphism(f))

@doc raw"""
    identity_map(T::TorQuadModule) -> TorQuadModuleMap

Return the identity map of `T`.
"""
function identity_map(T::TorQuadModule)
  map_ab = id_hom(abelian_group(T))
  return TorQuadModuleMap(T, T, map_ab)
end

@doc raw"""
    trivial_morphism(T::TorQuadModule, U::TorQuadModule) -> TorQuadModuleMap

Return the abelian group homomorphism between `T` and `U` sending every
elements of `T` to the zero element of `U`.
"""
trivial_morphism(T::TorQuadModule, U::TorQuadModule) = hom(T, U, zero_matrix(ZZ, ngens(T), ngens(U)))

@doc raw"""
    trivial_morphism(T::TorQuadModule) -> TorQuadModuleMap

Return the abelian group endomorphism of `T` sending every elements of `T`
to the zero element of `T`.
"""
trivial_morphism(T::TorQuadModule) = trivial_morphism(T, T)

@doc raw"""
    zero(f::TorQuadModuleMap) -> TorQuadModuleMap

Given a map `f` between two torsion quadratic modules `T` and `U`,
return the trivial map between `T` and `U` (see [`trivial_morphism`](@ref)).
"""
zero(f::TorQuadModuleMap) = trivial_morphism(domain(f), codomain(f))

@doc raw"""
    id_hom(T::TorQuadModule) -> TorQuadModuleMap

Alias for [`identity_map`](@ref).
"""
id_hom(T::TorQuadModule) = identity_map(T)

@doc raw"""
    inv(f::TorQuadModuleMap) -> TorQuadModuleMap

Given a bijective abelian group homomorphism `f` between two torsion
quadratic modules, return the inverse of `f`.
"""
function inv(f::TorQuadModuleMap)
  @req is_bijective(f) "Underlying map must be bijective"
  map_ab = inv(f.map_ab)
  return TorQuadModuleMap(codomain(f),domain(f),map_ab)
end

@doc raw"""
    compose(f::TorQuadModuleMap, g::TorQuadModuleMap) -> TorQuadModuleMap

Given two abelian group homomorphisms $f\colon T \to S$ and
$g \colon S \to U$ between torsion quadratic modules, return the
composition $f\circ g\colon T \to U$.
"""
function compose(f::TorQuadModuleMap, g::TorQuadModuleMap)
  @req codomain(f) == domain(g) "Codomain of the first map should agree with the domain of the second one"
  map_ab = compose(f.map_ab, g.map_ab)
  return TorQuadModuleMap(domain(f), codomain(g), map_ab)
end

@doc raw"""
    image(f::TorQuadModuleMap, a::TorQuadModuleElem) -> TorQuadModuleElem

Given an abelian group homomorphism $f\colon T \to S$ between two torsion
quadratic modules, and given an element `a` of `T`, return the image
$f(a) \in S$.
"""
function image(f::TorQuadModuleMap, a::TorQuadModuleElem)
  @req parent(a) === domain(f) "a must be an element of the domain of f"
  A = abelian_group(domain(f))
  return codomain(f)(f.map_ab(A(a)))
end

@doc raw"""
    has_preimage_with_preimage(f::TorQuadModuleMap, b::TorQuadModuleElem)
                                      -> Bool, TorQuadModuleElem

Given an abelian group homomorphism $f\colon T \to S$ between two
torsion quadratic modules, and given an element `b` of `S`, return
whether `b` is in the image of `T`. If it is the case, the function
also returns a preimage of `b` by `f`. Otherwise, it returns the
identity element in `T`.
"""
function has_preimage_with_preimage(f::TorQuadModuleMap, b::TorQuadModuleElem)
  @req parent(b) === codomain(f) "b must be an element of the codomain of f"
  ok, a = has_preimage_with_preimage(f.map_ab, data(b))
  return ok, domain(f)(a)
end

@doc raw"""
    preimage(f::TorQuadModuleMap, b::TorQuadModuleElem)
                                      -> TorQuadModuleElem

Given an abelian group homomorphism `f` between two torsion quadratic
modules, and given an element `b` in the image of `f`, return a preimage
of `b` by `f`.
"""
function preimage(f::TorQuadModuleMap, a::TorQuadModuleElem)
  ok, b = has_preimage_with_preimage(f, a)
  @req ok "a is not in the image of f"
  return b
end

@doc raw"""
    is_bijective(f::TorQuadModuleMap) -> Bool

Return whether `f` is bijective.
"""
is_bijective(f::TorQuadModuleMap) = is_bijective(f.map_ab)

@doc raw"""
    is_surjective(f::TorQuadModuleMap) -> Bool

Return whether `f` is surjective.
"""
is_surjective(f::TorQuadModuleMap) = is_surjective(f.map_ab)

@doc raw"""
    is_injective(f::TorQuadModuleMap) -> Bool

Return whether `f` is injective.
"""
is_injective(f::TorQuadModuleMap) = is_injective(f.map_ab)

# Rely on the algorithm implemented for FinGenAbGroupHom
@doc raw"""
    has_complement(i::TorQuadModuleMap) -> Bool, TorQuadModuleMap

Given a map representing the injection of a submodule $W$ of a torsion
quadratic module $T$, return whether $W$ has a complement $U$ in $T$.
If yes, it returns an injection $U \to T$.

Note: if such a $U$ exists, $W$ and $U$ are in direct sum inside $T$
but they are not necessarily orthogonal to each other.
"""
function has_complement(i::TorQuadModuleMap)
  @req is_injective(i) "i must be injective"
  T = codomain(i)
  bool, jab = Hecke.has_complement(i.map_ab)
  if !bool
    return (false, sub(T, TorQuadModuleElem[])[2])
  end
  Qab = domain(jab)
  Q, j = sub(T, TorQuadModuleElem[T(jab(a)) for a in gens(Qab)])
  return (true, j)
end

@doc raw"""
    kernel(f::TorQuadModuleMap) -> TorQuadModule, TorQuadModuleMap

Given an abelian group homomorphism `f` between two torsion quadratic modules `T`
and `U`, return the kernel `S` of `f` as well as the injection $S \to T$.
"""
function kernel(f::TorQuadModuleMap)
  g = abelian_group_homomorphism(f)
  Kg, KgtoA = kernel(g)
  S, StoKg = snf(Kg)
  return sub(domain(f), TorQuadModuleElem[domain(f)(KgtoA(StoKg(a))) for a in gens(S)])
end

################################################################################
#
#  Arithmetic of maps
#
################################################################################

@doc raw"""
    +(f::TorQuadModuleMap, g::TorQuadModuleMap) -> TorQuadModuleMap

Given two abelian group homomorphisms `f` and `g` between the same torsion
quadratic modules `T` and `U`, return the pointwise sum `h` of `f` and `g`
which sends every element `a` of `T` to $h(a) := f(a) + g(a)$.
"""
function Base.:(+)(f::TorQuadModuleMap, g::TorQuadModuleMap)
  @req domain(f) === domain(g) "f and g must have the same domain"
  @req codomain(f) === codomain(g) "f and g must have the same codomain"
  hab = abelian_group_homomorphism(f) + abelian_group_homomorphism(g)
  return TorQuadModuleMap(domain(f), codomain(f), hab)
end

@doc raw"""
    -(f::TorQuadModuleMap) -> TorQuadModuleMap

Given an abelian group homomorphism `f` between two torsion quadratic modules
`T` and `U`, return the pointwise opposite morphism `h` of `f` which sends every
element `a` of `T` to $h(a) := -f(a)$.
"""
function Base.:(-)(f::TorQuadModuleMap)
  hab = -abelian_group_homomorphism(f)
  return TorQuadModuleMap(domain(f), codomain(f), hab)
end

@doc raw"""
    -(f::TorQuadModuleMap, g::TorQuadModuleMap) -> TorQuadModuleMap

Given two abelian group homomorphisms `f` and `g` between the same torsion
quadratic modules `T` and `U`, return the pointwise difference `h` of `f` and
`g` which sends every element `a` of `T` to $h(a) := f(a) - g(a)$.
"""
function Base.:(-)(f::TorQuadModuleMap, g::TorQuadModuleMap)
  @req domain(f) === domain(g) "f and g must have the same domain"
  @req codomain(f) === codomain(g) "f and g must have the same codomain"
  hab = abelian_group_homomorphism(f) - abelian_group_homomorphism(g)
  return TorQuadModuleMap(domain(f), codomain(g), hab)
end

@doc raw"""
    *(a::IntegerUnion, f::TorQuadModuleMap) -> TorQuadModuleMap
    *(f::TorQuadModuleMap, a::IntegerUnion) -> TorQuadModuleMap

Given an abelian group homomorphism `f` between two torsion quadratic modules
`T` and `U`, return the pointwise $a$-twist morphism `h` of `f` which sends every
element `b` of `T` to $h(b) := a*f(b)$.
"""
function Base.:(*)(a::IntegerUnion, f::TorQuadModuleMap)
  hab = a*abelian_group_homomorphism(f)
  return TorQuadModuleMap(domain(f), codomain(f), hab)
end

Base.:(*)(f::TorQuadModuleMap, a::IntegerUnion) = a*f

@doc raw"""
    ^(f::TorQuadModuleMap, n::Integer) -> TorQuadModuleMap

Given an abelian group endomorphism `f` of a torsion quadratic module `T`
return the $n$-fold self-composition of `f`.

Note that `n` must be non-negative and $f^0$ is by default the identity map
of the domain of `f` (see [`identity_map`](@ref)).
"""
function Base.:^(f::TorQuadModuleMap, n::Integer)
  @req n >= 0 "n must be a positive integer"
  @assert domain(f) === codomain(f) "f must be a self-map"
  hab = abelian_group_homomorphism(f)^n
  return TorQuadModuleMap(domain(f), codomain(f), hab)
end

@doc raw"""
    evaluate(p::Union{ZZPolyRingElem, QQPolyRingElem}, f::TorQuadModuleMap)
                                                          -> TorQuadModuleMap

Given an abelian group endomorphism `f` of a torsion quadratic module `T` and
an univariate polynomial `p` with integral coefficients, return the abelian
group endomorphism $h := p(f)$ of `T` obtained by substituting the variable of
`p` by `f`.

Note that one also simply call `p(f)` instead of writing `evaluate(p, f)`.
"""
function evaluate(p::ZZPolyRingElem, f::TorQuadModuleMap)
  @req domain(f) === codomain(f) "f must be a self-map"
  hab = p(abelian_group_homomorphism(f))
  return TorQuadModuleMap(domain(f), codomain(f), hab)
end

function evaluate(p::QQPolyRingElem, f::TorQuadModuleMap)
  @req domain(f) === codomain(f) "f must be a self-map"
  @req all(a -> is_integral(a), coefficients(p)) "p must have integral coefficients"
  return evaluate(map_coefficients(ZZ, p, cached = false), f)
end

(p::ZZPolyRingElem)(f::TorQuadModuleMap) = evaluate(p, f)

(p::QQPolyRingElem)(f::TorQuadModuleMap) = evaluate(p, f)

################################################################################
#
#  (Anti)-Isometry
#
################################################################################

# we test isometry in the semi-regular case: we compare the gram matrices of the
# quadratic forms associated to the respective normal forms.
function _isometry_semiregular(T::TorQuadModule, U::TorQuadModule)
  # the zero map for default output
  hz = hom(T, U, zero_matrix(ZZ, ngens(T), ngens(U)))
  NT, TtoNT = normal_form(T)
  NU, UtoNU = normal_form(U)
  gqNT = gram_matrix_quadratic(NT)
  gqNU = gram_matrix_quadratic(NU)
  if gqNT != gqNU
    return (false, hz)
  end
  NTtoNU = hom(NT, NU, identity_matrix(ZZ, ngens(NT)))
  TtoU = hom(T, U, TorQuadModuleElem[UtoNU\(NTtoNU(TtoNT(a))) for a in gens(T)])
  @hassert :Lattice 1 is_bijective(TtoU)
  @hassert :Lattice 1 all(a -> a*a == TtoU(a)*TtoU(a), gens(T))
  return (true, TtoU)
end

# we test in the degenerate case. For now, we only cover the case where both T and U
# split into a direct sum of their respective quadratic radical. If not, we return
# "Not yet implemented". If yes, we compare the normal forms of the respective complements
# which are semi-regular, and if the radicals have the same elementary divisors, we
# complete the isometry by adding the identity matrix from one radical to the other one.
function _isometry_degenerate(T::TorQuadModule, U::TorQuadModule)
  # the zero map for default output
  hz = hom(T, U, zero_matrix(ZZ, ngens(T), ngens(U)))
  rqT, rqTtoT = radical_quadratic(T)
  rqU, rqUtoU = radical_quadratic(U)
  if elementary_divisors(rqT) != elementary_divisors(rqU)
    return (false, hz)
  end
  # at this point we can map safely one radical to the other one
  boolT, jT = has_complement(rqTtoT)
  boolU, jU = has_complement(rqUtoU)
  if boolU != boolT
    return (false, hz)
  end
  if !boolT
    return _isometry_non_split_degenerate(T, U)
  end
  NT = domain(jT)
  NU = domain(jU)
  bool, isom = _isometry_semiregular(NT, NU)
  if !bool
    return (false, hz)
  end
  # now we know that there is an isometry, just need to put everything together
  # we first tidy the generators of the radicals up
  AT, ATtoab = snf(abelian_group(rqT))
  geneT = TorQuadModuleElem[rqT(a) for a in ATtoab.(gens(AT))]
  @assert sort(order.(geneT)) == sort(elementary_divisors(rqT))
  AU, AUtoab = snf(abelian_group(rqU))
  geneU = TorQuadModuleElem[rqU(a) for a in AUtoab.(gens(AU))]
  @assert sort(order.(geneU)) == sort(elementary_divisors(rqU))
  # we map generators of the radical and its complement in the module
  # to obtain an isomorphic module with a nicer basis
  geneT = rqTtoT.(geneT)
  append!(geneT, jT.(gens(NT)))
  Tsub, TsubinT = sub(T, geneT)
  @hassert :Lattice 1 is_bijective(TsubinT)  # same module, different bases, since we have a splitting
  geneU = rqUtoU.(geneU)
  append!(geneU, jU.(gens(NU)))
  Usub, UsubinU = sub(U, geneU)
  @hassert :Lattice 1 is_bijective(UsubinU)
  @assert length(geneT) == length(geneU)
  # now the radical parts are similar, the normal parts are isometric, we just
  # need to create our bijective mapping by sending generators of one radical to the
  # other and applying our previously computed isometry to the complements
  I = identity_matrix(ZZ, length(geneT)-length(gens(NT))) # for the radicals
  M = matrix(isom)                                        # for the complements
  D = block_diagonal_matrix([I, M])
  phi = hom(Tsub, Usub, D)
  @hassert :Lattice 1 is_bijective(phi)
  TtoU = hom(T, U, TorQuadModuleElem[UsubinU(phi(TsubinT\(a))) for a in gens(T)])
  @hassert :Lattice 1 all(a -> a*a == TtoU(a)*TtoU(a), gens(T))
  return (true, TtoU)
end

# This is a fallback function to cover the case where T and U are not semiregular
# and they both do not split their radical quadratic.
function _isometry_non_split_degenerate(T::TorQuadModule, U::TorQuadModule)
  Ts, TstoT = snf(T)
  n = ngens(Ts)
  u_cand = [[u for u in U if quadratic_product(u) == quadratic_product(t) && order(u) == order(t)] for t in gens(Ts)]
  waiting = Vector{TorQuadModuleElem}[[]]
  while !isempty(waiting)
    f = pop!(waiting)
    i = length(f)
    if i == n
      TstoU = hom(Ts, U, f)
      return (true, hom(T, U, TorQuadModuleElem[TstoU(TstoT\(a)) for a in gens(T)]))
    end

    t = Ts[i+1]
    card = prod([order(Ts[k]) for k in 1:(i+1)]; init = ZZ(1))
    for u in u_cand[i+1]
      if all(k -> u*f[k] == t*Ts[k], 1:i)
        fnew = copy(f)
        push!(fnew, u)
        if order(sub(U, fnew)[1]) == card
          push!(waiting, fnew)
        end
      end
    end
  end
  return (false, hom(T, U, zero_matrix(ZZ, ngens(T), ngens(U))))
end

@doc raw"""
    is_isometric_with_isometry(T::TorQuadModule, U::TorQuadModule)
                                                   -> Bool, TorQuadModuleMap

Return whether the torsion quadratic modules `T` and `U` are isometric.
If yes, it also returns an isometry $T \to U$.

If `T` and `U` are not semi-regular it requires that they both split into a direct
sum of their respective quadratic radical (see [`radical_quadratic`](@ref)).

It requires that both `T` and `U` have modulus 1: in case one of them do not,
they should be rescaled (see [`rescale`](@ref)).

# Examples

```jldoctest
julia> T = torsion_quadratic_module(QQ[2//3 2//3    0    0    0;
                                       2//3 2//3 2//3    0 2//3;
                                          0 2//3 2//3 2//3    0;
                                          0    0 2//3 2//3    0;
                                          0 2//3    0    0 2//3])
Finite quadratic module
  over integer ring
Abelian group: (Z/3)^5
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[2//3   2//3      0      0      0]
[2//3   2//3   2//3      0   2//3]
[   0   2//3   2//3   2//3      0]
[   0      0   2//3   2//3      0]
[   0   2//3      0      0   2//3]

julia> U = torsion_quadratic_module(QQ[4//3    0    0    0    0;
                                          0 4//3    0    0    0;
                                          0    0 4//3    0    0;
                                          0    0    0 4//3    0;
                                          0    0    0    0 4//3])
Finite quadratic module
  over integer ring
Abelian group: (Z/3)^5
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[4//3      0      0      0      0]
[   0   4//3      0      0      0]
[   0      0   4//3      0      0]
[   0      0      0   4//3      0]
[   0      0      0      0   4//3]

julia> bool, phi = is_isometric_with_isometry(T,U)
(true, Map: finite quadratic module -> finite quadratic module)

julia> is_bijective(phi)
true

julia> T2, _ = sub(T, [-T[4], T[2]+T[3]+T[5]])
(Finite quadratic module: (Z/3)^2 -> Q/2Z, Map: finite quadratic module -> finite quadratic module)

julia> U2, _ = sub(T, [T[4], T[2]+T[3]+T[5]])
(Finite quadratic module: (Z/3)^2 -> Q/2Z, Map: finite quadratic module -> finite quadratic module)

julia> bool, phi = is_isometric_with_isometry(U2, T2)
(true, Map: finite quadratic module -> finite quadratic module)

julia> is_bijective(phi)
true
```
"""
function is_isometric_with_isometry(T::TorQuadModule, U::TorQuadModule)
  if T === U
    return (true, id_hom(T))
  end
  # the zero map for default output
  hz = hom(T, U, zero_matrix(ZZ, ngens(T), ngens(U)))
  if order(T) != order(U)
    return (false, hz)
  end
  @req (modulus_bilinear_form(T) == 1 && modulus_bilinear_form(U) == 1) "Only implemented for torsion quadratic module with bilinear modulus 1"
  if elementary_divisors(T) != elementary_divisors(U)
    return (false, hz)
  end
  if is_semi_regular(T) != is_semi_regular(U)
    return (false, hz)
  end
  # if they have no elementary divisors, then they are trivial and therefore isometric
  if length(elementary_divisors(T)) == 0
    return (true, hz)
  end
  # they should have the same parity
  if modulus_quadratic_form(T) != modulus_quadratic_form(U)
    return (false, hz)
  end
  # the case where there is no quadratic structure
  if is_zero(gram_matrix_quadratic(T))
    is_zero(gram_matrix_quadratic(U)) || return (false, hz)
    Tabs, TabstoTab = snf(abelian_group(T))
    Uabs, UabstoUab = snf(abelian_group(U))
    fabs = hom(Tabs, Uabs, identity_matrix(ZZ, length(elementary_divisors(T))))
    fab = compose(inv(TabstoTab), compose(fabs, UabstoUab))
    return true, hom(T, U, matrix(fab))
  else
    is_zero(gram_matrix_quadratic(U)) && return (false, hz)
  end
  if is_semi_regular(T)
    return _isometry_semiregular(T, U)
  else
    return _isometry_degenerate(T, U)
  end
end

@doc raw"""
    is_anti_isometric_with_anti_isometry(T::TorQuadModule, U::TorQuadModule)
                                                     -> Bool, TorQuadModuleMap

Return whether there exists an anti-isometry between the torsion quadratic
modules `T` and `U`. If yes, it returns such an anti-isometry $T \to U$.

If `T` and `U` are not semi-regular it requires that they both split into a direct
sum of their respective quadratic radical (see [`radical_quadratic`](@ref)).

It requires that both `T` and `U` have modulus 1: in case one of them do not,
they should be rescaled (see [`rescale`](@ref)).

# Examples

```jldoctest
julia> T = torsion_quadratic_module(QQ[4//5;])
Finite quadratic module
  over integer ring
Abelian group: Z/5
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[4//5]

julia> bool, phi = is_anti_isometric_with_anti_isometry(T, T)
(true, Map: finite quadratic module -> finite quadratic module)

julia> a = gens(T)[1];

julia> a*a == -phi(a)*phi(a)
true

julia> G = matrix(FlintQQ, 6, 6 , [3 3 0 0 0  0;
                                   3 3 3 0 3  0;
                                   0 3 3 3 0  0;
                                   0 0 3 3 0  0;
                                   0 3 0 0 3  0;
                                   0 0 0 0 0 10]);

julia> V = quadratic_space(QQ, G);

julia> B = matrix(QQ, 6, 6 , [1    0    0    0    0    0;
                              0 1//3 1//3 2//3 1//3    0;
                              0    0    1    0    0    0;
                              0    0    0    1    0    0;
                              0    0    0    0    1    0;
                              0    0    0    0    0 1//5]);


julia> M = lattice(V, B);

julia> B2 = matrix(FlintQQ, 6, 6 , [ 1  0 -1  1  0 0;
                                     0  0  1 -1  0 0;
                                    -1  1  1 -1 -1 0;
                                     1 -1 -1  2  1 0;
                                     0  0 -1  1  1 0;
                                     0  0  0  0  0 1]);

julia> N = lattice(V, B2);

julia> T = torsion_quadratic_module(M, N)
Finite quadratic module
  over integer ring
Abelian group: Z/15
Bilinear value module: Q/Z
Quadratic value module: Q/Z
Gram matrix quadratic form:
[3//5]

julia> bool, phi = is_anti_isometric_with_anti_isometry(T,T)
(true, Map: finite quadratic module -> finite quadratic module)

julia> a = gens(T)[1];

julia> a*a == -phi(a)*phi(a)
true
```
"""
function is_anti_isometric_with_anti_isometry(T::TorQuadModule, U::TorQuadModule)
  # the zero map for default output
  hz = hom(T, U, zero_matrix(ZZ, ngens(T), ngens(U)))
  if order(T) != order(U)
    return (false, hz)
  end
  @req (modulus_bilinear_form(T) == 1 && modulus_bilinear_form(U) == 1) "Only implemented for torsion quadratic module with bilinear modulus 1"
  if elementary_divisors(T) != elementary_divisors(U)
    return (false, hz)
  end
  if is_semi_regular(T) != is_semi_regular(U)
    return (false, hz)
  end
  # if they have no elementary divisors, then they are trivial and therefore isometric
  if length(elementary_divisors(T)) == 0
    return (true, hz)
  end
  # they should have the same parity
  if modulus_quadratic_form(T) != modulus_quadratic_form(U)
    return (false, hz)
  end
  # the case where there is no quadratic structure
  if is_zero(gram_matrix_quadratic(T))
    is_zero(gram_matrix_quadratic(U)) || return (false, hz)
    Tabs, TabstoTab = snf(abelian_group(T))
    Uabs, UabstoUab = snf(abelian_group(U))
    fabs = hom(Tabs, Uabs, identity_matrix(ZZ, length(elementary_divisors(T))))
    fab = compose(inv(TabstoTab), compose(fabs, UabstoUab))
    return true, hom(T, U, matrix(fab))
  else
    is_zero(gram_matrix_quadratic(U)) && return (false, hz)
  end

  Ue = rescale(U, -1)
  UetoU = hom(Ue, U, U.(lift.(gens(Ue))))
  if is_semi_regular(T)
    bool, TtoUe = _isometry_semiregular(T, Ue)
  else
    bool, TtoUe = _isometry_degenerate(T, Ue)
  end
  TtoU = compose(TtoUe, UetoU)
  if bool
    @hassert :Lattice 1 all(a -> a*a == -TtoU(a)*TtoU(a), gens(T))
  end
  return (bool, TtoU)
end

################################################################################
#
#  Submodules
#
################################################################################

@doc raw"""
    sub(T::TorQuadModule, generators::Vector{TorQuadModuleElem})
                                                    -> TorQuadModule, TorQuadModuleMap

Return the submodule of `T` defined by `generators` and the inclusion morphism.
"""
function sub(T::TorQuadModule, gens::Vector{TorQuadModuleElem})
  @req all(parent(x)===T for x in gens) "generators must lie in T"
  if length(gens) > 0
    _gens = Vector{QQFieldElem}[lift(g) for g in gens]
    V = ambient_space(T.cover)
    _gens_mat = matrix(QQ, _gens)
    gens_new = [basis_matrix(T.rels); _gens_mat]::QQMatrix
    cover = lattice(V, gens_new; isbasis = false)
  else
    cover = T.rels
    _gens = nothing
  end
  S = torsion_quadratic_module(cover, T.rels; gens=_gens, modulus=modulus_bilinear_form(T),
                               modulus_qf=modulus_quadratic_form(T))
  imgs = TorQuadModuleElem[T(lift(g)) for g in Hecke.gens(S)]
  inclusion = hom(S, T, imgs)
  return S, inclusion
end

@doc raw"""
    torsion_quadratic_module(q::QQMatrix) -> TorQuadModule

Return a torsion quadratic module with gram matrix given by `q` and
value module `Q/Z`.
If all the diagonal entries of `q` have: either even numerator or
even denominator, then the value module of the quadratic form is `Q/2Z`

# Example
```jldoctest
julia> torsion_quadratic_module(QQ[1//6;])
Finite quadratic module
  over integer ring
Abelian group: Z/6
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[1//6]

julia> torsion_quadratic_module(QQ[1//2;])
Finite quadratic module
  over integer ring
Abelian group: Z/2
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[1//2]

julia> torsion_quadratic_module(QQ[3//2;])
Finite quadratic module
  over integer ring
Abelian group: Z/2
Bilinear value module: Q/Z
Quadratic value module: Q/2Z
Gram matrix quadratic form:
[3//2]

julia> torsion_quadratic_module(QQ[1//3;])
Finite quadratic module
  over integer ring
Abelian group: Z/3
Bilinear value module: Q/Z
Quadratic value module: Q/Z
Gram matrix quadratic form:
[1//3]
```
"""
function torsion_quadratic_module(q::QQMatrix)
  @req is_square(q) "Matrix must be a square matrix"
  @req is_symmetric(q) "Matrix must be symmetric"

  d = denominator(q)
  Q = change_base_ring(FlintZZ, d * q)
  S, U, V = snf_with_transform(Q)
  D = change_base_ring(FlintQQ, U) * q * change_base_ring(FlintQQ, V)
  L = integer_lattice(1//d * identity_matrix(QQ, nrows(q)); gram = d^2 * q)
  denoms = QQFieldElem[denominator(D[i, i]) for i in 1:ncols(D)]
  rels = diagonal_matrix(denoms) * U
  LL = lattice(ambient_space(L), 1//d * change_base_ring(QQ, rels))
  return torsion_quadratic_module(L, LL; modulus = QQFieldElem(1))
end

TorQuadModule(q::QQMatrix) = torsion_quadratic_module(q)

@doc raw"""
    primary_part(T::TorQuadModule, m::ZZRingElem)-> Tuple{TorQuadModule, TorQuadModuleMap}

Return the primary part of `T` as a submodule.
"""
function primary_part(T::TorQuadModule, m::ZZRingElem)
  S, i = primary_part(T.ab_grp, m, false)
  submod = sub(T, TorQuadModuleElem[T(i(s)) for s in gens(S)])
  return submod
end

primary_part(T::TorQuadModule,m::Int) = primary_part(T,ZZ(m))

@doc raw"""
    orthogonal_submodule(T::TorQuadModule, S::TorQuadModule)-> TorQuadModule

Return the orthogonal submodule to the submodule `S` of `T`.
"""
function orthogonal_submodule(T::TorQuadModule, S::TorQuadModule)
  @assert is_sublattice(cover(T), cover(S)) "The second argument is not a submodule of the first argument"
  V = ambient_space(cover(T))
  G = gram_matrix(V)
  B = basis_matrix(cover(T))
  C = basis_matrix(cover(S))
  m = modulus_bilinear_form(T)
  Y = B * G * transpose(C)
  # Elements of the ambient module which pair integrally with cover(T)
  integral = inv(Y) * B
  # Element of the ambient module which pair in mZZ with cover(T)
  orthogonal =  m * integral
  # We have to make sure we get a submodule
  ortho = intersect(lattice(V, B), lattice(V, orthogonal))
  Borth = basis_matrix(ortho)
  gens_orth = [T(vec(collect(Borth[i:i,:]))) for i in 1:nrows(Borth)]
  filter!(!iszero, gens_orth)
  return sub(T, gens_orth)
end

@doc raw"""
    is_degenerate(T::TorQuadModule) -> Bool

Return true if the underlying bilinear form is degenerate.
"""
function is_degenerate(T::TorQuadModule)
  return get_attribute!(T,:is_degenerate) do
    return order(orthogonal_submodule(T,T)[1]) != 1
  end
end

@doc raw"""
    is_semi_regular(T::TorQuadModule) -> Bool

Return whether `T` is semi-regular, that is its quadratic radical is trivial
(see [`radical_quadratic`](@ref)).
"""
is_semi_regular(T::TorQuadModule) = is_trivial(abelian_group(radical_quadratic(T)[1]))

@doc raw"""
    radical_bilinear(T::TorQuadModule) -> TorQuadModule, TorQuadModuleMap

Return the radical `\{x \in T | b(x,T) = 0\}` of the bilinear form `b` on `T`.
"""
function radical_bilinear(T::TorQuadModule)
  return orthogonal_submodule(T,T)
end

@doc raw"""
    radical_quadratic(T::TorQuadModule) -> TorQuadModule, TorQuadModuleMap

Return the radical `\{x \in T | b(x,T) = 0 and q(x)=0\}` of the quadratic form
`q` on `T`.
"""
function radical_quadratic(T::TorQuadModule)
  Kb, ib = radical_bilinear(T)
  G = gram_matrix_quadratic(Kb)*1//modulus_bilinear_form(Kb)
  F = Native.GF(2; cached=false)
  G2 = matrix(F, nrows(G), 1, F.(diagonal(G)))
  kermat = kernel(G2, side = :left)
  kermat = lift(kermat)
  g = gens(Kb)
  n = length(g)
  kergen = TorQuadModuleElem[sum(kermat[i,j]*g[j] for j in 1:n) for i in 1:nrows(kermat)]
  Kq, iq = sub(Kb,kergen)
  @assert iszero(gram_matrix_quadratic(Kq))
  return Kq, compose(iq,ib)
end

@doc raw"""
    rescale(T::TorQuadModule, k::RingElement) -> TorQuadModule

Return the torsion quadratic module with quadratic form scaled by ``k``,
where k is a non-zero rational number.
If the old form was defined modulo `n`, then the new form is defined
modulo `n k`.
"""
function rescale(T::TorQuadModule, k::RingElement)
  @req !iszero(k) "Parameter ($k) must be non-zero"
  C = cover(T)
  V = rescale(ambient_space(C), k)
  M = lattice(V, basis_matrix(C))
  N = lattice(V, basis_matrix(T.rels))
  gene = ngens(T) == 0 ? nothing : lift.(gens(T))
  return torsion_quadratic_module(M, N; gens = gene,
                                        modulus = abs(k)*modulus_bilinear_form(T),
                                        modulus_qf = abs(k)*modulus_quadratic_form(T))
end

@doc raw"""
    normal_form(T::TorQuadModule; partial=false) -> TorQuadModule, TorQuadModuleMap

Return the normal form `N` of the given torsion quadratic module `T` along
with the projection `T -> N`.

Let `K` be the radical of the quadratic form of `T`. Then `N = T/K` is
half-regular. Two half-regular torsion quadratic modules are isometric
if and only if they have equal normal forms.
"""
function normal_form(T::TorQuadModule; partial=false)
  if T.is_normal
    return T, id_hom(T)
  end
  if is_degenerate(T)
    K, _ = radical_quadratic(T)
    N = torsion_quadratic_module(cover(T), cover(K); modulus=modulus_bilinear_form(T), modulus_qf=modulus_quadratic_form(T))
    i = hom(T, N, TorQuadModuleElem[N(lift(g)) for g in gens(T)])
  else
    N = T
    i = identity_map(T)
  end
  normal_gens = TorQuadModuleElem[]
  prime_div = prime_divisors(exponent(N))
  for p in prime_div
    D_p, I_p = primary_part(N, p)
    q_p = gram_matrix_quadratic(D_p)
    if p == 2
        q_p = q_p * modulus_quadratic_form(D_p)^-1
    else
        q_p = q_p * modulus_bilinear_form(D_p)^-1
    end

    # the normal form is implemented for p-adic lattices
    # so we should work with the lattice q_p --> q_p^-1
    q_p1 = inv(q_p)
    prec = 2*valuation(exponent(T), p) + 5
    D, U = padic_normal_form(q_p1, p; prec, partial)
    R = residue_ring(ZZ, ZZ(p)^prec)[1]
    UR = map_entries(x->R(ZZ(x)), U)
    UR = transpose(inv(UR))

    # the inverse is in normal form - so to get a normal form for
    # the original one
    # it is enough to massage each 1x1 resp. 2x2 block.
    denom = denominator(q_p)
    q_pR = map_entries(x->R(ZZ(x)), denom*q_p)
    D = UR * q_pR * transpose(UR)
    D = map_entries(x->R(mod(lift(x),denom)), D)
    if p != 2
       # follow the conventions of Miranda-Morrison
       m = ZZ(modulus_quadratic_form(D_p)//modulus_bilinear_form(D_p))
       D = R(m)^-1*D
    end

    D1, U1 = _normalize(D, ZZ(p), false)
    UR = U1 * UR
    #apply U to the generators
    n1 = ncols(UR)
    Gp =  gens(D_p);
    for i in 1:nrows(UR)
      g = sum(lift(UR[i,j]) * Gp[j] for j in 1:ncols(UR))
      push!(normal_gens, I_p(g))
    end
  end

  S, j =  sub(N, normal_gens)
  J = compose(i,inv(j))
  if !partial
    S.is_normal = true
  end
  return S, J
end

@doc raw"""
    _brown_indecomposable(q::MatElem, p::ZZRingElem) ->  ZZRingElem
Return the Brown invariant of the indecomposable form ``q``.

The values are taken from Table 2.1 in [Shim2016]_.
INPUT:
- ``q`` - an indecomposable quadratic form represented by a
  rational `1 \times 1` or `2 \times 2` matrix
- ``p`` - a prime number
EXAMPLES::

  julia> q = matrix(QQ, 1, 1, [1//3])
  julia> _brown_indecomposable(q,ZZRingElem(3))
  6
  julia> q = matrix(QQ, 1, 1, [2//3])
  julia> _brown_indecomposable(q,ZZRingElem(3))
  2
"""
function _brown_indecomposable(q::MatElem, p::ZZRingElem)
  v = valuation(denominator(q), p)
  if p == 2
    # brown(U) = 0
    if ncols(q) == 2
      if iszero(q[1,1]) || iszero(q[2,2]) || (valuation(q[1,1],2) > v + 1 && valuation(q[2, 2],2) > v + 1)
        # type U
        return mod(0, 8)
      else
        # type V
        return mod(4*v, 8)
      end
    end
    u = numerator(q[1, 1])
    return mod(u + divexact(v*(u^2 - 1), 2), 8)
  end
  if p % 4 == 1
    e = -1
  end
  if p % 4 == 3
    e = 1
  end
  if v % 2 == 1
    u = div(numerator(q[1, 1]), 2)
    if jacobi_symbol(u, p) == 1
      return mod(1 + e, 8)
    else
      return mod(-3 + e, 8)
    end
  end
  return mod(0, 8)
end

@doc raw"""
    brown_invariant(self::TorQuadModule) -> Nemo.zzModRingElem
Return the Brown invariant of this torsion quadratic form.

Let `(D,q)` be a torsion quadratic module with values in `Q / 2Z`.
The Brown invariant `Br(D,q) in Z/8Z` is defined by the equation

$$\exp \left( \frac{2 \pi i }{8} Br(q)\right) =
  \frac{1}{\sqrt{D}} \sum_{x \in D} \exp(i \pi q(x)).$$

The Brown invariant is additive with respect to direct sums of
torsion quadratic modules.

# Examples
```jldoctest
julia> L = integer_lattice(gram=matrix(ZZ, [[2,-1,0,0],[-1,2,-1,-1],[0,-1,2,0],[0,-1,0,2]]));

julia> T = Hecke.discriminant_group(L);

julia> brown_invariant(T)
4
```
"""
function brown_invariant(T::TorQuadModule)
  @req modulus_quadratic_form(T) == 2 "the torsion quadratic form must have values in Q/2Z"
  @req !is_degenerate(T) "the torsion quadratic form must be non-degenerate"
  brown = residue_ring(ZZ, 8)[1](0)
  for p in prime_divisors(exponent(T))
    q = normal_form(primary_part(T, p)[1])[1]
    q = gram_matrix_quadratic(q)
    L = collect_small_blocks(q)
    for qi in L
      brown += _brown_indecomposable(qi, p)
    end
  end
  return brown
end

function _as_finite_bilinear_module(T::TorQuadModule)
  n = modulus_bilinear_form(T)
  if n == modulus_quadratic_form(T)
    return T
  end
  return torsion_quadratic_module(cover(T), relations(T); modulus = n, modulus_qf = n)
end

@doc raw"""
    genus(T::TorQuadModule, signature_pair::Tuple{Int, Int};
                            parity::RationalUnion = modulus_quadratic_form(T))
                                                                    -> ZZGenus

Return the genus of an integer lattice whose discriminant group has the bilinear
form of `T`, the given `signature_pair` and the given `parity`.

The argument `parity` is one of the following: either `parity == 1` for genera
of odd lattices, or `parity == 2` for even lattices. By default, `parity` is
set to be as the parity of the quadratic form on `T`

If no such genus exists, raise an error.

# Reference
[Nik79](@cite) Corollary 1.9.4 and 1.16.3.
"""
function genus(T::TorQuadModule, signature_pair::Tuple{Int, Int}; parity::RationalUnion = modulus_quadratic_form(T))
  @req modulus_bilinear_form(T) == 1 "Modulus for the bilinear form must be 1"
  @req modulus_quadratic_form(T) == 1 || modulus_quadratic_form(T) == 2 "Modulus for the quadratic form must be 1 or 2"
  @req parity == 1 || parity == 2 "Parity must be 1 or 2"
  s_plus = signature_pair[1]
  s_minus = signature_pair[2]
  rank = s_plus + s_minus
  if s_plus < 0 || s_minus < 0
    error("signatures must be non-negative")
  end
  if length(elementary_divisors(T)) > rank
    error("this discriminant form and signature do not define a genus")
  end
  if rank == 0 && order(T) == 1
    return genus(zero_matrix(ZZ,0,0))
  end
  disc = order(T)
  determinant = ZZ(-1)^s_minus * disc
  local_symbols = ZZLocalGenus[]
  P = prime_divisors(2 * disc)
  sort!(P) # expects primes in ascending order
  for p in P
    D, _ = primary_part(T, p)
    if length(elementary_divisors(D)) != 0
      G_p = inv(gram_matrix_quadratic(D))
      dp = denominator(G_p)^2
      # get rid of denominators without changing the local equivalence class
      map_entries!(x -> x*dp, G_p, G_p)
      G_pZZ = change_base_ring(ZZ, G_p)
      genus_p = genus(G_pZZ, p, valuation(elementary_divisors(D)[end], p))
    else
      genus_p = ZZLocalGenus(p, Vector{Int}[])
    end
    rk = rank - length(elementary_divisors(D))
    if rk > 0
      if p == 2
        det = remove(determinant, 2)[2]
        mul!(det, det, prod(di[3] for di in genus_p._symbol; init = ZZ(1)))
        mod!(det, det, ZZ(8))
        push!(genus_p._symbol, Int[0, rk, det, 0, 0])
      else
        det = ZZ(jacobi_symbol(remove(determinant, p)[2], p))
        mul!(det, det, prod(di[3] for di in genus_p._symbol; init = ZZ(1)))
        push!(genus_p._symbol, Int[0, rk, det])
      end
    end
    sort!(genus_p._symbol)
    push!(local_symbols, genus_p)
  end
  # This genus has the right discriminant group
  # but it may be empty
  #
  # make sure the first 3 symbols are of scales 1, 2, 4
  # i.e. their valuations are 0, 1, 2

  sym2 = local_symbols[1]._symbol
  if sym2[1][1] != 0
    sym2 = pushfirst!(sym2, Int[0, 0, 1, 0, 0])
  end
  if length(sym2) <= 1 || sym2[2][1] != 1
    sym2 = insert!(sym2, 2, Int[1, 0, 1, 0, 0])
  end
  if length(sym2) <= 2 || sym2[3][1] != 2
    sym2 = insert!(sym2, 3, Int[2, 0, 1, 0, 0])
  end
  if modulus_quadratic_form(T) == 1 || parity == 1
    # in this case the blocks of scales 1, 2, 4 are under determined

    _o = mod(parity, 2)
    # the form is of parity `parity`
    block0 = [b for b in _blocks(sym2[1]) if b[4] == _o]

    o = sym2[2][4]::Int
    # no restrictions on determinant and
    # oddity beyond existence
    # but we know if even or odd
    block1 = [b for b in _blocks(sym2[2]) if b[4] == o]

    d = sym2[3][3]::Int
    o = sym2[3][4]::Int
    t = sym2[3][5]::Int
    # if the jordan block of scale 2 is even we know it
    if o == 0
      block2 = [sym2[3]]
      # if it is odd we know det and oddity mod 4 at least
    else
      block2 = [b for b in _blocks(sym2[3]) if b[4] == o
        && mod(b[3] - d, 4) == 0
        && mod(b[5] - t, 4) == 0
        && mod(b[3] - d, 8) == mod(b[5] - t, 8)  # if the oddity is altered by 4 then so is the determinant
        ]
    end
  else
    if modulus_quadratic_form(T) == 2
      # the form is even
      block0 = [b for b in _blocks(sym2[1]) if b[4] == 0]

      # if the jordan block of scale 2 is even we know it
      d = sym2[2][3]::Int
      o = sym2[2][4]::Int
      t = sym2[2][5]::Int
      if o == 0
        block1 = [sym2[2]]
      else
        # the block is odd and we know det and oddity mod 4
        block1 = [b for b in _blocks(sym2[2])
                if b[4] == o
                && mod(b[3] - d, 4) == 0
                && mod(b[5] - t, 4) == 0
                && mod(b[3] - d, 8) == mod(b[5] - t, 8) # if the oddity is altered by 4 then so is the determinant
                ]
      end
      # this is completely determined
      block2 = [sym2[3]]
    else
      error("this is not a discriminant form of a ZLattice")
    end
  end
  # figure out which symbol defines a genus and return that
  for b0 in block0
    for b1 in block1
      for b2 in block2
        sym2[1:3] = [b0, b1, b2]
        local_symbols[1] = ZZLocalGenus(2, copy(sym2))
        genus = ZZGenus(signature_pair, local_symbols)
        if _isglobal_genus(genus)
          return genus
        end
      end
    end
  end
  error("this discriminant form and signature do not define a genus")
end

@doc raw"""
    is_genus(T::TorQuadModule, signature_pair::Tuple{Int, Int};
                               parity::RationalUnion = modulus_quadratic_form(T)) -> Bool

Return if there is an integral lattice whose discriminant form has the bilinear
form of `T`, whose signatures match `signature_pair` and which is of parity
`parity`.

The argument `parity` is one of the following: either `parity == 1` for genera
of odd lattices, or `parity == 2` for even lattices. By default, `parity` is
set to be as the parity of the quadratic form on `T`
"""
function is_genus(T::TorQuadModule, signature_pair::Tuple{Int, Int}; parity::RationalUnion = modulus_quadratic_form(T))
  try
    genus(T, signature_pair; parity)
    return true
  catch
    return false
  end
end

function _is_genus_brown(T::TorQuadModule, signature_pair::Tuple{Int, Int})
  s_plus = signature_pair[1]
  s_minus = signature_pair[2]
  even = modulus_quadratic_form(T) == 2
  @req even || modulus_quadratic_form(T) == 1 "the discriminant form must be defined modulo Z or 2Z"
  if s_plus < 0 || s_minus < 0
    error("signature invariants must be non negative")
  end
  rank = s_plus + s_minus
  signature = s_plus - s_minus
  D = order(T)
  det = (-1)^s_minus * D
  if rank < length(elementary_divisors(T))
    return false
  end
  if !even
    try
      genus(T, signature_pair)
      return true
    catch
      return false
    end
  end
  for p in prime_divisors(D)
    # check the determinant conditions
    Q_p = primary_part(T, p)[1]
    gram_p = gram_matrix_quadratic(Q_p)
    length_p = length(elementary_divisors(Q_p))
    u = remove(det, p)[2]
    up = remove(numerator(Hecke.det(gram_p)), p)[2]
    if p != 2 && length_p == rank
      if jacobi_symbol(u, p) != jacobi_symbol(up, p)
        return false
      end
    end
    if p == 2
      if mod(rank, 2) != mod(length_p, 2)
        return false
      end
      n = (rank - length_p) // 2
      if mod(u, 4) != mod((-1)^(mod(n, 2)) * up, 4)
        return false
      end
      if rank == length_p
        a = QQ(1, 2)
        b = QQ(3, 2)
        diag = diagonal(gram_p)
        if  !((a in diag) || (b in diag))
          if mod(u, 8) != mod(up, 8)
            return false
          end
        end
      end
    end
  end
  if brown_invariant(T) != signature
    return false
  end
  return true
end

###############################################################################
#
#  Sums
#
###############################################################################

@doc raw"""
    +(T::TorQuadModule, U::TorQuadModule) -> TorQuadModule

Given two torsion quadratic modules `T` and `U` whose covers are in the same
ambient space, return their sum `S` defined as the quotient of the sum of their
covers by the sum of their respective relation lattices.

Note that `T` and `U` must have the same moduli, both bilinear and quadratic
ones.
"""
function +(T::TorQuadModule, U::TorQuadModule)
  @req modulus_bilinear_form(T) == modulus_bilinear_form(U) "T and U must have the same bilinear modulus"
  @req modulus_quadratic_form(T) == modulus_quadratic_form(U) "T and U must have the same quadratic modulus"
  @req ambient_space(cover(T)) === ambient_space(cover(U)) "Covers must be in the same ambient space"
  cS = cover(T) + cover(U)
  rS = relations(T) + relations(U)
  geneT = [lift(a) for a in gens(T)]
  geneU = [lift(b) for b in gens(U)]
  S = torsion_quadratic_module(cS, rS; gens = filter!(!iszero, union!(geneT, geneU)), modulus = modulus_bilinear_form(T), modulus_qf = modulus_quadratic_form(T))
  return S
end

function _biproduct(x::Vector{TorQuadModule}; proj = true)
  mbf = modulus_bilinear_form(x[1])
  mqf = modulus_quadratic_form(x[1])
  @req all(q -> modulus_bilinear_form(q) == mbf, x) "All torsion quadratic modules must have the same bilinear modulus"
  @req all(q -> modulus_quadratic_form(q) == mqf, x) "All torsion quadratic modules must have the same quadratic modulus"
  cs = cover.(x)
  rs = relations.(x)
  C, injC, projC = biproduct(cs)
  R = lattice(ambient_space(C), block_diagonal_matrix(basis_matrix.(rs)))
  gensinj = Vector{Vector{QQFieldElem}}[]
  gensproj = Vector{Vector{QQFieldElem}}[]
  inj2 = TorQuadModuleMap[]
  proj2 = TorQuadModuleMap[]
  for i in 1:length(x)
    gene = [injC[i](lift(a)) for a in gens(x[i])]
    push!(gensinj, gene)
  end
  S = torsion_quadratic_module(C, R; gens = reduce(vcat, gensinj), modulus = mbf, modulus_qf = mqf)
  for i in 1:length(x)
    T = x[i]
    iT = hom(T, S, S.(gensinj[i]))
    push!(inj2, iT)
  end
  if proj
    for i in 1:length(x)
      gene = [projC[i](lift(a)) for a in gens(S)]
      push!(gensproj, gene)
    end
    for i in 1:length(x)
      T = x[i]
      pT = hom(S, T, T.(gensproj[i]))
      push!(proj2, pT)
    end
  end
  return S, inj2, proj2
end

@doc raw"""
    direct_sum(x::Vararg{TorQuadModule}) -> TorQuadModule, Vector{TorQuadModuleMap}
    direct_sum(x::Vector{TorQuadModule}) -> TorQuadModule, Vector{TorQuadModuleMap}

Given a collection of torsion quadratic modules $T_1, \ldots, T_n$, return
their direct sum $T := T_1\oplus \ldots \oplus T_n$, together with the
injections $T_i \to T$.

For objects of type `TorQuadModule`, finite direct sums and finite direct products
agree and they are therefore called biproducts.
If one wants to obtain `T` as a direct product with the projections $T \to T_i$,
one should call `direct_product(x)`.
If one wants to obtain `T` as a biproduct with the injections $T_i \to T$ and the
projections $T \to T_i$, one should call `biproduct(x)`.
"""
function direct_sum(x::Vector{TorQuadModule})
  T, inj, = _biproduct(x, proj=false)
  return T, inj
end

direct_sum(x::Vararg{TorQuadModule}) = direct_sum(collect(x))

@doc raw"""
    direct_product(x::Vararg{TorQuadModule}) -> TorQuadModule, Vector{TorQuadModuleMap}
    direct_product(x::Vector{TorQuadModule}) -> TorQuadModule, Vector{TorQuadModuleMap}

Given a collection of torsion quadratic modules $T_1, \ldots, T_n$, return
their direct product $T := T_1\times \ldots \times T_n$, together with the
projections $T \to T_i$.

For objects of type `TorQuadModule`, finite direct sums and finite direct products
agree and they are therefore called biproducts.
If one wants to obtain `T` as a direct sum with the inctions $T_i \to T$,
one should call `direct_sum(x)`.
If one wants to obtain `T` as a biproduct with the injections $T_i \to T$ and the
projections $T \to T_i$, one should call `biproduct(x)`.
"""
function direct_product(x::Vector{TorQuadModule})
  T, _, proj = _biproduct(x)
  return T, proj
end

direct_product(x::Vararg{TorQuadModule}) = direct_product(collect(x))

@doc raw"""
    biproduct(x::Vararg{TorQuadModule}) -> TorQuadModule, Vector{TorQuadModuleMap}, Vector{TorQuadModuleMap}
    biproduct(x::Vector{TorQuadModule}) -> TorQuadModule, Vector{TorQuadModuleMap}, Vector{TorQuadModuleMap}

Given a collection of torsion quadratic modules $T_1, \ldots, T_n$, return
their biproduct $T := T_1\oplus \ldots \oplus T_n$, together with the
injections $T_i \to T$ and the projections $T \to T_i$.

For objects of type `TorQuadModule`, finite direct sums and finite direct products
agree and they are therefore called biproducts.
If one wants to obtain `T` as a direct sum with the inctions $T_i \to T$,
one should call `direct_sum(x)`.
If one wants to obtain `T` as a direct product with the projections $T \to T_i$,
one should call `direct_product(x)`.
"""
function biproduct(x::Vector{TorQuadModule})
  return _biproduct(x)
end

biproduct(x::Vararg{TorQuadModule}) = biproduct(collect(x))

###############################################################################
#
#  Primary/elementary torsion quadratic module
#
###############################################################################

@doc raw"""
    is_primary_with_prime(T::TorQuadModule) -> Bool, ZZRingElem

Given a torsion quadratic module `T`, return whether the underlying (finite)
abelian group of `T` (see [`abelian_group`](@ref)) is a `p`-group for some prime
number `p`. In case it is, `p` is also returned as second output.

Note that in the case of trivial groups, this function returns `(true, 1)`. If
`T` is not primary, the second return value is `-1` by default.
"""
function is_primary_with_prime(T::TorQuadModule)
  ed = elementary_divisors(T)
  if is_empty(ed)
    return true, ZZ(1)
  end
  bool, _, p = is_prime_power_with_data(elementary_divisors(T)[end])
  bool || return false, ZZ(-1)
  return bool, p
end

@doc raw"""
    is_primary(T::TorQuadModule, p::Union{Integer, ZZRingElem}) -> Bool

Given a torsion quadratic module `T` and a prime number `p`, return whether
the underlying (finite) abelian group of `T` (see [`abelian_group`](@ref)) is
a `p`-group.
"""
function is_primary(T::TorQuadModule, p::Union{Integer, ZZRingElem})
  bool, q = is_primary_with_prime(T)
  return bool && q == p
end

@doc raw"""
    is_elementary_with_prime(T::TorQuadModule) -> Bool, ZZRingElem

Given a torsion quadratic module `T`, return whether the underlying (finite)
abelian group of `T` (see [`abelian_group`](@ref)) is an elementary `p`-group,
for some prime number `p`. In case it is, `p` is also returned as second output.

Note that in the case of trivial groups, this function returns `(true, 1)`. If
`T` is not elementary, the second return value is `-1` by default.
"""
function is_elementary_with_prime(T::TorQuadModule)
  bool, p = is_primary_with_prime(T)
  bool && p != 1 || return bool, p
  if p != elementary_divisors(T)[end]
    return false, ZZ(-1)
  end
  return bool, p
end

@doc raw"""
    is_elementary(T::TorQuadModule, p::Union{Integer, ZZRingElem}) -> Bool

Given a torsion quadratic module `T` and a prime number `p`, return whether the
underlying (finite) abelian group of `T` (see [`abelian_group`](@ref)) is an
elementary `p`-group.
"""
function is_elementary(T::TorQuadModule, p::Union{Integer, ZZRingElem})
  bool, q = is_elementary_with_prime(T)
  return bool && q == p
end

###############################################################################
#
#  Smith normal form
#
###############################################################################

@doc raw"""
    snf(T::TorQuadModule) -> TorQuadModule, TorQuadModuleMap

Given a torsion quadratic module `T`, return a torsion quadratic module `S`,
isometric to `T`, such that the underlying abelian group of `S` is in canonical
Smith normal form. It comes with an isometry $f : S \to T$.
"""
function snf(T::TorQuadModule)
  A = abelian_group(T)
  if is_snf(A)
    return T, id_hom(T)
  end
  G, f = snf(A)
  S, f = sub(T, [T(f(g)) for g in gens(G)])
  @assert is_bijective(f)
  return (S, f)::Tuple{TorQuadModule, TorQuadModuleMap}
end

@doc raw"""
    is_snf(T::TorQuadModule) -> Bool

Given a torsion quadratic module `T`, return whether its
underlying abelian group is in Smith normal form.
"""
is_snf(T::TorQuadModule) = is_snf(abelian_group(T))

################################################################################
#
#  Isotropic check
#
################################################################################

@doc raw"""
    is_totally_isotropic(T::TorQuadModule)

Return whether the quadratic form on the torsion quadratic module `T` vanishes.
"""
function is_totally_isotropic(T::TorQuadModule)
  n = ngens(T)
  for i in 1:n
    a = gen(T, i)
    if !is_zero(quadratic_product(a))
      return false
    end
    for j in (i + 1):n
      b = gen(T, j)
      k = inner_product(ambient_space(cover(T)), lift(a), lift(b))
      if !is_zero(value_module_quadratic_form(T)(2*k))
        return false
      end
    end
  end
  return true
end

################################################################################
#
#  Isometry/Anti-isometry check
#
################################################################################

function _is_isometry_epsilon(f::TorQuadModuleMap, epsilon)
  !is_bijective(f) && return false
  T = domain(f)
  k = ngens(T)
  for i in 1:k
    a = gen(T, i)
    for j in i:k
      b = gen(T, j)
      if f(a)*f(b) != epsilon * a * b
        return false
      end
    end
    if quadratic_product(a) != epsilon * quadratic_product(f(a))
      return false
    end
  end
  return true
end

function is_isometry(f::TorQuadModuleMap)
  return _is_isometry_epsilon(f, 1)
end

function is_anti_isometry(f::TorQuadModuleMap)
  return _is_isometry_epsilon(f, -1)
end

################################################################################
#
#  Submodules
#
################################################################################

@doc raw"""
    submodules(T::TorQuadModule; kw...)

Return the submodules of `T` as an iterator. Possible keyword arguments to
restrict the submodules:
- `order::Int`: only submodules of order `order`,
- `index::Int`: only submodules of index `index`,
- `subtype::Vector{Int}`: only submodules which are isomorphic as an abelian
  group to `abelian_group(subtype)`,
- `quotype::Vector{Int}`: only submodules whose quotient are isomorphic as an
  abelian to `abelian_group(quotype)`.
"""
function submodules(T::TorQuadModule; kw...)
  A = abelian_group(T)
  return (sub(T, T.(StoA.(gens(S)))) for (S, StoA) in subgroups(A; kw..., fun = (x, y) -> sub(x, y, false)))
end

@doc raw"""
    stable_submodules(T::TorQuadModule, act::Vector{TorQuadModuleMap}; kw...)

Return the submodules of `T` stable under the endomorphisms in `act` as
an iterator. Possible keyword arguments to restrict the submodules:
- `quotype::Vector{Int}`: only submodules whose quotient are isomorphic as an
  abelian group to `abelian_group(quotype)`.
"""
function stable_submodules(T::TorQuadModule, act::Vector{TorQuadModuleMap}; kw...)
  A = abelian_group(T)
  _act = [f.map_ab for f in act]
  _res = stable_subgroups(A, _act; kw..., op = (x, y) -> sub(x, y, false))
  return (sub(T, T.(StoA.(gens(S)))) for (S, StoA) in _res)
end
