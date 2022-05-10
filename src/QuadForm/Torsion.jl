export discriminant_group, torsion_quadratic_module, normal_form, genus, is_genus,
is_degenerate, cover, relations

# Torsion QuadraticForm
#
# Example:
# A = matrix(ZZ, [[2,0,0,-1],[0,2,0,-1],[0,0,2,-1],[-1,-1,-1,2]])
# L = Zlattice(gram = A)
# T = Hecke.discriminant_group(T)

# We represent torsion quadratic modules as quotients of Z-lattices
# by a full rank sublattice.
#
# We store them as a Z-lattice M together with a projection p : M -> A
# onto an abelian group A. The bilinear structure of A is induced via p,
# that is <a, b> = <p^-1(a), p^-1(a)> with values in Q/nZ, where n
# is the modulus and depends on the kernel of p.
#
# Elements of A are basically just elements of the underlying abelian group.
# To move between M and A, we use the lift function lift : M -> A
# and coercion A(m).
#
# N.B. Since there are no elements of Z-latties, we think of elements of M as
# elements of the ambient vector space. Thus if v::Vector is such an element
# then the coordinates with respec to the basis of M are given by
# solve_left(basis_matrix(M), v).
@attributes mutable struct TorQuadMod
  ab_grp::GrpAbFinGen             # underlying abelian group
  cover::ZLat                     # ZLat -> ab_grp, x -> x * proj
  rels::ZLat
  proj::fmpz_mat                  # is a projection and respects the forms
  gens_lift::Vector{Vector{fmpq}}
  gens_lift_mat::fmpq_mat
  modulus::fmpq
  modulus_qf::fmpq
  value_module::QmodnZ
  value_module_qf::QmodnZ
  gram_matrix_bilinear::fmpq_mat
  gram_matrix_quadratic::fmpq_mat
  gens
  is_normal::Bool

  TorQuadMod() = new()
end

################################################################################
#
#  Construction
#
################################################################################

# compute the torsion quadratic module M/N

@doc Markdown.doc"""
    torsion_quadratic_module(M::ZLat, N::ZLat; gens::Union{Nothing, Vector{<:Vector}} = nothing,
                                                    snf::Bool = true,
                                                    modulus::fmpq = fmpq(0),
                                                    check::Bool = true)

Given a Z-lattice $M$ and a sublattice $N$ of $M$, return the torsion quadratic
module $M/N$.

If `gens` is set, the images of `gens` will be used as the
generators of the abelian group $M/N$.

If `snf` is `true`, the underlying abelian group will be in Smith normal form.
Otherwise, the images of the basis of $M$ will be used as the generators.
"""
function torsion_quadratic_module(M::ZLat, N::ZLat; gens::Union{Nothing, Vector{<:Vector}} = nothing,
                                                    snf::Bool = true,
                                                    modulus::fmpq = fmpq(0),
                                                    modulus_qf::fmpq = fmpq(0),
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
  if gens != nothing
    gens_in_A = elem_type(A)[]
    for g in gens
      @req length(g) == n "Generator not an element of the ambient space"
      fl, v = can_solve_with_solution(BM,
                                      matrix(FlintQQ, 1, n, g),
                                      side = :left)
      @req denominator(v) == 1 "Generator not an element of the lattice"
      ginA = A(change_base_ring(FlintZZ, v))
      push!(gens_in_A, ginA)
    end
    S, mS = sub(A, gens_in_A)
    if check
      if order(S) != order(A)
        throw(ArgumentError("Generators do not generator the torsion module"))
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
  if gens != nothing
    gens_lift = gens
  else
    gens_lift = Vector{fmpq}[reshape(collect(change_base_ring(FlintQQ, mS(s).coeff) * BM), :) for s in Hecke.gens(S)]
  end

  num = basis_matrix(M) * gram_matrix(ambient_space(M)) * transpose(basis_matrix(N))
  if iszero(modulus)
    modulus = reduce(gcd, [a for a in num], init = zero(fmpq))
  end
  norm = reduce(gcd, diagonal(gram_matrix(N)), init = zero(fmpq))

  if iszero(modulus_qf)
    modulus_qf = gcd(norm, 2 * modulus)
  else
    modulus_qf = modulus_qf
  end

  T = TorQuadMod()
  T.cover = M
  T.rels = N
  T.ab_grp = S
  T.proj = inv(mS).map
  T.gens_lift = gens_lift
  T.gens_lift_mat = matrix(FlintQQ, length(gens_lift), degree(M), reduce(vcat, gens_lift, init = fmpq[]))
  T.modulus = modulus
  T.modulus_qf = modulus_qf
  T.value_module = QmodnZ(modulus)
  T.value_module_qf = QmodnZ(modulus_qf)
  T.is_normal = false
  return T
end

# compute M^#/M
function discriminant_group(L::ZLat)
  @req is_integral(L) "the lattice must be integral"
  T = torsion_quadratic_module(dual(L), L)
  set_attribute!(T,:is_degenerate => false)
  return T
end

@doc Markdown.doc"""
    order(T::TorQuadMod) -> fmpz

Return the order of `T`
"""
function order(T::TorQuadMod)
  return order(abelian_group(T))
end

@doc Markdown.doc"""
    exponent(T::TorQuadMod) -> fmpz

Return the exponent of `T`
"""
function exponent(T::TorQuadMod)
  return exponent(abelian_group(T))
end

@doc Markdown.doc"""
    elementary_divisors(T::TorQuadMod) -> Vector{fmpz}

Return the elementary divisors of underlying abelian group of `T`.
"""
function elementary_divisors(T::TorQuadMod)
  return elementary_divisors(abelian_group(T))
end

################################################################################
#
#  Basic field access
#
################################################################################

abelian_group(T::TorQuadMod) = T.ab_grp

cover(T::TorQuadMod) = T.cover

relations(T::TorQuadMod) = T.rels

value_module(T::TorQuadMod) = T.value_module

value_module_quadratic_form(T::TorQuadMod) = T.value_module_qf

################################################################################
#
#  Gram matrices
#
################################################################################

function gram_matrix_bilinear(T::TorQuadMod)
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

function gram_matrix_quadratic(T::TorQuadMod)
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
function Base.show(io::IO, ::MIME"text/plain" , T::TorQuadMod)
  @show_name(io,T)
  print(io, "Finite quadratic module over Integer Ring with underlying abelian group\n")
  println(io, abelian_group(T))
  print(io, "Gram matrix of the quadratic form with values in ")
  println(io, value_module_quadratic_form(T))
  show(io,MIME"text/plain"(), gram_matrix_quadratic(T))
end

function Base.show(io::IO, T::TorQuadMod)
  compact = get(io, :compact, false)
  if compact
    name = get_attribute(T,:name)
    if name !== nothing
      print(io, name)
    else
      print(io, "TorQuadMod ", gram_matrix_quadratic(T))
    end
  else
    print(io, "TorQuadMod: ")
    A = abelian_group(T)
    if is_snf(A)
      show_snf_structure(io, abelian_group(T))
      print(io, " ")
    end
    print(io, gram_matrix_quadratic(T))
  end
end



################################################################################
#
#  Elements
#
################################################################################

mutable struct TorQuadModElem
  data::GrpAbFinGenElem
  parent::TorQuadMod

  TorQuadModElem(T::TorQuadMod, a::GrpAbFinGenElem) = new(a, T)
end

elem_type(::Type{TorQuadMod}) = TorQuadModElem


################################################################################
#
#  Creation
#
################################################################################

function (T::TorQuadMod)(a::GrpAbFinGenElem)
  @req abelian_group(T) === parent(a) "Parents do not match"
  return TorQuadModElem(T, a)
end

# Coerces an element of the ambient space of cover(T) to T

function (T::TorQuadMod)(v::Vector)
  @req length(v) == dim(ambient_space(cover(T))) "Vector of wrong length"
  vv = map(FlintQQ, v)
  if eltype(vv) != fmpq
    error("Cannot coerce elements to the rationals")
  end
  return T(vv::Vector{fmpq})
end

function (T::TorQuadMod)(v::Vector{fmpq})
  @req length(v) == degree(cover(T)) "Vector of wrong length"
  vv = matrix(FlintQQ, 1, length(v), v)
  vv = change_base_ring(FlintZZ, solve_left(basis_matrix(cover(T)), vv))
  return T(abelian_group(T)(vv * T.proj))
end


################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, a::TorQuadModElem)
  v = a.data.coeff
  print(io, "[")
  for i in 1:length(v)
    if i == length(v)
      print(io, v[i])
    else
      print(io, v[i], ", ")
    end
  end
  print(io, "]")
end

################################################################################
#
#  Equality
#
################################################################################

function Base.:(==)(a::TorQuadModElem, b::TorQuadModElem)
  if parent(a) !== parent(b)
    return false
  else
    return data(a) == data(b)
  end
end

################################################################################
#
#  Generators
#
################################################################################

function gens(T::TorQuadMod)
  if isdefined(T, :gens)
    return T.gens::Vector{TorQuadModElem}
  else
    _gens = TorQuadModElem[T(g) for g in gens(abelian_group(T))]
    T.gens = _gens
    return _gens
  end
end

ngens(T::TorQuadMod) = length(T.gens_lift)

parent(a::TorQuadModElem) = a.parent

data(a::TorQuadModElem) = a.data

# Check the parent
function (A::GrpAbFinGen)(a::TorQuadModElem)
  @req A === abelian_group(parent(a)) "Parents do not match"
  return a.data
end

################################################################################
#
#  Addition
#
################################################################################

function Base.:(+)(a::TorQuadModElem, b::TorQuadModElem)
  @req parent(a) === parent(b) "Parents do not match"
  T = parent(a)
  return T(a.data + b.data)
end

function Base.:(*)(a::TorQuadModElem, b::fmpz)
  T = parent(a)
  return T(a.data * b)
end

Base.:(*)(a::fmpz, b::TorQuadModElem) = b * a

Base.:(*)(a::Integer, b::TorQuadModElem) = fmpz(a) * b

Base.:(*)(a::TorQuadModElem, b::Integer) = b * a

################################################################################
#
#  Inner product
#
################################################################################

function Base.:(*)(a::TorQuadModElem, b::TorQuadModElem)
  T = parent(a)
  z = inner_product(ambient_space(cover(T)), lift(a), lift(b))
  return value_module(T)(z)
end

inner_product(a::TorQuadModElem, b::TorQuadModElem)=(a*b)

################################################################################
#
#  Quadratic product
#
################################################################################

function quadratic_product(a::TorQuadModElem)
  T = parent(a)
  al = lift(a)
  z = inner_product(ambient_space(cover(T)), al, al)
  return value_module_quadratic_form(T)(z)
end

################################################################################
#
#  order
#
################################################################################

order(a::TorQuadModElem) = order(a.data)

################################################################################
#
#  Lift
#
################################################################################

# Lift an element to the ambient space of cover(parent(a))
function lift(a::TorQuadModElem)
  T = parent(a)
  z = change_base_ring(FlintQQ, a.data.coeff) * T.gens_lift_mat
  return fmpq[z[1, i] for i in 1:ncols(z)]
end

################################################################################
#
#  Maps between torsion quadratic modules
#
################################################################################

mutable struct TorQuadModMor <: Map{TorQuadMod, TorQuadMod, HeckeMap, TorQuadModMor}
  header::MapHeader{TorQuadMod, TorQuadMod}
  map_ab::GrpAbFinGenMap

  function TorQuadModMor(T::TorQuadMod, S::TorQuadMod, m::GrpAbFinGenMap)
    z = new()
    z.header = MapHeader(T, S)
    z.map_ab = m
    return z
  end
end

################################################################################
#
#  User constructors
#
################################################################################

function hom(T::TorQuadMod, S::TorQuadMod, M::fmpz_mat)
  map_ab = hom(abelian_group(T), abelian_group(S), M)
  return TorQuadModMor(T, S, map_ab)
end

function hom(T::TorQuadMod, S::TorQuadMod, img::Vector{TorQuadModElem})
  _img = GrpAbFinGenElem[]
  @req length(img) == ngens(T) "Wrong number of elements"
  for g in img
    @req parent(g) === S "Elements have the wrong parent"
    push!(_img, abelian_group(S)(g))
  end
  map_ab = hom(abelian_group(T), abelian_group(S), _img)
  return TorQuadModMor(T, S, map_ab)
end

function identity_map(T::TorQuadMod)
  map_ab = id_hom(abelian_group(T))
  return TorQuadModMor(T, T, map_ab)
end

id_hom(T::TorQuadMod) = identity_map(T)

function inv(f::TorQuadModMor)
  map_ab = inv(f.map_ab)
  return TorQuadModMor(codomain(f),domain(f),map_ab)
end

function compose(f::TorQuadModMor, g::TorQuadModMor)
  codomain(f) == domain(g) || error("incompatible (co)domains")
  map_ab = compose(f.map_ab, g.map_ab)
  return TorQuadModMor(domain(f), codomain(g), map_ab)
end

function image(f::TorQuadModMor, a::TorQuadModElem)
  A = abelian_group(domain(f))
  return codomain(f)(f.map_ab(A(a)))
end

function preimage(f::TorQuadModMor, a::TorQuadModElem)
  A = abelian_group(codomain(f))
  return domain(f)(f.map_ab\(A(a)))
end

is_bijective(f::TorQuadModMor) = is_bijective(f.map_ab)

################################################################################
#
#  Submodules
#
################################################################################


@doc Markdown.doc"""
    sub(T::TorQuadMod, generators::Vector{TorQuadModElem})-> TorQuadMod, Map

Return the submodule of `T` defined by `generators` and the inclusion morphism.
"""
function sub(T::TorQuadMod, gens::Vector{TorQuadModElem})
  if length(gens) > 0
    _gens = [lift(g) for g in gens]
    V = ambient_space(T.cover)
    _gens_mat = matrix(QQ, _gens)
    gens_new = [basis_matrix(T.rels); _gens_mat]
    cover = lattice(V, gens_new, isbasis = false)
  else
    cover = T.cover
    _gens = nothing
  end
  S = torsion_quadratic_module(cover, T.rels, gens=_gens, modulus=T.modulus,
                               modulus_qf=T.modulus_qf)
  imgs = [T(lift(g)) for g in Hecke.gens(S)]
  inclusion = hom(S, T, imgs)
  return S, inclusion
end

function TorQuadMod(q::fmpq_mat)
  @req is_square(q) "Matrix must be a square matrix"
  @req is_symmetric(q) "Matrix must be symmetric"

  d = denominator(q)
  Q = change_base_ring(FlintZZ, d * q)
  S, U, V = snf_with_transform(Q)
  D = change_base_ring(FlintQQ, U) * q * change_base_ring(FlintQQ, V)
  L = Zlattice(1//d * identity_matrix(QQ, nrows(q)), gram = d^2 * q)
  denoms = [denominator(D[i, i]) for i in 1:ncols(D)]
  rels = diagonal_matrix(denoms) * U
  LL = lattice(ambient_space(L), 1//d * change_base_ring(QQ, rels))
  return torsion_quadratic_module(L, LL, modulus = fmpq(1))
end

@doc Markdown.doc"""
    primary_part(T::TorQuadMod, m::fmpz)-> Tuple{TorQuadMod, TorQuadModMor}

Return the primary part of `T` as a submodule.
"""
function primary_part(T::TorQuadMod, m::fmpz)
  S, i = primary_part(T.ab_grp, m)
  genprimary = [i(s) for s in gens(S)]
  submod = sub(T, [T(a) for a in genprimary])
  return submod
end

primary_part(T::TorQuadMod,m::Int) = primary_part(T,ZZ(m))

@doc Markdown.doc"""
    orthogonal_submodule_to(T::TorQuadMod, S::TorQuadMod)-> TorQuadMod

Return the orthogonal submodule to the submodule `S` of `T`.
"""
function orthogonal_submodule_to(T::TorQuadMod, S::TorQuadMod)
  @assert is_sublattice(cover(T), cover(S)) "The second argument is not a submodule of the first argument"
  V = ambient_space(cover(T))
  G = gram_matrix(V)
  B = basis_matrix(cover(T))
  C = basis_matrix(cover(S))
  m = T.modulus
  Y = B * G * transpose(C)
  # Elements of the ambient module which pair integrally with cover(T)
  integral = inv(Y) * B
  # Element of the ambient module which pair in mZZ with cover(T)
  orthogonal =  m * integral
  # We have to make sure we get a submodule
  ortho = intersect(lattice(V, B), lattice(V, orthogonal))
  Borth = basis_matrix(ortho)
  gens_orth = [T(vec(collect(Borth[i,:]))) for i in 1:nrows(Borth)]
  return sub(T, gens_orth)
end

@doc Markdown.doc"""
    is_degenerate(T::TorQuadMod)-> Bool

Return true if the underlying bilinear form is degenerate.
"""
function is_degenerate(T::TorQuadMod)
  return get_attribute!(T,:is_degenerate) do
    return order(orthogonal_submodule_to(T,T)[1]) != 1
  end
end


@doc Markdown.doc"""
    radical_bilinear(T::TorQuadMod) -> Tuple{TorQuadMod, TorQuadModMor}

Return the radical `\{x \in T | b(x,T) = 0\}` of the bilinear form `b` on `T`.
"""
function radical_bilinear(T::TorQuadMod)
  return orthogonal_submodule_to(T,T)
end

@doc Markdown.doc"""
    radical_quadratic(T::TorQuadMod) -> Tuple{TorQuadMod, TorQuadModMor}

Return the radical `\{x \in T | b(x,T) = 0 and q(x)=0\}` of the quadratic form
`q` on `T`.
"""
function radical_quadratic(T::TorQuadMod)
  Kb, ib = radical_bilinear(T)
  G = gram_matrix_quadratic(Kb)*1//Kb.modulus
  F = GF(2, cached=false)
  G2 = map_entries(F, G)
  r, kermat = left_kernel(G2)
  kermat = lift(kermat[1:r,:])
  g = gens(Kb)
  n = length(g)
  kergen = [sum(kermat[i,j]*g[j] for j in 1:n) for i in 1:r]
  Kq, iq = sub(Kb,kergen)
  @assert iszero(gram_matrix_quadratic(Kq))
  return Kq, compose(iq,ib)
end

@doc Markdown.doc"""
    rescale(T::TorQuadMod, k::RingElement) -> TorQuadMod

Return the torsion quadratic module with quadratic form scaled by ``k``,
where k is a non-zero rational number.
If the old form was defined modulo `n`, then the new form is defined
modulo `n k`.
"""
function rescale(T::TorQuadMod, k::RingElement)
  @req !iszero(k) "Parameter ($k) must be non-zero"
  C = cover(T)
  inner_product_mat = k * gram_matrix(ambient_space(C))
  V = quadratic_space(QQ, inner_product_mat)
  M = lattice(V, basis_matrix(C))
  N = lattice(V, basis_matrix(T.rels))
  return torsion_quadratic_module(M, N)
end

@doc Markdown.doc"""
    normal_form(T::TorQuadMod; partial=false) -> tuple{TorQuadMod,TorQuadModMor}

Return the normal form `N` of the given torsion quadratic module `T` along
with the projection ``T -> N``.

Let `K` be the radical of the quadratic form of `T`. Then `N = T/K` is
half-regular. Two half-regular torsion quadratic modules are isometric
if and only if they have equal normal forms.
"""
function normal_form(T::TorQuadMod; partial=false)
  if T.is_normal
    return T, hom(T,T,gens(T))
  end
  if is_degenerate(T)
    K, _ = radical_quadratic(T)
    N = torsion_quadratic_module(cover(T), cover(K), modulus=T.modulus, modulus_qf=T.modulus_qf)
    i = hom(T, N, [N(lift(g)) for g in gens(T)])
  else
    N = T
    i = identity_map(T)
  end
  normal_gens = TorQuadModElem[]
  prime_div = prime_divisors(exponent(N))
  for p in prime_div
    D_p, I_p = primary_part(N, p)
    q_p = gram_matrix_quadratic(D_p)
    if p == 2
      q_p = q_p * D_p.modulus_qf^-1
    else
      q_p = q_p * D_p.modulus^-1
    end

    # the normal form is implemented for p-adic lattices
    # so we should work with the lattice q_p --> q_p^-1
    q_p1 = inv(q_p)
    prec = valuation(exponent(T), p) + 5
    D, U = padic_normal_form(q_p1, p, prec=prec, partial=partial)
    R = ResidueRing(ZZ, ZZ(p)^prec)
    U = map_entries(x->R(ZZ(x)),U)
    U = transpose(inv(U))

    # the inverse is in normal form - so to get a normal form for
    # the original one
    # it is enough to massage each 1x1 resp. 2x2 block.
    denom = denominator(q_p)
    q_pR = map_entries(x->R(ZZ(x)), denom*q_p)
    D = U * q_pR * transpose(U)
    D = map_entries(x->R(mod(lift(x),denom)), D)
    if p != 2
       # follow the conventions of Miranda-Morrison
       m = ZZ(D_p.modulus_qf//D_p.modulus)
       D = R(m)^-1*D
    end

    D1, U1 = _normalize(D, ZZ(p), false)
    U = U1 * U

    #apply U to the generators
    n1 = ncols(U)
    Gp =  gens(D_p);
    for i in 1:nrows(U)
      g = sum(lift(U[i,j]) * Gp[j] for j in 1:ncols(U))
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

@doc Markdown.doc"""
_brown_indecomposable(q::MatElem, p::fmpz) ->  fmpz
Return the Brown invariant of the indecomposable form ``q``.

The values are taken from Table 2.1 in [Shim2016]_.
INPUT:
- ``q`` - an indecomposable quadratic form represented by a
  rational `1 \times 1` or `2 \times 2` matrix
- ``p`` - a prime number
EXAMPLES::

  julia> q = matrix(QQ, 1, 1, [1//3])
  julia> _brown_indecomposable(q,fmpz(3))
  6
  julia> q = matrix(QQ, 1, 1, [2//3])
  julia> _brown_indecomposable(q,fmpz(3))
  2
"""
function _brown_indecomposable(q::MatElem, p::fmpz)
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

@doc Markdown.doc"""
    brown_invariant(self::TorQuadMod) -> Nemo.nmod
Return the Brown invariant of this torsion quadratic form.

Let `(D,q)` be a torsion quadratic module with values in `\QQ / 2 \ZZ`.
The Brown invariant `Br(D,q) \in \Zmod{8}` is defined by the equation

.. MATH::

  \exp \left( \frac{2 \pi i }{8} Br(q)\right) =
  \frac{1}{\sqrt{D}} \sum_{x \in D} \exp(i \pi q(x)).

The Brown invariant is additive with respect to direct sums of
torsion quadratic modules.

OUTPUT:

  - an element of `\Zmod{8}`
EXAMPLES::

  julia> L = Zlattice(gram=matrix(ZZ, [[2,-1,0,0],[-1,2,-1,-1],[0,-1,2,0],[0,-1,0,2]]))
  julia> T = Hecke.discriminant_group(L)
  julia> brown_invariant(T)
  4
"""
function brown_invariant(T::TorQuadMod)
  @req T.modulus_qf == 2 "the torsion quadratic form must have values in Q/2Z"
  @req !is_degenerate(T) "the torsion quadratic form must be non-degenerate"
  brown = ResidueRing(ZZ, 8)(0)
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

@doc Markdown.doc"""
    genus(T::TorQuadMod, signature_pair::Tuple{Int, Int}) -> ZGenus

Return the genus defined by a TorQuadMod T and the ``signature_pair``.
If no such genus exists, raise a ``ErrorException``.

REFERENCES:

  [Nik1977]_ Corollary 1.9.4 and 1.16.3.

"""
function genus(T::TorQuadMod, signature_pair::Tuple{Int, Int})
  s_plus = signature_pair[1]
  s_minus = signature_pair[2]
  rank = s_plus + s_minus
  if s_plus < 0 || s_minus < 0
    error("signatures must be non-negative")
  end
  if length(elementary_divisors(T)) > rank
    error("this discriminant form and signature do not define a genus")
  end
  disc = order(T)
  determinant = ZZ(-1)^s_minus * disc
  local_symbols = ZpGenus[]
  P = prime_divisors(2 * disc)
  sort!(P) # expects primes in ascending order
  for p in P
    D, _ = primary_part(T, p)
    if length(elementary_divisors(D)) != 0
      G_p = inv(gram_matrix_quadratic(D))
      # get rid of denominators without changing the local equivalence class
      G_p *= denominator(G_p)^2
      G_p = change_base_ring(ZZ, G_p)
      genus_p = genus(G_p, p, valuation(elementary_divisors(D)[end], p))
    else
      genus_p = ZpGenus(p, Vector{Int}[])
    end
    rk = rank - length(elementary_divisors(D))
    if rk > 0
      if p == 2
        det = remove(determinant, 2)[2]
        det *= prod([di[3] for di in genus_p._symbol])
        det = mod(det, 8)
        push!(genus_p._symbol, [0, rk, det, 0, 0])
      else
        det = jacobi_symbol(remove(determinant, p)[2], p)
        det = det * prod([di[3] for di in genus_p._symbol])
        push!(genus_p._symbol, [0, rk, det])
      end
    end
    sort!(genus_p._symbol)
    push!(local_symbols, genus_p)
  end
  # This genus has the right discriminant group
  # but it may be empty
  sym2 = local_symbols[1]._symbol

  if sym2[1][1] != 0
    sym2 = pushfirst!(sym2, [0, 0, 1, 0, 0])
  end
  if length(sym2) <= 1 || sym2[2][1] != 1
    sym2 = insert!(sym2, 2, [1, 0, 1, 0, 0])
  end
  if length(sym2) <= 2 || sym2[3][1] != 2
    sym2 = insert!(sym2, 3, [2, 0, 1, 0, 0])
  end

  if T.modulus_qf == 1
    # in this case the blocks of scales 1, 2, 4 are under determined
    # make sure the first 3 symbols are of scales 1, 2, 4
    # i.e. their valuations are 0, 1, 2

    # the form is odd
    block0 = [b for b in _blocks(sym2[1]) if b[4] == 1]

    o = sym2[2][4]
    # no restrictions on determinant and
    # oddity beyond existence
    # but we know if even or odd
    block1 = [b for b in _blocks(sym2[2]) if b[4] == o]

    d = sym2[3][3]
    o = sym2[3][4]
    t = sym2[3][5]
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
    if T.modulus_qf == 2
      # the form is even
      block0 = [b for b in _blocks(sym2[1]) if b[4] == 0]

      # if the jordan block of scale 2 is even we know it
      d = sym2[2][3]
      o = sym2[2][4]
      t = sym2[2][5]
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
        local_symbols[1] = ZpGenus(2, sym2)
        genus = ZGenus(signature_pair, local_symbols)
        if _isglobal_genus(genus)
          # make the symbol sparse again.
          i = 0
          k = 1
          while i < 3
            if sym2[k][2] == 0
              deleteat!(sym2, k)
            else
              k = k + 1
            end
            i = i + 1
          end
          local_symbols[1] = ZpGenus(2, sym2)
          genus = ZGenus(signature_pair, local_symbols)
          return genus
        end
      end
    end
  end
  error("this discriminant form and signature do not define a genus")
end


@doc Markdown.doc"""
    is_genus(T::TorQuadMod, signature_pair::Tuple{Int, Int}) -> Bool

Return if there is an integral lattice with this signature and discriminant form.

If the discriminant form is defined modulo `Z`, returns an odd lattice.
If it is defined modulo `2Z`, returns an even lattice.
"""
function is_genus(T::TorQuadMod, signature_pair::Tuple{Int, Int})
  s_plus = signature_pair[1]
  s_minus = signature_pair[2]
  even = T.modulus_qf == 2
  @req even || T.modulus_qf == 1 "the discriminant form must be defined modulo Z or 2Z"
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

