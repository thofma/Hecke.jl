export discriminant_group, torsion_quadratic_module, normal_form

# Torsion QuadraticForm
#
# Example:
# A = matrix(ZZ, [[2,0,0,-1],[0,2,0,-1],[0,0,2,-1],[-1,-1,-1,2]])
# L = Zlattice(gram = A)
# T = Hecke.discriminant_group(T)

# We representation torsion quadratic modules as quotients of Z-lattices
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
# v * inv(basis_matrix(M)).
mutable struct TorQuadMod
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
  fl, _rels = issublattice_with_relations(M, N)
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
    gens_lift = Vector{fmpq}[collect(change_base_ring(FlintQQ, mS(s).coeff) * BM) for s in Hecke.gens(S)]
  end

  num = basis_matrix(M) * gram_matrix(ambient_space(M)) * basis_matrix(N)'
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
  T.gens_lift_mat = matrix(FlintQQ, length(gens_lift), ngens(A), reduce(vcat, gens_lift, init = fmpq[]))
  T.modulus = modulus
  T.modulus_qf = modulus_qf
  T.value_module = QmodnZ(modulus)
  T.value_module_qf = QmodnZ(modulus_qf)
  return T
end

# compute M^#/M
function discriminant_group(L::ZLat)
  # I need to check that M is integral
  return torsion_quadratic_module(dual(L), L)
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

Returns the exponent of `T`
"""
function exponent(T::TorQuadMod)
  return exponent(abelian_group(T))
end

@doc Markdown.doc"""
    elementary_divisors(T::TorQuadMod) -> Vector{fmpz}

Returns the elementary divisors of underlying abelian group of `T`.
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
function Base.show(io::IO, T::TorQuadMod)
  print(io, "Finite quadratic module over Integer Ring with underlying abelian group\n")
  println(io, abelian_group(T))
  print(io, "Gram matrix of the quadratic form with values in ")
  println(io, value_module_quadratic_form(T))
  print(io, gram_matrix_quadratic(T))
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
  @req length(v) == dim(ambient_space(cover(T))) "Vector of wrong length"
  vv = change_base_ring(FlintZZ, matrix(FlintQQ, 1, length(v), v) * inv(basis_matrix(cover(T))))
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
  f = hom(abelian_group(T), abelian_group(S), M)
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

function image(f::TorQuadModMor, a::TorQuadModElem)
  A = abelian_group(domain(f))
  return codomain(f)(f.map_ab(A(a)))
end

function preimage(f::TorQuadModMor, a::TorQuadModElem)
  A = abelian_group(domain(f))
  return domain(f)(f.map_ab\(A(a)))
end

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
  @req issquare(q) "Matrix must be a square matrix"
  @req issymmetric(q) "Matrix must be symmetric"

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

#        if modulus is None or check:
#           # The inner product of two elements `b(v1+W,v2+W)`
#           # is defined `mod (V,W)`
#           num = V.basis_matrix() * V.inner_product_matrix() * W.basis_matrix().T
#           max_modulus = gcd(num.list())
#
#       if modulus is None:
#           modulus = max_modulus
#       elif check and max_modulus / modulus not in V.base_ring():
#           raise ValueError("the modulus must divide (V, W)")
#
#       if modulus_qf is None or check:
#           # The quadratic_product of an element `q(v+W)` is defined
#           # `\mod 2(V,W) + ZZ\{ (w,w) | w in w\}`
#           norm = gcd(W.gram_matrix().diagonal())
#           max_modulus_qf = gcd(norm, 2 * modulus)
#
#       if modulus_qf is None:
#           modulus_qf = max_modulus_qf
#       elif check and max_modulus_qf / modulus_qf not in V.base_ring():
#           raise ValueError("the modulus_qf must divide (V, W)")
#       return super(TorsionQuadraticModule, cls).__classcall__(cls, V, W, gens, modulus, modulus_qf)
@doc Markdown.doc"""
    primary_part(T::TorQuadMod, m::fmpz)-> Tuple{TorQuadMod, TorQuadModMor}

Return the primary part of `T` as a submodule.
"""
function primary_part(T::TorQuadMod, m::fmpz)
  S, i = psylow_subgroup(T.ab_grp, m)
  genprimary = [i(s) for s in gens(S)]
  submod = sub(T, [T(a) for a in genprimary])
  return submod
end

@doc Markdown.doc"""
    orthogonal_submodule_to(T::TorQuadMod, S::TorQuadMod)-> TorQuadMod

Return the orthogonal submodule to the submodule `S` of `T`.
"""
function orthogonal_submodule_to(T::TorQuadMod, S::TorQuadMod)
  @assert issublattice(cover(T), cover(S)) "The second argument is not a submodule of the first argument"
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
  Ortho = intersect(lattice(V, B), lattice(V, orthogonal))
  ortho = Hecke.discriminant_group(Ortho)
  return sub(T, gens(ortho))
end

@doc Markdown.doc"""
    isdegenerate(T::TorQuadMod)-> Bool

Return true if the underlying bilinear form is degenerate.
"""
function isdegenerate(T::TorQuadMod)
  if order(orthogonal_submodule_to(T,T)[1]) == 1
    return true
  else
    return false
  end
end

@doc Markdown.doc"""
    rescale(T::TorQuadMod, k::RingElement) -> TorQuadMod

Returns the torsion quadratic module with quadratic form scaled by ``k``,
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
    normal_form(T::TorQuadMod; partial=false) -> TorQuadMod

Return the normal form of given torsion quadratic module.
"""
function normal_form(T::TorQuadMod; partial=false)
  normal_gens = TorQuadModElem[]
  prime_div = prime_divisors(exponent(T))
  for p in prime_div
    D_p, I_p = primary_part(T, p)
    q_p = gram_matrix_quadratic(D_p)
    q_p = q_p * D_p.modulus_qf^-1

    # continue with the non-degenerate part
    r = rank(q_p)
    dd = denominator(q_p)
    G0 = change_base_ring(FlintZZ, dd * q_p)
    n = nrows(q_p)
    if r != n
      _, U = hnf_with_transform(G0)
      _ker = U[(r + 1):n, :]
      _nondeg = U[1:r, :]
      ker = change_base_ring(FlintQQ, _ker)
      nondeg = change_base_ring(FlintQQ, _nondeg)
    else
      ker = zero_matrix(FlintQQ, 0, n)
      nondeg = identity_matrix(FlintQQ, n)
    end
    q_p = nondeg * q_p * transpose(nondeg)

    # the normal form is implemented for p-adic lattices
    # so we should work with the lattice q_p --> q_p^-1
    q_p1 = inv(q_p)
    prec = valuation(exponent(T), p) + 5
    D, U = padic_normal_form(q_p1, p, prec=2*prec+5, partial=partial)
    # if we compute the inverse in the p-adics everything explodes -> go to ZZ
    U = transpose(inv(U))
    d = denominator(U)
    R = ResidueRing(ZZ, ZZ(p)^prec)
    U = d*U * lift(R(d)^-1)
    # the inverse is in normal form - so to get a normal form for
    # the original one
    # it is enough to massage each 1x1 resp. 2x2 block.
    D = U * q_p * U' * p^valuation(denominator(q_p), p)
    d = denominator(D)
    D = change_base_ring(ZZ, d*D)
    D = change_base_ring(R, D)*R(d)^-1
    D, U1 = _normalize(D, ZZ(p), false)

    # reattach the degenerate part
    U1 = change_base_ring(ZZ, U1)
    U = change_base_ring(ZZ, U)
    U = U1 * U
    nondeg = change_base_ring(ZZ, nondeg)
    nondeg = U * nondeg
    U = vcat(nondeg, ker)

    #apply U to the generators
    n1 = ncols(U)
    Gp =  gens(D_p);
    for i in 1:nrows(U)
      g = sum(U[i,j] * Gp[j] for j in 1:ncols(U))
      push!(normal_gens, I_p(g))
    end
  end
  return sub(T, normal_gens)
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
      if valuation(q[1,1],2) > v + 1 && valuation(q[2, 2],2) > v + 1
        # type U
        return mod(0, 8)
      else
        # type V
        return mod(4*v, 8)
      end
    end
    u = numerator(q[1, 1])
    return mod(divexact(u + v*(u^2 - 1), 2), 8)
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
#=
@doc Markdown.doc"""
    genus(T::TorQuadMod, signature_pair::Tuple) -> 
    
Return the genus defined by ``self`` and the ``signature_pair``.
If no such genus exists, raise a ``ValueError``.

REFERENCES:

  [Nik1977]_ Corollary 1.9.4 and 1.16.3.

EXAMPLES::

  sage: L = IntegralLattice("D4").direct_sum(IntegralLattice("A2"))
  sage: D = L.discriminant_group()
  sage: genus = D.genus(L.signature_pair())
  sage: genus
  Genus of
  None
  Signature:  (6, 0)
  Genus symbol at 2:    1^4:2^-2
  Genus symbol at 3:     1^-5 3^-1
  sage: genus == L.genus()
  True

Let `H` be an even unimodular lattice of signature `(9, 1)`.
Then `L = D_4 + A_2` is primitively embedded in `H`. We compute the discriminant
form of the orthogonal complement of `L` in `H`::

  sage: DK = D.twist(-1)
  sage: DK
  Finite quadratic module over Integer Ring with invariants (2, 6)
  Gram matrix of the quadratic form with values in Q/2Z:
  [  1 1/2]
  [1/2 1/3]

We know that  `K` has signature `(5, 1)` and thus we can compute
the genus of `K` as::

  sage: DK.genus((3,1))
  Genus of
  None
  Signature:  (3, 1)
  Genus symbol at 2:    1^2:2^-2
  Genus symbol at 3:     1^-3 3^1

We can also compute the genus of an odd lattice
from its discriminant form::

  sage: L = IntegralLattice(matrix.diagonal(range(1,5)))
  sage: D = L.discriminant_group()
  sage: D.genus((4,0))
  Genus of
  None
  Signature:  (4, 0)
  Genus symbol at 2:    [1^-2 2^1 4^1]_6
  Genus symbol at 3:     1^-3 3^1

TESTS::

  sage: L.genus() == D.genus((4,0))
  True
  sage: D.genus((1,0))
  Traceback (most recent call last):
  ...
  ValueError: this discriminant form and signature do not define a genus

A systematic test of lattices of small ranks and determinants::

  sage: from sage.quadratic_forms.genera.genus import genera
  sage: signatures = [(1,0),(1,1),(1,2),(3,0),(0,4)]
  sage: dets = range(1,33)
  sage: genera = flatten([genera(s, d, even=False) for d in dets for s in signatures])    # long time
  sage: all(g == g.discriminant_form().genus(g.signature_pair()) for g in genera)  # long time
  True
"""
function genus(T::TorQuadMod, signature_pair::Tuple)
  s_plus = ZZ(signature_pair[0])
  s_minus = ZZ(signature_pair[1])
  rank = s_plus + s_minus
  if s_plus < 0 or s_minus < 0
    raise ValueError("signatures must be non-negative")
  end
  if len(self.invariants()) > rank:
    raise ValueError("this discriminant form and " + "signature do not define a genus")
  end
  disc = self.cardinality()
  determinant = ZZ(-1)**s_minus * disc
  local_symbols = []
  for p in (2 * disc).prime_divisors():
    D = self.primary_part(p)
    if len(D.invariants()) != 0:
      G_p = D.gram_matrix_quadratic().inverse()
      # get rid of denominators without changing the local equivalence class
      G_p *= G_p.denominator()**2
      G_p = G_p.change_ring(ZZ)
      local_symbol = p_adic_symbol(G_p, p, D.invariants()[-1].valuation(p))
    else:
      local_symbol = []
    end
    rk = rank - len(D.invariants())
    if rk > 0:
      if p == 2:
        det = determinant.prime_to_m_part(2)
        det *= prod([di[2] for di in local_symbol])
        det = det % 8
        local_symbol.append([ZZ(0), rk, det, ZZ(0), ZZ(0)])
      else:
        det = legendre_symbol(determinant.prime_to_m_part(p), p)
        det = (det * prod([di[2] for di in local_symbol]))
        local_symbol.append([ZZ(0), rk, det])
      end
    end
    local_symbol.sort()
    local_symbol = Genus_Symbol_p_adic_ring(p, local_symbol)
    local_symbols.append(local_symbol)
  end
  # This genus has the right discriminant group
  # but it may be empty
  sym2 = local_symbols[0].symbol_tuple_list()

  if sym2[0][0] != 0:
    sym2 = [[ZZ(0), ZZ(0), ZZ(1), ZZ(0), ZZ(0)]] + sym2
  end
  if len(sym2) <= 1 or sym2[1][0] != 1:
    sym2 = sym2[:1] + [[ZZ(1), ZZ(0), ZZ(1), ZZ(0), ZZ(0)]] + sym2[1:]
  end
  if len(sym2) <= 2 or sym2[2][0] != 2:
    sym2 = sym2[:2] + [[ZZ(2), ZZ(0), ZZ(1), ZZ(0), ZZ(0)]] + sym2[2:]
  end

  if self.value_module_qf().n == 1:
    # in this case the blocks of scales 1, 2, 4 are under determined
    # make sure the first 3 symbols are of scales 1, 2, 4
    # i.e. their valuations are 0, 1, 2

    # the form is odd
    block0 = [b for b in _blocks(sym2[0]) if b[3] == 1]

    o = sym2[1][3]
    # no restrictions on determinant and
    # oddity beyond existence
    # but we know if even or odd
    block1 = [b for b in _blocks(sym2[1]) if b[3] == o]

    d = sym2[2][2]
    o = sym2[2][3]
    t = sym2[2][4]
    # if the jordan block of scale 2 is even we know it
    if o == 0:
      block2 = [sym2[2]]
      # if it is odd we know det and oddity mod 4 at least
    else:
      block2 = [b for b in _blocks(sym2[2]) if b[3] == o
        and (b[2] - d) % 4 == 0
        and (b[4] - t) % 4 == 0
        and (b[2] - d) % 8 == (b[4] - t) % 8  # if the oddity is altered by 4 then so is the determinant
        ]
  elif self.value_module_qf().n == 2:
    # the form is even
    block0 = [b for b in _blocks(sym2[0]) if b[3] == 0]

    # if the jordan block of scale 2 is even we know it
    d = sym2[1][2]
    o = sym2[1][3]
    t = sym2[1][4]
    if o == 0:
      block1 = [sym2[1]]
    else:
      # the block is odd and we know det and oddity mod 4
      block1 = [b for b in _blocks(sym2[1])
                if b[3] == o
                and (b[2] - d) % 4 == 0
                and (b[4] - t) % 4 == 0
                and (b[2] - d) % 8 == (b[4] - t) % 8 # if the oddity is altered by 4 then so is the determinant
                ]
    end
    # this is completely determined
    block2 = [sym2[2]]
  else:
    raise ValueError("this is not a discriminant form")
  end

  # figure out which symbol defines a genus and return that
  for b0 in block0:
    for b1 in block1:
      for b2 in block2:
        sym2[:3] = [b0, b1, b2]
        local_symbols[0] = Genus_Symbol_p_adic_ring(2, sym2)
        genus = GenusSymbol_global_ring(signature_pair, local_symbols)
        if is_GlobalGenus(genus):
          # make the symbol sparse again.
          i = 0
          k = 0
          while i < 3:
            if sym2[k][1] == 0:
              sym2.pop(k)
            else:
              k = k + 1
            end
            i = i + 1
          end
          local_symbols[0] = Genus_Symbol_p_adic_ring(2, sym2)
          genus = GenusSymbol_global_ring(signature_pair, local_symbols)
          return genus
        end
      end
    end
  end
  raise ValueError("this discriminant form and signature do not define a genus")
end


@doc Markdown.doc"""
    isgenus(T::TorQuadMod, signature_pair::Tuple; even=true) ->
Return ``True`` if there is a lattice with this signature and discriminant form.

.. TODO::

    implement the same for odd lattices

INPUT:

- signature_pair -- a tuple of non negative integers ``(s_plus, s_minus)``
- even -- bool (default: ``True``)

EXAMPLES::

    sage: L = IntegralLattice("D4").direct_sum(IntegralLattice(3 * Matrix(ZZ,2,[2,1,1,2])))
    sage: D = L.discriminant_group()
    sage: D.is_genus((6,0))
    True

Let us see if there is a lattice in the genus defined by the same discriminant form
but with a different signature::

    sage: D.is_genus((4,2))
    False
    sage: D.is_genus((16,2))
    True
"""
function isgenus(T::TorQuadMod, signature_pair::Tuple; even=true)
  s_plus = ZZ(signature_pair[0])
  s_minus = ZZ(signature_pair[1])
  if s_plus < 0 or s_minus < 0
    raise ValueError("signature invariants must be non negative")
  end
  rank = s_plus + s_minus
  signature = s_plus - s_minus
  D = cardinality(T)
  det = (-1)^s_minus * D
  if rank < len(self.invariants())
    return false
  end
  if even==true && T._modulus_qf != 2
    error("the discriminant form of an even lattice has values modulo 2.")
  end
  if even!=true && T._modulus != T._modulus_qf != 1
    error("the discriminant form of an odd lattice has values modulo 1.")
  end
  if even == false
    error("at the moment sage knows how to do this only for even genera. Help us to implement this for odd genera.")
  end
  for p in prime_divisors(D)
    # check the determinant conditions
    Q_p = primary_part(T, p)[1]
    gram_p = gram_matrix_quadratic(Q_p)
    length_p = length(Q_p.invariants())
    u = det.prime_to_m_part(p)
    up = gram_p.det().numerator().prime_to_m_part(p)
    if p != 2 and length_p == rank
      if jacobi_symbol(u, p) != jacobi_symbol(up, p)
        return false
      end
    end
    if p == 2
      if rank % 2 != length_p % 2
        return false
      end
      n = (rank - length_p) // 2
      if u % 4 != (-1)^(n % 2) * up % 4
        return false
      end
      if rank == length_p:
        a = QQ(1) // QQ(2)
        b = QQ(3) // QQ(2)
        diag = gram_p.diagonal()
        if not (a in diag or b in diag)
          if u % 8 != up % 8
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
=#