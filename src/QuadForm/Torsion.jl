export discriminant_group, torsion_quadratic_module

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
  V = ambient_space(T.cover)
  _gens = matrix(QQ, [lift(g) for g in gens])
  gens_new = [basis_matrix(T.rels); _gens]
  cover = lattice(V, gens_new, isbasis = false)
  S = torsion_quadratic_module(cover, T.rels)
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
    # if we compute the inverse in the p-adics everything explodes --> go to ZZ
    U = transpose(inv(U))
    # the inverse is in normal form - so to get a normal form for the original one
    # it is enough to massage each 1x1 resp. 2x2 block.
    D = U * q_p * U' * p^valuation(denominator(q_p), p) 
    R = ResidueRing(ZZ, ZZ(p^prec))
    D = change_base_ring(ZZ, D)
    D = change_base_ring(R, D)
    _, U = _normalize(D, ZZ(p), false)

    # reattach the degenerate part
    U = change_base_ring(ZZ, U)
    nondeg = change_base_ring(ZZ, nondeg)
    nondeg = U * nondeg
    U = vcat(nondeg, ker)

    #apply U to the generators
    n1 = ncols(U)
    Gp =  gens(D_p); 
    for i in 1:nrows(U) 
      g = sum(U[i,j] * Gp[j] for j in 1:ncols(U))
      push!(normal_gens, g)
    end
  end
  return sub(T, normal_gens)
end
