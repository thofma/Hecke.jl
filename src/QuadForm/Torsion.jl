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
  proj::fmpz_mat                  # is a projection and respects the forms
  gens_lift::Vector{Vector{fmpz}}
  gens_lift_ambient::Vector{Vector{fmpq}}
  gens_lift_mat::fmpz_mat          # integer matrix
  gens_lift_mat_ambient::fmpq_mat
  d::fmpz
  rels::fmpz_mat
  modulus::fmpq 
  modulus_qf::fmpq
  value_module::QmodnZ
  value_module_qf::QmodnZ
  gram_matrix_bilinear::fmpq_mat
  gram_matrix_quadratic::fmpq_mat

  TorQuadMod() = new()
end

################################################################################
#
#  Construction
#
################################################################################

# compute the torsion quadratic module M/N
function torsion_quadratic_module(M::ZLat, N::ZLat)
  @req ambient_space(M) === ambient_space(N) "Lattices must have same ambient space"
  _rels = basis_matrix(N) * inv(basis_matrix(M))
  @req isone(denominator(_rels)) "Second lattice must be a submodule of first lattice"
  rels = change_base_ring(FlintZZ, _rels)
  A = abelian_group(rels)
  S, mS = snf(A)
  gens_lift = [collect(mS(s).coeff) for s in gens(S)]

  num = basis_matrix(M) * gram_matrix(ambient_space(M)) * basis_matrix(N)'
  modulus = reduce(gcd, [a for a in num], init = zero(fmpq))
  norm = reduce(gcd, diagonal(gram_matrix(N)), init = zero(fmpq))
  modulus_qf = gcd(norm, 2 * modulus)

  T = TorQuadMod()
  T.cover = M
  T.ab_grp = S
  T.proj = inv(mS).map
  T.gens_lift = gens_lift
  T.gens_lift_mat = matrix(ZZ, length(gens_lift), ngens(A), reduce(vcat, gens_lift))
  T.gens_lift_mat_ambient = change_base_ring(FlintQQ, T.gens_lift_mat) * basis_matrix(M)
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

function Base.show(io::IO, T::TorQuadMod)
  print(io, "Finite quadratic module over Integer Ring with invariants ")
  println(io, elementary_divisors(abelian_group(T)))
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
  a::GrpAbFinGenElem
  parent::TorQuadMod

  TorQuadModElem(T::TorQuadMod, a::GrpAbFinGenElem) = new(a, T)
end

# TODO: Check the parents ...
(T::TorQuadMod)(a::GrpAbFinGenElem) = TorQuadModElem(T, a)

function (T::TorQuadMod)(v::Vector{fmpq})
  vv = change_base_ring(FlintZZ, matrix(FlintQQ, 1, length(v), v) * inv(basis_matrix(cover(T))))
  return T(abelian_group(T)(vv * T.proj))
end

# TODO: Cache this
gens(T::TorQuadMod) = [T(g) for g in gens(abelian_group(T))]

parent(a::TorQuadModElem) = a.parent

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
  z = change_base_ring(FlintQQ, a.a.coeff) * T.gens_lift_mat_ambient
  return fmpq[z[1, i] for i in 1:ncols(z)]
end


# this is broken
#function TorQuadMod(q::fmpq_mat)
#  @req issquare(q) "Matrix must be a square matrix"
#  @req issymmetric(q) "Matrix must be symmetric"
#
#  d = denominator(q)
#  Q = change_base_ring(FlintZZ, d * q)
#  S, U, V = snf_with_transform(Q)
#  D = change_base_ring(FlintQQ, U) * q * change_base_ring(FlintQQ, V)
#  @show D
#  L = Zlattice(gram = d^2 * q)
#  denoms = [denominator(D[i, i]) for i in 1:ncols(D)]
#  rels = diagonal_matrix(denoms) * U
#  _A = abelian_group(rels)
#  S, T = snf(_A)
#  @show T
#  @show T(gens(S)[1])
#  value_module = QmodnZ()
#  return TorQuadMod(S, L, d, rels, value_module)
#end


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

