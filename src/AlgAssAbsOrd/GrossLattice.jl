################################################################################
#
#  Gross lattice of an order in a quaternion algebra over QQ
#
################################################################################

@doc raw"""
    gross_lattice(O::AlgAssAbsOrd{<:QuaternionAlgebra{QQFieldElem}}) -> ZZLat

Return the Gross lattice of the order $O$ in a quaternion algebra $A$ over
$\mathbf{Q}$: the elements of reduced trace zero in $\mathbf{Z} + 2O$, a
lattice of rank $3$, with the reduced norm as its quadratic form.

It lies in the quadratic space on the coordinates with respect to `basis(A)`
whose bilinear form is $(x, y) \mapsto \mathrm{trd}(x\bar{y})/2$, so that the
norm of a vector is the reduced norm of the element and not twice it. Its
basis consists of the coordinates of [`gross_lattice_basis`](@ref) and its
Gram matrix is [`gross_gram_matrix`](@ref) of that basis.

If $A$ is definite, the lattice is positive definite. For a maximal order of
the quaternion algebra ramified exactly at $p$ and infinity, the determinant
of the Gram matrix is $4p^2$ [CG14](@cite), and two such maximal orders are
isomorphic if and only if their Gross lattices are isometric [GL25](@cite).

# Examples

```jldoctest
julia> A = quaternion_algebra(QQ, -1, -3);

julia> L = gross_lattice(maximal_order(A));

julia> rank(L), det(L)
(3, 36)
```
"""
function gross_lattice(O::AlgAssAbsOrd{<:QuaternionAlgebra{QQFieldElem}})
  a, b = standard_form(algebra(O))
  V = quadratic_space(QQ, diagonal_matrix(QQ, [one(QQ), -a, -b, a * b]))
  return lattice(V, _gross_lattice_coordinates(O))
end

@doc raw"""
    gross_lattice_basis(O::AlgAssAbsOrd{<:QuaternionAlgebra{QQFieldElem}})
      -> Vector{AssociativeAlgebraElem{QQFieldElem}}

Return a basis of the Gross lattice of $O$, the elements of reduced trace
zero in $\mathbf{Z} + 2O$, as three elements of the algebra of $O$; see
[`gross_lattice`](@ref).

# Examples

```jldoctest
julia> A = quaternion_algebra(QQ, -1, -3);

julia> B = gross_lattice_basis(maximal_order(A));

julia> length(B), all(iszero, trred.(B))
(3, true)
```
"""
function gross_lattice_basis(
    O::AlgAssAbsOrd{<:QuaternionAlgebra{QQFieldElem}})
  A = algebra(O)
  X = _gross_lattice_coordinates(O)
  return [A(collect(X[k, :])) for k in 1:3]
end

@doc raw"""
    gross_gram_matrix(B::Vector{<:AssociativeAlgebraElem{QQFieldElem}})
      -> ZZMatrix

Return the Gram matrix of the three elements in `B`, a basis of a Gross
lattice in a quaternion algebra over $\mathbf{Q}$, with respect to the
bilinear form $(x, y) \mapsto \mathrm{trd}(x\bar{y})/2$: the reduced norms
of the elements are on its diagonal. The matrix is integral for a basis of a
Gross lattice; an `ArgumentError` is thrown otherwise.

# Examples

```jldoctest
julia> A = quaternion_algebra(QQ, -1, -3);

julia> B = gross_lattice_basis(maximal_order(A));

julia> G = gross_gram_matrix(B);

julia> det(G), [G[i, i] for i in 1:3] == normred.(B)
(36, true)
```
"""
function gross_gram_matrix(B::Vector{<:AssociativeAlgebraElem{QQFieldElem}})
  @req length(B) == 3 "a basis of a Gross lattice has 3 elements"
  A = parent(first(B))
  @req A isa QuaternionAlgebra "the elements must lie in a quaternion algebra"
  # On 1, i, j, ij of (a, b) the form trd(x conj(y))/2 has Gram matrix
  # diag(1, -a, -b, ab).
  a, b = standard_form(A)
  X = matrix(QQ, [coefficients(x, copy = false)[k] for x in B, k in 1:4])
  G = X * diagonal_matrix(QQ, [one(QQ), -a, -b, a * b]) * transpose(X)
  @req isone(denominator(G)) "the elements do not span a Gross lattice"
  return map_entries(ZZ, G)
end

# The coordinates on basis(A) = 1, i, j, ij of a basis of the Gross lattice of
# O. Its elements are the n + 2x, x in O, of trace 2n + trd(2x) = 0, that is
# the 2x - trd(x): the image of O under x -> 2x - trd(x), whose kernel is
# O cap Q = Z. In coordinates on the basis of O this map sends the i-th basis
# element to 2e_i - trd(b_i)c, with c the coordinates of 1; a Hermite normal
# form of these four integral rows has one zero row and three rows spanning
# the image.
function _gross_lattice_coordinates(
    O::AlgAssAbsOrd{<:QuaternionAlgebra{QQFieldElem}})
  M = basis_matrix(O, copy = false)
  # the coordinates of 1 = basis(A)[1] on the basis of O
  c = basis_matrix_inverse(O, copy = false)
  G = zero_matrix(ZZ, 4, 4)
  for i in 1:4
    # trd(b_i), as trd(x_0 + x_1 i + x_2 j + x_3 ij) = 2 x_0
    t = 2 * M[i, 1]
    for j in 1:4
      G[i, j] = ZZ((i == j ? 2 : 0) - t * c[1, j])
    end
  end
  H = hnf(G)
  rows = [k for k in 1:4 if !is_zero_row(H, k)]
  @assert length(rows) == 3
  return change_base_ring(QQ, H[rows, :]) * M
end
