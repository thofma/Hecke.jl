################################################################################
#
#  Lattice constructors in the absolute case
#
################################################################################

# Test whether the Z-module with basis matrix B is O-invariant.
function _defines_lattice(V::ModAlgAss{QQField}, O, B)
  Binv = inv(B)
  for g in basis(O)
    T = action(V, elem_in_algebra(g))
    BB = B * T * Binv
    if !isone(abs(denominator(BB)))
      return false
    end
  end
  return true
end

@doc raw"""
    lattice(V::ModAlgAss, O::AlgAssAbsOrd, B::MatElem) -> ModAlgAssLat

Given a module with matrix action over a $\mathbf{Q}$-algebra $A$, a
$\mathbf{Z}$-order of $A$, return the lattice with $O$-lattice basis matrix $B$.
"""
function lattice(V::ModAlgAss{QQField}, O::AlgAssAbsOrd, B::MatElem; check::Bool = true)
  if B isa QQMatrix
    return _lattice(V, O, B, check = check)
  else
    return _lattice(V, O, change_base_ring(QQ, B)::QQMatrix, check = check)
  end
end

# internal function to construct lattice
function _lattice(V::ModAlgAss{QQField}, O::AlgAssAbsOrd, B::QQMatrix; check::Bool = true, is_hnf::Bool = false)
  if check
    fl = _defines_lattice(V, O, B)
    @req fl "Z-lattice with this basis matrix is not invariant under order"
  end

  @hassert :ModLattice _defines_lattice(V, O, B)

  if !is_hnf
    BB = QQMatrix(hnf!(FakeFmpqMat(B), :upperright))
  else
    BB = B
  end
  return ModAlgAssLat{typeof(O), typeof(V), typeof(BB)}(O, V, BB)
end

@doc raw"""
    natural_lattice(O::AlgAssAbsOrd{<:AlgMat}) -> ModAlgAssLat

Given a $\mathbf{Z}$-order $O$ of a rational matrix algebra contained in
$\mathrm{M}_n(\mathbf{Z})$, return $\mathbf{Z}^n$ as an $O$-lattice.
"""
function natural_lattice(O::AlgAssAbsOrd{<:AlgMat{QQFieldElem, QQMatrix}})
  A = algebra(O)
  if all(x -> isone(denominator(matrix(elem_in_algebra(x)))),
         basis(O, copy = false))
    M = Amodule(A, matrix.(basis(A)))
    if dim(A) == degree(A)^2 # this is a full matrix algebra
      M.is_abs_irreducible = 1
    end
    return lattice(M, O, identity_matrix(QQ, degree(algebra(O))))
  else
    throw(ArgumentError("Order is not contained in M_n(Z)"))
  end
end

################################################################################
#
#  Rank
#
################################################################################

rank(L::ModAlgAssLat) = nrows(basis_matrix(L))

################################################################################
#
#  Basis matrix
#
################################################################################

function basis_matrix(L::ModAlgAssLat)
  @req base_ring(L.base_ring) isa ZZRing "Order of lattice must be a Z-order"
  @req has_matrix_action(L.V) "Action on module must be given by matrices"
  return L.basis
end

function basis_matrix_inverse(L::ModAlgAssLat)
  @req base_ring(L.base_ring) isa ZZRing "Order of lattice must be a Z-order"
  @req has_matrix_action(L.V) "Action on module must be given by matrices"
  if isdefined(L, :basis_inv)
    return L.basis_inv
  else
    M = inv(basis_matrix(L))
    L.basis_inv = M
    return M
  end
end

################################################################################
#
#  String I/O
#
################################################################################

function Base.show(io::IO, L::ModAlgAssLat)
  print(io, "Lattice of rank ", rank(L), " over ", base_ring(L.base_ring))
end

################################################################################
#
#  Lattice arithmetic
#
################################################################################

function _hnf_nonzero(a::QQMatrix)
  b = QQMatrix(hnf(FakeFmpqMat(a)))
  i = 1
  while is_zero_row(b, i)
    i += 1
  end
  return b[i:nrows(b), 1:ncols(b)]
end

function *(m::Int, L::ModAlgAssLat)
  return lattice(L.V, L.base_ring, _hnf_nonzero(m * basis_matrix(L)))
end

function +(L::T, M::T) where {T <: ModAlgAssLat}
  @req L.base_ring === M.base_ring "Lattices must be defined over the same order"
  @req L.V === M.V "Lattices must have same ambient module"
  return lattice(L.V, L.base_ring, _hnf_nonzero(vcat(basis_matrix(L),
                                                     basis_matrix(M))))
end

function intersect(L::T, M::T) where {T <: ModAlgAssLat}
  @req L.base_ring === M.base_ring "Lattices must be defined over the same order"
  @req L.V === M.V "Lattices must have same ambient module"
  BM = basis_matrix(M)
  BN = basis_matrix(N)
  dM = denominator(BM)
  dN = denominator(BN)
  d = lcm(dM, dN)
  BMint = change_base_ring(FlintZZ, d * BM)
  BNint = change_base_ring(FlintZZ, d * BN)
  H = vcat(BMint, BNint)
  k, K = left_kernel(H)
  BI = divexact(change_base_ring(FlintQQ, hnf(view(K, 1:k, 1:nrows(BM)) * BMint)), d)
  return lattice(L.V, L.base_ring, BI)
end

function Base.:(==)(L::T, M::T) where {T <: ModAlgAssLat}
  return L.V === M.V && basis_matrix(M) == basis_matrix(N)
end

################################################################################
#
#  Local containment
#
################################################################################

function is_subset_locally(L::T, M::T, p::IntegerUnion) where {T <: ModAlgAssLat}
  if L.V !== M.V
    return false
  end
  t = basis_matrix(L) * basis_matrix_inverse(M)
  for m in t
    if !iszero(m) && valuation(m, p) < 0
      return false
    end
  end
  return true
end

function is_equal_locally(L::T, M::T, p::IntegerUnion) where {T <: ModAlgAssLat}
  return is_subset_locally(L, M, p) && is_subset_locally(M, L, p)
end

################################################################################
#
#  Action
#
################################################################################

@doc raw"""
    action(L::ModAlgAssLat, x)

Given a lattice $L$ over an order $O$ and an element $x$ of $O$, return
the matrix with which $x$ is acting on $L$.
"""
function action(L::ModAlgAssLat, x)
  T = basis_matrix(L)
  Tinv = basis_matrix_inverse(L)
  M = T * action(L.V, elem_in_algebra(x))
  mul!(M, M, Tinv)
  return M
end

function action_of_basis(L::ModAlgAssLat)
  A = action_of_order_basis(L.V, L.base_ring)
  T = basis_matrix(L)
  Tinv = basis_matrix_inverse(L)
  res = Vector{eltype(A)}(undef, length(A))
  for i in 1:length(res)
    M = T * A[i]
    res[i] = mul!(M, M, Tinv)
  end
  return res
end

################################################################################
#
#  Index
#
################################################################################

function index(L::T, M::T) where {T <: ModAlgAssLat}
  t = basis_matrix(L) * basis_matrix_inverse(M)
  @req !isone(denominator(t)) "First lattice not contained in second lattice"
  return abs(det(t))
end
