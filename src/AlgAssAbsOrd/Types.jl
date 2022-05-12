################################################################################
#
#  AlgAssAbsOrd / AlgAssAbsOrdElem
#
################################################################################

# Orders in algebras over the rationals
@attributes mutable struct AlgAssAbsOrd{S, T} <: Ring
  algebra::S                       # Algebra containing the order
  dim::Int
  basis#::Vector{AlgAssAbsOrdElem{S, T}}
  basis_alg::Vector{T}             # Basis as array of elements of the algebra
  basis_matrix::FakeFmpqMat           # Basis matrix of order wrt basis of the algebra
  basis_mat_inv::FakeFmpqMat       # Inverse of basis matrix
  gen_index::fmpq                  # The det of basis_mat_inv as fmpq
  index::fmpz                      # The det of basis_mat_inv
                                   # (this is the index of the equation order
                                   #  in the given order)
  disc::fmpz                       # Discriminant

  is_maximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  #trace_mat::fmpz_mat              # The reduced trace matrix (if known)
  trred_matrix::fmpz_mat

  picard_group#::MapPicardGrp

  tcontain::FakeFmpqMat

  isnice::Bool
  nice_order#Tuple{AlgAssAbsOrd, T}
  nice_order_ideal::fmpz

  function AlgAssAbsOrd{S, T}(A::S) where {S, T}
    # "Default" constructor with default values.
    O = new{S, T}(A, dim(A))
    O.is_maximal = 0
    O.isnice = false
    O.tcontain = FakeFmpqMat(zero_matrix(FlintZZ, 1, dim(A)))
    return O
  end

  function AlgAssAbsOrd{S, T}(A::S, M::FakeFmpqMat, Minv::FakeFmpqMat, B::Vector{T}, cached::Bool = false) where {S, T}
    return get_cached!(AlgAssAbsOrdID, (A, M), cached) do
      O = AlgAssAbsOrd{S, T}(A)
      O.basis_alg = B
      O.basis_matrix = M
      O.basis_mat_inv = Minv
      return O
    end::AlgAssAbsOrd{S, T}
  end

  function AlgAssAbsOrd{S, T}(A::S, M::FakeFmpqMat, cached::Bool = false) where {S, T}
    return get_cached!(AlgAssAbsOrdID, (A, M), cached) do
      O = AlgAssAbsOrd{S, T}(A)
      d = dim(A)
      O.basis_matrix = M
      O.basis_alg = Vector{T}(undef, d)
      for i in 1:d
        O.basis_alg[i] = elem_from_mat_row(A, M.num, i, M.den)
      end
      return O
    end::AlgAssAbsOrd{S, T}
  end

  function AlgAssAbsOrd{S, T}(A::S, B::Vector{T}, cached::Bool = false) where {S, T}
    M = basis_matrix(B, FakeFmpqMat)
    return get_cached!(AlgAssAbsOrdID, (A, M), cached) do
      O = AlgAssAbsOrd{S, T}(A)
      O.basis_alg = B
      O.basis_matrix = M
      return O
    end::AlgAssAbsOrd{S, T}
  end
end

const AlgAssAbsOrdID = Dict{Tuple{AbsAlgAss, FakeFmpqMat}, AlgAssAbsOrd}()

mutable struct AlgAssAbsOrdElem{S, T} <: RingElem
  elem_in_algebra::T
  coordinates::Vector{fmpz}
  has_coord::Bool # needed for mul!
  parent::AlgAssAbsOrd{S, T}

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_algebra = algebra(O)()
    z.coordinates = Vector{fmpz}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}, a::T) where {S, T}
    z = new{S, T}()
    z.elem_in_algebra = a
    z.parent = O
    z.coordinates = Vector{fmpz}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}, arr::Vector{fmpz}) where {S, T}
    z = new{S, T}()
    z.elem_in_algebra = dot(O.basis_alg, arr)
    z.coordinates = arr
    z.parent = O
    z.has_coord = true
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}, a::T, arr::Vector{fmpz}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_algebra = a
    z.coordinates = arr
    z.has_coord = true
    return z
  end
end

################################################################################
#
#  AlgAssAbsOrdIdl
#
################################################################################

mutable struct AlgAssAbsOrdIdl{S, T}
  algebra::S

  basis::Vector{T} # Basis of the ideal as array of elements of the algebra
  # The basis matrix is in the BASIS of the ALGEBRA!
  basis_matrix::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat

  # Basis matrices with respect to orders
  basis_matrix_wrt::Dict{AlgAssAbsOrd{S, T}, FakeFmpqMat}

  # Left and right order:
  # The largest orders of which the ideal is a left resp. right ideal.
  left_order::AlgAssAbsOrd{S, T}
  right_order::AlgAssAbsOrd{S, T}

  # Any order contained in the left or right order, that is, an order of which
  # the ideal is a (possibly fractional) ideal.
  order::AlgAssAbsOrd{S, T}
  gens::Vector{T}    # Generators of the ideal w. r. t. order

  # isleft and isright with respect to `order`
  isleft::Int                      # 0 Not known
                                   # 1 Known to be a left ideal
                                   # 2 Known not to be a left ideal
  isright::Int                     # as for isleft

  iszero::Int                      # 0: don't know, 1: known to be zero, 2: known to be not zero

  norm::Dict{AlgAssAbsOrd{S, T}, fmpq} # The ideal has different norms with respect
                                       # to different orders
  normred::Dict{AlgAssAbsOrd{S, T}, fmpq}

  function AlgAssAbsOrdIdl{S, T}(A::S) where { S <: AbsAlgAss, T <: AbsAlgAssElem }
    r = new{S, T}()
    r.algebra = A
    r.isleft = 0
    r.isright = 0
    r.iszero = 0
    r.basis_matrix_wrt = Dict{AlgAssAbsOrd{S, T}, FakeFmpqMat}()
    r.norm = Dict{AlgAssAbsOrd{S, T}, fmpq}()
    r.normred = Dict{AlgAssAbsOrd{S, T}, fmpq}()
    return r
  end

  function AlgAssAbsOrdIdl{S, T}(A::S, M::FakeFmpqMat) where { S <: AbsAlgAss, T <: AbsAlgAssElem }
    r = AlgAssAbsOrdIdl{S, T}(A)
    r.basis_matrix = M
    return r
  end
end

mutable struct AlgAssAbsOrdIdlSet{S, T}
  order::AlgAssAbsOrd{S, T}

  function AlgAssAbsOrdIdlSet{S, T}(O::AlgAssAbsOrd{S, T}) where {S, T}
    z = new{S, T}(O)
    return z
  end
end

function AlgAssAbsOrdIdlSet(O::AlgAssAbsOrd{S, T}) where {S, T}
  return AlgAssAbsOrdIdlSet{S, T}(O)
end

################################################################################
#
#  AlgAssAbsOrdQuoRing / AlgAssAbsOrdQuoRingElem
#
################################################################################

const AlgAssAbsOrdQuoRing{S, T} = AbsOrdQuoRing{AlgAssAbsOrd{S, T}, AlgAssAbsOrdIdl{S, T}} where {S, T}

const AlgAssAbsOrdQuoRingElem{S, T} = AbsOrdQuoRingElem{AlgAssAbsOrd{S, T}, AlgAssAbsOrdIdl{S, T}, AlgAssAbsOrdElem{S, T}} where {S, T}
