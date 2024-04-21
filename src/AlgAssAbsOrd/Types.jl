################################################################################
#
#  AlgAssAbsOrd / AlgAssAbsOrdElem
#
################################################################################

# Orders in algebras over the rationals
@attributes mutable struct AlgAssAbsOrd{S, T} <: NCRing
  algebra::S                       # Algebra containing the order
  dim::Int
  basis#::Vector{AlgAssAbsOrdElem{S, T}}
  basis_alg::Vector{T}             # Basis as array of elements of the algebra
  basis_matrix::FakeFmpqMat           # Basis matrix of order wrt basis of the algebra
  basis_mat_inv::FakeFmpqMat       # Inverse of basis matrix
  gen_index::QQFieldElem                  # The det of basis_mat_inv as QQFieldElem
  index::ZZRingElem                      # The det of basis_mat_inv
                                   # (this is the index of the equation order
                                   #  in the given order)
  det_basis_matrix::QQFieldElem
  disc::ZZRingElem                       # Discriminant

  is_maximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  #trace_mat::ZZMatrix              # The reduced trace matrix (if known)
  trred_matrix::ZZMatrix

  picard_group#::MapPicardGrp

  tcontain::FakeFmpqMat

  isnice::Bool
  nice_order#Tuple{AlgAssAbsOrd, T}
  nice_order_ideal::ZZRingElem

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

const AlgAssAbsOrdID = AbstractAlgebra.CacheDictType{Tuple{AbstractAssociativeAlgebra, FakeFmpqMat}, AlgAssAbsOrd}()

@attributes mutable struct AlgAssAbsOrdElem{S, T} <: NCRingElem
  elem_in_algebra::T
  coordinates::Vector{ZZRingElem}
  has_coord::Bool # needed for mul!
  parent::AlgAssAbsOrd{S, T}

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_algebra = algebra(O)()
    z.coordinates = Vector{ZZRingElem}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}, a::T) where {S, T}
    z = new{S, T}()
    z.elem_in_algebra = a
    z.parent = O
    z.coordinates = Vector{ZZRingElem}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}, arr::Vector{ZZRingElem}) where {S, T}
    z = new{S, T}()
    z.elem_in_algebra = degree(O) == 0 ? zero(algebra(O)) : dot(O.basis_alg, arr)
    z.coordinates = arr
    z.parent = O
    z.has_coord = true
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}, a::T, arr::Vector{ZZRingElem}) where {S, T}
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

@attributes mutable struct AlgAssAbsOrdIdl{S, T}
  algebra::S

  basis::Vector{T} # Basis of the ideal as array of elements of the algebra
  # The basis matrix is in the BASIS of the ALGEBRA!
  basis_matrix::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat
  det_basis_matrix::QQFieldElem

  # Store whether the ideal has full rank
  # -1 no, 0 don't know, 1 yes
  full_rank::Int
  # rank
  rank::Int

  # In case the ideal has full rank, store a multiple of the largest elementary
  # divisor of the numerator of the basis matrix
  eldiv_mul::ZZRingElem

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

  norm::Dict{AlgAssAbsOrd{S, T}, QQFieldElem} # The ideal has different norms with respect
                                       # to different orders
  normred::Dict{AlgAssAbsOrd{S, T}, QQFieldElem}

  function AlgAssAbsOrdIdl{S, T}(A::S) where { S <: AbstractAssociativeAlgebra, T <: AbstractAssociativeAlgebraElem }
    r = new{S, T}()
    r.algebra = A
    r.isleft = 0
    r.isright = 0
    r.iszero = 0
    r.basis_matrix_wrt = Dict{AlgAssAbsOrd{S, T}, FakeFmpqMat}()
    r.norm = Dict{AlgAssAbsOrd{S, T}, QQFieldElem}()
    r.normred = Dict{AlgAssAbsOrd{S, T}, QQFieldElem}()
    r.full_rank = 0
    r.rank = -1
    return r
  end

  function AlgAssAbsOrdIdl{S, T}(A::S, M::FakeFmpqMat) where { S <: AbstractAssociativeAlgebra, T <: AbstractAssociativeAlgebraElem }
    r = AlgAssAbsOrdIdl{S, T}(A)
    r.basis_matrix = M
    n = nrows(M)
    if is_square(M)
      if is_lower_triangular(M)
        i = 0
        while i < n && is_zero_row(M, i + 1)
          i += 1
        end
        r.full_rank = (i == 0) ? 1 : -1
        r.rank = n - i
        if r.full_rank == 1
          r.eldiv_mul = reduce(*, diagonal(numerator(M, copy = false)), init = one(ZZ))
        else
          r.eldiv_mul = zero(ZZ)
        end
      elseif is_upper_triangular(M)
        i = n + 1
        while i > 0 && is_zero_row(M, i - 1)
          i -= 1
        end
        r.rank = i - 1
        r.full_rank = (i == n + 1) ? 1 : -1
        if r.full_rank == 1
          r.eldiv_mul = reduce(*, diagonal(numerator(M, copy = false)), init = one(ZZ))
        else
          r.eldiv_mul = zero(ZZ)
        end
      else
        error("basis matrix not triangular matrix")
      end
    else
      r.full_rank = 0
    end

    return r
  end
end

@attributes mutable struct AlgAssAbsOrdIdlSet{S, T}
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
