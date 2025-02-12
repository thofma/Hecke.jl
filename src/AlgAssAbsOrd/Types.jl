################################################################################
#
#  AlgAssAbsOrd / AlgAssAbsOrdElem
#
################################################################################

# Orders in algebras over the rationals
@attributes mutable struct AlgAssAbsOrd{AlgType, BRingType} <: NCRing
  algebra::AlgType                       # Algebra containing the order
  dim::Int
  base_ring::BRingType #= parent_type(elem_type) =#
  basis#::Vector{elem_type(self)}
  basis_alg#=::Vector{elem_type(algebra_type)}}=#             # Basis as array of elements of the algebra
  basis_matrix#=::dense_matrix_type(elem_type(base_ring(AlgType)))=#           # Basis matrix of order wrt basis of the algebra
  basis_mat_inv       # Inverse of basis matrix
  gen_index                  # The det of basis_mat_inv as QQFieldElem
  index                      # The det of basis_mat_inv (element of base ring)
                                   # (this is the index of the equation order
                                   #  in the given order)
  det_basis_matrix#::QQFieldElem
  disc#::ZZRingElem                       # Discriminant

  is_maximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  #trace_mat::ZZMatrix              # The reduced trace matrix (if known)
  trred_matrix#::ZZMatrix

  picard_group#::MapPicardGrp

  tcontain#::QQMatrix

  isnice::Bool
  nice_order#Tuple{AlgAssAbsOrd, T}
  nice_order_ideal#::ZZRingElem

  function AlgAssAbsOrd{AlgType, BRingType}(A::AlgType, R::BRingType) where {AlgType, BRingType}
    # "Default" constructor with default values.
    O = new{AlgType, BRingType}(A, dim(A), R)
    O.is_maximal = 0
    O.isnice = false
    O.tcontain = zero_matrix(base_ring(A), 1, dim(A))
    return O
  end

  function AlgAssAbsOrd{AlgType, BRingType}(A::AlgType, R::BRingType, M::MatElem, Minv::MatElem, B::Vector, cached::Bool = false) where {AlgType, BRingType}
    return get_cached!(AlgAssAbsOrdID, (A, R, M), cached) do
      O = AlgAssAbsOrd{AlgType, BRingType}(A, R)
      O.basis_alg = B
      O.basis_matrix = M
      O.basis_mat_inv = Minv
      return O
    end::AlgAssAbsOrd{AlgType, BRingType}
  end

  function AlgAssAbsOrd{AlgType, BRingType}(A::AlgType, R::BRingType, M::MatElem, cached::Bool = false) where {AlgType, BRingType}
    return get_cached!(AlgAssAbsOrdID, (A, M), cached) do
      O = AlgAssAbsOrd{AlgType, BRingType}(A, R)
      d = dim(A)
      O.basis_matrix = M
      O.basis_alg = Vector{elem_type(A)}(undef, d)
      for i in 1:d
        O.basis_alg[i] = elem_from_mat_row(A, M, i)
      end
      return O
    end::AlgAssAbsOrd{AlgType, BRingType}
  end

  function AlgAssAbsOrd{AlgType, BRingType}(A::AlgType, R::BRingType, B::Vector, cached::Bool = false) where {AlgType, BRingType}
    M = basis_matrix(B)
    return get_cached!(AlgAssAbsOrdID, (A, R, M), cached) do
      O = AlgAssAbsOrd{AlgType, BRingType}(A, R)
      O.basis_alg = B
      O.basis_matrix = M
      return O
    end::AlgAssAbsOrd{AlgType, BRingType}
  end
end

const AlgAssAbsOrdID = AbstractAlgebra.CacheDictType{Any, AlgAssAbsOrd}()

@attributes mutable struct AlgAssAbsOrdElem{S, T} <: NCRingElem
  elem_in_algebra::T
  coordinates::Vector# elem_type(base_ring(S))
  has_coord::Bool # needed for mul!
  parent::S

  function AlgAssAbsOrdElem{S, T}(O::S) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_algebra = algebra(O)()
    z.coordinates = Vector{elem_type(base_ring(O))}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::S, a::T) where {S, T}
    z = new{S, T}()
    z.elem_in_algebra = a
    z.parent = O
    z.coordinates = Vector{elem_type(base_ring(O))}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::S, arr::Vector) where {S, T}
    z = new{S, T}()
    @assert eltype(arr) === elem_type(base_ring(O))
    z.elem_in_algebra = degree(O) == 0 ? zero(algebra(O)) : dot(O.basis_alg, arr)
    z.coordinates = arr
    z.parent = O
    z.has_coord = true
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::S, a::T, arr::Vector) where {S, T}
    z = new{S, T}()
    @assert eltype(arr) === elem_type(base_ring(O))
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

@attributes mutable struct AlgAssAbsOrdIdl{AlgType, BRingType}
  algebra::AlgType
  base_ring::BRingType

  basis::Vector # Basis of the ideal as array of elements of the algebra
  # The basis matrix is in the BASIS of the ALGEBRA!
  basis_matrix
  basis_mat_inv
  det_basis_matrix

  # Store whether the ideal has full rank
  # -1 no, 0 don't know, 1 yes
  full_rank::Int
  # rank
  rank::Int

  # In case the ideal has full rank, store a multiple of the largest elementary
  # divisor of the numerator of the basis matrix
  eldiv_mul#::ZZRingElem

  # Basis matrices with respect to orders
  basis_matrix_wrt::Dict#{AlgAssAbsOrd{S, T}, QQMatrix}

  # Left and right order:
  # The largest orders of which the ideal is a left resp. right ideal.
  left_order#::AlgAssAbsOrd{S, T}
  right_order#::AlgAssAbsOrd{S, T}

  # Any order contained in the left or right order, that is, an order of which
  # the ideal is a (possibly fractional) ideal.
  order#::AlgAssAbsOrd{S, T}
  gens#::Vector{T}    # Generators of the ideal w. r. t. order

  # isleft and isright with respect to `order`
  isleft::Int                      # 0 Not known
                                   # 1 Known to be a left ideal
                                   # 2 Known not to be a left ideal
  isright::Int                     # as for isleft

  iszero::Int                      # 0: don't know, 1: known to be zero, 2: known to be not zero

  norm#::Dict{AlgAssAbsOrd{S, T}, QQFieldElem} # The ideal has different norms with respect
                                       # to different orders
  normred#::Dict{AlgAssAbsOrd{S, T}, QQFieldElem}

  function AlgAssAbsOrdIdl{AlgType, BRingType}(A::AlgType, R::BRingType) where {AlgType, BRingType}
    r = new{AlgType, BRingType}()
    r.algebra = A
    r.base_ring = R
    r.isleft = 0
    r.isright = 0
    r.iszero = 0
    r.basis_matrix_wrt = Dict{order_type(A, R), dense_matrix_type(base_ring(A))}()
    r.norm = Dict{order_type(A, R), elem_type(base_ring(A))}()
    r.normred = Dict{order_type(A, R), elem_type(base_ring(A))}()
    r.full_rank = 0
    r.rank = -1
    return r
  end

  function AlgAssAbsOrdIdl{AlgType, BRingType}(A::AlgType, R::BRingType, M::MatElem) where {AlgType, BRingType}
    r = AlgAssAbsOrdIdl{AlgType, BRingType}(A, R)
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
          Mn, = integral_split(M, R)
          r.eldiv_mul = reduce(*, diagonal(Mn), init = one(R))
        else
          r.eldiv_mul = zero(R)
        end
      elseif is_upper_triangular(M)
        i = n + 1
        while i > 0 && is_zero_row(M, i - 1)
          i -= 1
        end
        r.rank = i - 1
        r.full_rank = (i == n + 1) ? 1 : -1
        if r.full_rank == 1
          Mn, = integral_split(M, R)
          r.eldiv_mul = reduce(*, diagonal(Mn), init = one(R))
        else
          r.eldiv_mul = zero(R)
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

@attributes mutable struct AlgAssAbsOrdIdlSet{S}
  order::S

  function AlgAssAbsOrdIdlSet{S}(O::S) where {S}
    z = new{S}(O)
    return z
  end
end

function AlgAssAbsOrdIdlSet(O::S) where {S}
  return AlgAssAbsOrdIdlSet{S}(O)
end

################################################################################
#
#  AlgAssAbsOrdQuoRing / AlgAssAbsOrdQuoRingElem
#
################################################################################

const AlgAssAbsOrdQuoRing{S, T} = AbsOrdQuoRing{S, T} where {S, T}

const AlgAssAbsOrdQuoRingElem{S, U, V} = AbsOrdQuoRingElem{S, U, V} where {S, U, V}
