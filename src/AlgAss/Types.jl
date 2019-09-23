export AlgAss, AlgAssElem, AlgGrp, AlgGrpElem, AlgMat, AlgMatElem

abstract type AbsAlgAss{T} <: Ring end

abstract type AbsAlgAssElem{T} <: RingElem end

################################################################################
#
#  AlgAss / AlgAssElem
#
################################################################################

# Associative algebras defined by structure constants (multiplication table)
mutable struct AlgAss{T} <: AbsAlgAss{T}
  base_ring::Ring
  mult_table::Array{T, 3} # e_i*e_j = sum_k mult_table[i, j, k]*e_k
  one::Vector{T}
  has_one::Bool
  iszero::Bool
  iscommutative::Int       # 0: don't know
                           # 1: known to be commutative
                           # 2: known to be not commutative
  basis#::Vector{AlgAssElem{T, AlgAss{T}}
  gens#::Vector{AlgAssElem{T, AlgAss{T}} # "Small" number of algebra generators
  trace_basis_elem::Vector{T}
  issimple::Int
  issemisimple::Int

  decomposition#::Vector{Tuple{AlgAss{T}, mor(AlgAss{T}, AlgAss{T})}
  center#Tuple{AlgAss{T}, mor(AlgAss{T}, AlgAss{T})
  maps_to_numberfields
  maximal_order

  # Constructor with default values
  function AlgAss{T}(R::Ring) where {T}
    A = new{T}()
    A.base_ring = R
    A.iscommutative = 0
    A.issimple = 0
    A.issemisimple = 0
    return A
  end

  function AlgAss{T}(R::Ring, mult_table::Array{T, 3}, one::Vector{T}) where {T}
    A = AlgAss{T}(R)
    A.mult_table = mult_table
    A.one = one
    A.has_one = true
    A.iszero = (size(mult_table, 1) == 0)
    return A
  end

  function AlgAss{T}(R::Ring, mult_table::Array{T, 3}) where {T}
    A = AlgAss{T}(R)
    A.mult_table = mult_table
    A.iszero = (size(mult_table, 1) == 0)
    return A
  end
end

mutable struct AlgAssElem{T, S} <: AbsAlgAssElem{T}
  parent::S
  coeffs::Array{T, 1}

  function AlgAssElem{T, S}(A::S) where {T, S}
    z = new{T, S}()
    z.parent = A
    z.coeffs = Array{T, 1}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function AlgAssElem{T, S}(A::AlgAss{T}) where {T, S}
    z = new{T, AlgAss{T}}()
    z.parent = A
    z.coeffs = Array{T, 1}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  # This does not make a copy of coeffs
  function AlgAssElem{T, S}(A::S, coeffs::Array{T, 1}) where {T, S}
    z = new{T, AlgAss{T}}()
    z.parent = A
    z.coeffs = coeffs
    return z
  end
end

################################################################################
#
#  AlgGrp / AlgGrpElem
#
################################################################################

# Group rings
mutable struct AlgGrp{T, S, R} <: AbsAlgAss{T}
  base_ring::Ring
  group::S
  group_to_base::Dict{R, Int}
  one::Vector{T}
  basis#::Vector{AlgAssElem{T, AlgAss{T}}
  gens#::Vector{AlgAssElem{T, AlgAss{T}} # "Small" number of algebra generators
  mult_table::Array{Int, 2} # b_i * b_j = b_(mult_table[i, j])
  iscommutative::Int
  trace_basis_elem::Array{T, 1}
  issimple::Int
  issemisimple::Int

  decomposition
  center
  maps_to_numberfields
  maximal_order

  function AlgGrp(K::Ring, G::GrpAbFinGen)
    A = AlgGrp(K, G, op = +)
    A.iscommutative = true
    return A
  end

  function AlgGrp(K::Ring, G; op = *)
    A = new{elem_type(K), typeof(G), elem_type(G)}()
    A.iscommutative = 0
    A.issimple = 0
    A.issemisimple = 0
    A.base_ring = K
    A.group = G
    d = Int(order(G))
    A.group_to_base = Dict{elem_type(G), Int}()
    A.mult_table = zeros(Int, d, d)

    for (i, g) in enumerate(G)
      A.group_to_base[deepcopy(g)] = i
    end

    v = Vector{elem_type(K)}(undef, d)
    for i in 1:d
      v[i] = zero(K)
    end
    v[1] = one(K)

    A.one = v

    for (i, g) in enumerate(G)
      for (j, h) in enumerate(G)
        l = op(g, h)
        A.mult_table[i, j] = A.group_to_base[l]
      end
    end

    @assert all(A.mult_table[1, i] == i for i in 1:dim(A))

    return A
  end
end

mutable struct AlgGrpElem{T, S} <: AbsAlgAssElem{T}
  parent::S
  coeffs::Array{T, 1}

  function AlgGrpElem{T, S}(A::S) where {T, S}
    z = new{T, S}()
    z.parent = A
    z.coeffs = Array{T, 1}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function AlgGrpElem{T, S}(A::S, g::U) where {T, S, U}
    return A[A.group_to_base[g]]
  end

  # This does not make a copy of coeffs
  function AlgGrpElem{T, S}(A::S, coeffs::Array{T, 1}) where {T, S}
    z = new{T, S}()
    z.parent = A
    z.coeffs = coeffs
    return z
  end
end

################################################################################
#
#  AbsAlgAssIdl
#
################################################################################

# S is the type of the algebra, T = elem_type(S) and U is the type of matrices
# over the base ring of the algebra
mutable struct AbsAlgAssIdl{S, T, U}
  algebra::S
  basis::Vector{T}
  basis_matrix::U

  isleft::Int                      # 0 Not known
                                   # 1 Known to be a left ideal
                                   # 2 Known not to be a left ideal
  isright::Int                     # as for isleft

  iszero::Int

  function AbsAlgAssIdl{S, T, U}(A::S) where {S, T, U}
    I = new{S, T, U}()
    I.algebra = A
    I.isleft = 0
    I.isright = 0
    I.iszero = 0
    return I
  end

  function AbsAlgAssIdl{S, U}(A::S, M::U) where {S, U}
    I = new{S, elem_type(S), U}()
    I.algebra = A
    I.basis_matrix = M
    I.isleft = 0
    I.isright = 0
    I.iszero = 0
    return I
  end
end

################################################################################
#
#  AlgAssAbsOrd / AlgAssAbsOrdElem / AlgAssAbsOrdIdl / AlgAssAbsOrdFracIdl
#
################################################################################

# Orders in algebras over the rationals
mutable struct AlgAssAbsOrd{S, T} <: Ring
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

  ismaximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  #trace_mat::fmpz_mat              # The reduced trace matrix (if known)
  trred_matrix::fmpz_mat

  picard_group#::MapPicardGrp
  unit_group#::MapUnitGrp

  tcontain::FakeFmpqMat

  function AlgAssAbsOrd{S, T}(A::S) where {S, T}
    # "Default" constructor with default values.
    O = new{S, T}()
    O.algebra = A
    O.dim = dim(A)
    O.ismaximal = 0
    O.tcontain = FakeFmpqMat(zero_matrix(FlintZZ, 1, dim(A)))
    return O
  end

  function AlgAssAbsOrd{S, T}(A::S, M::FakeFmpqMat, Minv::FakeFmpqMat, B::Vector{T}, cached::Bool = false) where {S, T}
    if cached && haskey(AlgAssAbsOrdID, (A, M))
      return AlgAssAbsOrdID[(A, M)]
    end
    O = AlgAssAbsOrd{S, T}(A)
    O.basis_alg = B
    O.basis_matrix = M
    O.basis_mat_inv = Minv
    if cached
      AlgAssAbsOrdID[(A, M)] = O
    end
    return O
  end

  function AlgAssAbsOrd{S, T}(A::S, M::FakeFmpqMat, cached::Bool = false) where {S, T}
    if cached && haskey(AlgAssAbsOrdID, (A, M))
      return AlgAssAbsOrdID[(A, M)]
    end
    O = AlgAssAbsOrd{S, T}(A)
    d = dim(A)
    O.basis_matrix = M
    O.basis_alg = Vector{T}(undef, d)
    for i in 1:d
      O.basis_alg[i] = elem_from_mat_row(A, M.num, i, M.den)
    end
    if cached
      AlgAssAbsOrdID[(A, M)] = O
    end
    return O
  end

  function AlgAssAbsOrd{S, T}(A::S, B::Vector{T}, cached::Bool = false) where {S, T}
    O = AlgAssAbsOrd{S, T}(A)
    M = basis_matrix(B, FakeFmpqMat)
    if cached && haskey(AlgAssAbsOrdID, (A, M))
      return AlgAssAbsOrdID[(A, M)]
    end
    O.basis_alg = B
    O.basis_matrix = M
    if cached
      AlgAssAbsOrdID[(A, M)] = O
    end
    return O
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

mutable struct AlgAssAbsOrdIdl{S, T}
  order::AlgAssAbsOrd                     # Order containing it
  basis::Vector{AlgAssAbsOrdElem{S, T}}   # Basis of the ideal as array of elements of the order
  basis_matrix::fmpz_mat                     # Basis matrix of ideal wrt basis of the order
  basis_mat_inv::FakeFmpqMat
  gens::Vector{AlgAssAbsOrdElem{S, T}}    # Generators of the ideal

  isleft::Int                      # 0 Not known
                                   # 1 Known to be a left ideal
                                   # 2 Known not to be a left ideal
  isright::Int                     # as for isleft

  iszero::Int                             # 0: don't know, 1: known to be zero, 2: known to be not zero

  norm::fmpz
  normred::fmpz

  function AlgAssAbsOrdIdl{S, T}(O::AlgAssAbsOrd{S, T}) where {S, T}
    r = new{S, T}()
    r.order = O
    r.isleft = 0
    r.isright = 0
    r.iszero = 0
    return r
  end

  function AlgAssAbsOrdIdl{S, T}(O::AlgAssAbsOrd{S, T}, M::fmpz_mat) where {S, T}
    r = new{S, T}()
    r.order = O
    d = O.dim
    r.basis_matrix = M
    r.isleft = 0
    r.isright = 0
    r.iszero = 0
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

mutable struct AlgAssAbsOrdFracIdl{S, T}
  order::AlgAssAbsOrd{S, T}
  num::AlgAssAbsOrdIdl{S, T}
  den::fmpz
  basis_matrix::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat

  function AlgAssAbsOrdFracIdl{S, T}(O::AlgAssAbsOrd{S, T}, a::AlgAssAbsOrdIdl{S, T}, b::fmpz) where {S, T}
    z = new{S, T}()
    z.order = O
    z.basis_matrix = FakeFmpqMat(basis_matrix(a), deepcopy(b))
    z.num = a
    z.den = b
    return z
  end

  function AlgAssAbsOrdFracIdl{S, T}(O::AlgAssAbsOrd{S, T}, M::FakeFmpqMat) where {S, T}
    z = new{S, T}()
    z.order = O
    z.basis_matrix = M
    return z
  end
end

mutable struct AlgAssAbsOrdFracIdlSet{S, T}
  order::AlgAssAbsOrd{S, T}

  function AlgAssAbsOrdFracIdlSet{S, T}(O::AlgAssAbsOrd{S, T}) where {S, T}
    z = new{S, T}(O)
    return z
  end
end

function AlgAssAbsOrdFracIdlSet(O::AlgAssAbsOrd{S, T}) where {S, T}
  return AlgAssAbsOrdFracIdlSet{S, T}(O)
end

################################################################################
#
#  AlgAssAbsOrdQuoRing / AlgAssAbsOrdQuoRingElem
#
################################################################################

const AlgAssAbsOrdQuoRing{S, T} = AbsOrdQuoRing{AlgAssAbsOrd{S, T}, AlgAssAbsOrdIdl{S, T}} where {S, T}

const AlgAssAbsOrdQuoRingElem{S, T} = AbsOrdQuoRingElem{AlgAssAbsOrd{S, T}, AlgAssAbsOrdIdl{S, T}, AlgAssAbsOrdElem{S, T}} where {S, T}

################################################################################
#
#  AlgMat / AlgMatElem
#
################################################################################

# T == elem_type(base_ring), S == dense_matrix_type(coefficient_ring)
mutable struct AlgMat{T, S} <: AbsAlgAss{T}
  base_ring::Ring
  coefficient_ring::Ring
  one::S
  basis
  basis_matrix # matrix over the base_ring
  dim::Int
  degree::Int
  issimple::Int
  issemisimple::Int
  iscommutative::Int
  decomposition
  maximal_order
  mult_table::Array{T, 3} # e_i*e_j = sum_k mult_table[i, j, k]*e_k
  canonical_basis::Int # whether A[(j - 1)*n + i] == E_ij, where E_ij = (e_kl)_kl with e_kl = 1 if i =k and j = l and e_kl = 0 otherwise.
  center#Tuple{AlgAss{T}, mor(AlgAss{T}, AlgAss{T})
  trace_basis_elem::Vector{T}

  function AlgMat{T, S}(R::Ring) where {T, S}
    A = new{T, S}()
    A.base_ring = R
    A.coefficient_ring = R
    A.issimple = 0
    A.issemisimple = 0
    A.iscommutative = 0
    A.canonical_basis = 0
    return A
  end

  function AlgMat{T, S}(R1::Ring, R2::Ring) where {T, S}
    A = new{T, S}()
    A.base_ring = R1
    A.coefficient_ring = R2
    A.issimple = 0
    A.issemisimple = 0
    A.iscommutative = 0
    A.canonical_basis = 0
    return A
  end
end

mutable struct AlgMatElem{T, S, Mat} <: AbsAlgAssElem{T}
  parent::S
  matrix::Mat # over the coefficient ring of the parent
  coeffs::Vector{T} # over the base ring of the parent
  has_coeffs::Bool

  function AlgMatElem{T, S, Mat}(A::S) where {T, S, Mat}
    z = new{T, S, Mat}()
    z.parent = A
    z.matrix = zero_matrix(base_ring(A), degree(A), degree(A))
    z.has_coeffs = false
    return z
  end

  function AlgMatElem{T, S, Mat}(A::S, M::Mat) where {T, S, Mat}
    z = new{T, S, Mat}()
    z.parent = A
    z.matrix = M
    z.has_coeffs = false
    return z
  end
end

################################################################################
#
#  AlgAssRelOrd
#
################################################################################

# S is the element type of the base field of the algebra, T the fractional ideal
# type of this field
mutable struct AlgAssRelOrd{S, T} <: Ring
  algebra::AbsAlgAss{S}
  dim::Int
  pseudo_basis::Vector{Tuple{AbsAlgAssElem{S}, T}}
  basis_matrix::Generic.MatSpaceElem{S}
  basis_mat_inv::Generic.MatSpaceElem{S}
  basis_pmatrix::PMat{S, T}

  disc # an integral ideal in the base field

  ismaximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  trred_matrix::Generic.MatSpaceElem{S}

  inv_coeff_ideals::Vector{T}

  function AlgAssRelOrd{S, T}(A::AbsAlgAss{S}) where {S, T}
    z = new{S, T}()
    z.algebra = A
    z.dim = dim(A)
    z.ismaximal = 0
    return z
  end

  function AlgAssRelOrd{S, T}(A::AbsAlgAss{S}, M::PMat{S, T}) where {S, T}
    z = AlgAssRelOrd{S, T}(A)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    return z
  end

  function AlgAssRelOrd{S, T}(A::AbsAlgAss{S}, M::Generic.MatSpaceElem{S}) where {S, T}
    z = AlgAssRelOrd{S, T}(A)
    z.basis_matrix = M
    z.basis_pmatrix = pseudo_matrix(M)
    return z
  end
end

################################################################################
#
#  AlgAssRelOrdElem
#
################################################################################

mutable struct AlgAssRelOrdElem{S, T} <: RingElem
  parent::AlgAssRelOrd{S, T}
  elem_in_algebra::AbsAlgAssElem{S}
  coordinates::Vector{S}
  has_coord::Bool

  function AlgAssRelOrdElem{S, T}(O::AlgAssRelOrd{S, T}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_algebra = zero(algebra(O))
    z.coordinates = Vector{S}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function AlgAssRelOrdElem{S, T}(O::AlgAssRelOrd{S, T}, a::AbsAlgAssElem{S}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_algebra = a
    z.coordinates = Vector{S}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function AlgAssRelOrdElem{S, T}(O::AlgAssRelOrd{S, T}, a::AbsAlgAssElem{S}, arr::Vector{S}) where {S, T}
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
#  AlgAssRelOrdIdl
#
################################################################################

mutable struct AlgAssRelOrdIdl{S, T}
  order::AlgAssRelOrd{S, T}

  left_order::AlgAssRelOrd{S, T} # the largest order of which the ideal is a left ideal
  right_order::AlgAssRelOrd{S, T} # as above

  pseudo_basis::Vector{Tuple{AbsAlgAssElem{S}, T}}
  # The basis matrices are in the basis of `order`
  basis_pmatrix::PMat{S, T}
  basis_matrix::Generic.MatSpaceElem{S}
  basis_mat_inv::Generic.MatSpaceElem{S}

  # isleft and isright with respect to `order`
  isleft::Int                      # 0 Not known
                                   # 1 Known to be a left ideal
                                   # 2 Known not to be a left ideal
  isright::Int                     # as for isleft

  iszero::Int                      # 0: don't know, 1: known to be zero, 2: known to be not zero

  norm
  normred

  function AlgAssRelOrdIdl{S, T}(O::AlgAssRelOrd{S, T}) where {S, T}
    z = new{S, T}()
    z.order = O
    z.isleft = 0
    z.isright = 0
    z.iszero = 0
    return z
  end

  function AlgAssRelOrdIdl{S, T}(O::AlgAssRelOrd{S, T}, M::PMat{S, T}) where {S, T}
    z = AlgAssRelOrdIdl{S, T}(O)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    return z
  end
end

################################################################################
#
#  AlgAssRelOrdFracIdl
#
################################################################################

mutable struct AlgAssRelOrdFracIdl{S, T}
  order::AlgAssRelOrd{S, T}

  left_order::AlgAssRelOrd{S, T} # the largest order of which the ideal is a left ideal
  right_order::AlgAssRelOrd{S, T} # as above

  pseudo_basis::Vector{Tuple{AbsAlgAssElem{S}, T}}
  # The basis matrices are in the basis of `order`
  basis_pmatrix::PMat{S, T}
  basis_matrix::Generic.MatSpaceElem{S}
  basis_mat_inv::Generic.MatSpaceElem{S}
  den::fmpz

  # isleft and isright with respect to `order`
  isleft::Int                      # 0 Not known
                                   # 1 Known to be a left ideal
                                   # 2 Known not to be a left ideal
  isright::Int                     # as for isleft

  iszero::Int                      # 0: don't know, 1: known to be zero, 2: known to be not zero

  norm::T
  normred::T

  function AlgAssRelOrdFracIdl{S, T}(O::AlgAssRelOrd{S, T}) where {S, T}
    z = new{S, T}()
    z.order = O
    z.isleft = 0
    z.isright = 0
    z.iszero = 0
    return z
  end

  function AlgAssRelOrdFracIdl{S, T}(O::AlgAssRelOrd{S, T}, M::PMat{S, T}) where {S, T}
    z = AlgAssRelOrdIdl{S, T}(O)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    return z
  end
end
