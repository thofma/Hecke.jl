export AlgAss, AlgAssElem, AlgGrp, AlgGrpElem

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
  iscommutative::Int       # 0: don't know
                           # 1: known to be commutative
                           # 2: known to be not commutative
  basis#::Vector{AlgAssElem{T, AlgAss{T}}
  gens#::Vector{AlgAssElem{T, AlgAss{T}} # "Small" number of algebra generators
  trace_basis_elem::Vector{T}
  issimple::Int

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
    return A
  end

  function AlgAss{T}(R::Ring, mult_table::Array{T, 3}, one::Vector{T}) where {T}
    A = AlgAss{T}(R)
    A.mult_table = mult_table
    A.one = one
    return A
  end

  function AlgAss{T}(R::Ring, mult_table::Array{T, 3}) where {T}
    A = AlgAss{T}(R)
    A.mult_table = mult_table
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
#  AlgAssAbsOrd / AlgAssAbsOrdElem / AlgAssAbsOrdIdl
#
################################################################################

# Orders in algebras over the rationals
mutable struct AlgAssAbsOrd{S, T} <: Ring
  algebra::S                       # Algebra containing the order
  dim::Int
  basis#::Vector{AlgAssAbsOrdElem{S, T}}
  basis_alg::Vector{T}             # Basis as array of elements of the algebra
  basis_mat::FakeFmpqMat           # Basis matrix of order wrt basis of the algebra
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

  function AlgAssAbsOrd{S}(A::S) where {S}
    O = new{S, elem_type(S)}()
    O.algebra = A
    O.dim = dim(A)
    O.ismaximal = 0
    return O
  end

  function AlgAssAbsOrd{S, T}(A::S, basis::Vector{T}) where {S, T}
    # "Default" constructor with default values.
    r = AlgAssAbsOrd{S}(A)
    @assert length(basis) == r.dim
    r.basis_alg = basis
    r.basis_mat = basis_mat(basis)
    r.basis_mat_inv = inv(r.basis_mat)
    return r
  end

  function AlgAssAbsOrd{S}(A::S, basis_mat::FakeFmpqMat) where {S}
    r = AlgAssAbsOrd{S}(A)
    d = dim(A)
    r.basis_mat = basis_mat
    r.basis_alg = Vector{elem_type(S)}(undef, rows(basis_mat))
    for i in 1:d
      r.basis_alg[i] = elem_from_mat_row(A, basis_mat.num, i, basis_mat.den)
    end
    r.basis_mat_inv = inv(basis_mat)
    return r
  end
end

mutable struct AlgAssAbsOrdElem{S, T} <: RingElem
  elem_in_algebra::T
  elem_in_basis::Vector{fmpz}
  parent::AlgAssAbsOrd{S, T}

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_algebra = algebra(O)()
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}, a::T) where {S, T}
    z = new{S, T}()
    z.elem_in_algebra = a
    z.parent = O
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}, a::T, arr::Vector{fmpz}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_algebra = a
    z.elem_in_basis = arr
    return z
  end

  function AlgAssAbsOrdElem{S, T}(O::AlgAssAbsOrd{S, T}, arr::Vector{fmpz}) where {S, T}
    z = new{S, T}()
    z.elem_in_algebra = dot(O.basis_alg, arr)
    z.elem_in_basis = arr
    z.parent = O
    return z
  end
end

mutable struct AlgAssAbsOrdIdl{S, T}
  order::AlgAssAbsOrd                     # Order containing it
  basis::Vector{AlgAssAbsOrdElem{S, T}}   # Basis of the ideal as array of elements of the order
  basis_mat::fmpz_mat                     # Basis matrix of ideal wrt basis of the order
  basis_mat_inv::FakeFmpqMat
  gens::Vector{AlgAssAbsOrdElem{S, T}}    # Generators of the ideal

  function AlgAssAbsOrdIdl{S, T}(O::AlgAssAbsOrd{S, T}, M::fmpz_mat) where {S, T}
    r = new{S, T}()
    r.order = O
    d = O.dim
    r.basis = Vector{AlgAssAbsOrdElem{S, T}}(undef, d)
    for i = 1:d
      r.basis[i] = elem_from_mat_row(O, M, i)
    end
    r.basis_mat = M
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
