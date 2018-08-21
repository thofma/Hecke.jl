mutable struct AlgAss{T} <: Ring
  base_ring::Ring
  mult_table::Array{T, 3} # e_i*e_j = sum_k mult_table[i, j, k]*e_k
  one::Array{T, 1}
  iscommutative::Int       # 0: don't know
                           # 1 known to be commutative
                           # 2 known to be not commutative
  trace_basis_elem::Array{T, 1}

  function AlgAss{T}(R::Ring) where {T}
    A = new{T}()
    A.base_ring = R
    A.iscommutative = 0
    return A
  end

  function AlgAss{T}(R::Ring, mult_table::Array{T, 3}, one::Array{T, 1}) where {T}
    A = new{T}()
    A.base_ring = R
    A.mult_table = mult_table
    A.one = one
    A.iscommutative = 0
    return A
  end

  function AlgAss{T}(R::Ring, mult_table::Array{T, 3}) where {T}
    A = new{T}()
    A.base_ring = R
    A.mult_table = mult_table
    A.iscommutative = 0
    return A
  end
end

mutable struct AlgAssElem{T} <: RingElem
  parent::AlgAss{T}
  coeffs::Array{T, 1}

  function AlgAssElem{T}(A::AlgAss{T}) where {T}
    z = new{T}()
    z.parent = A
    z.coeffs = Array{T, 1}(size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  # This does not make a copy of coeffs
  function AlgAssElem{T}(A::AlgAss{T}, coeffs::Array{T, 1}) where{T}
    z = new{T}()
    z.parent = A
    z.coeffs = coeffs
    return z
  end
end

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
                                   
  trace_mat::fmpz_mat              # The reduced trace matrix (if known)

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
    r.basis_alg = Vector{elem_type(S)}(rows(basis_mat))
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
  basis_alg::Vector{AlgAssAbsOrdElem{S, T}} # Basis of the ideal as array of elements of the order
  basis_mat::fmpz_mat              # Basis matrix of ideal wrt basis of the order
  gens::Vector{AlgAssAbsOrdElem{S, T}}# Generators of the ideal 
  
  function AlgAssAbsOrdIdl{S, T}(O::AlgAssAbsOrd{S, T}, basis::Vector{AlgAssAbsOrdElem{S, T}}) where {S, T}
    r = new{S, T}()
    d = O.dim
    r.order = a
    r.basis_alg = basis
    r.basis_mat = zero_matrix(FlintZZ, d, d)
    for i = 1:d
      el = elem_in_basis(basis[i])
      for j = 1:d
        r.basis_mat[i,j] = el[j]
      end
    end
    return r
  end

  function AlgAssAbsOrdIdl{S, T}(O::AlgAssAbsOrd{S, T}, M::fmpz_mat) where {S, T}
    r = new{S, T}()
    r.order = O
    r.basis_mat = M
    return r
  end
end

