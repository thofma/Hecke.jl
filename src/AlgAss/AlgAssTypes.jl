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

mutable struct AlgAssOrd 
  A::AlgAss{fmpq}                  # CSA containing it
  dim::Int
  basis_alg::Vector{AlgAssElem{fmpq}}    # Basis as array of elements of the algebra
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


  function AlgAssOrd(a::AlgAss{fmpq}, basis::Array{AlgAssElem{fmpq},1})
    # "Default" constructor with default values.
    r = new()
    r.A=a
    r.dim=size(a.mult_table,1)
    @assert length(basis)==r.dim
    r.basis_alg=basis
    r.basis_mat=basis_mat(basis)
    r.basis_mat_inv=inv(r.basis_mat)
    r.ismaximal = 0
    return r
  end
  
  function AlgAssOrd(a::AlgAss{fmpq}, mat::FakeFmpqMat)
    r = new()
    r.A=a
    r.dim=size(a.mult_table,1)
    r.basis_alg=Array{AlgAssElem{fmpq},1}(rows(mat))
    for i=1:length(r.basis_alg)
      r.basis_alg[i]=elem_from_mat_row(a,mat.num, i, mat.den)
    end
    r.basis_mat=mat
    r.ismaximal = 0
    return r
  end
  
end

mutable struct AlgAssOrdElem
  elem_in_algebra::AlgAssElem{fmpq}
  elem_in_basis::Vector{fmpz}
  parent::AlgAssOrd

  function AlgAssOrdElem(O::AlgAssOrd, a::AlgAssElem)
    z = new()
    z.elem_in_algebra = a
    z.parent = O
    return z
  end

  function AlgAssOrdElem(O::AlgAssOrd, a::AlgAssElem, arr::Array{fmpz, 1})
    z = new()
    z.parent = O
    z.elem_in_algebra = a
    z.elem_in_basis = arr
    return z
  end

  function AlgAssOrdElem(O::AlgAssOrd, arr::Array{fmpz, 1})
    z = new()
    #z.elem_in_algebra = dot(O.basis_alg, arr)
    z.elem_in_basis = arr
    z.parent = O
    return z
  end

end

mutable struct AlgAssOrdIdl
  O::AlgAssOrd                     # Order containing it
  basis_alg::Vector{AlgAssOrdElem} # Basis of the ideal as array of elements of the order
  basis_mat::fmpz_mat              # Basis matrix of ideal wrt basis of the order
  gens::Vector{AlgAssOrdElem}      # Generators of the ideal 
  
  function AlgAssOrdIdl(a::AlgAssOrd, basis::Array{AlgAssOrdElem,1})
    # "Default" constructor with default values.
    r = new()
    r.O=a
    r.basis_alg=basis
    r.basis_mat=zero_matrix(FlintZZ, a.dim, a.dim)
    for i=1:a.dim
      for j=1:a.dim
        r.basis_mat[i,j]=basis[i].elem_in_basis[j]
      end
    end
    return r
  end

  function AlgAssOrdIdl(a::AlgAssOrd, M::fmpz_mat)
    r = new()
    r.O=a
    r.basis_alg=Array{AlgAssOrdElem,1}(a.dim)
    for i=1:a.dim
      r.basis_alg[i]=elem_from_mat_row(a,M,i)
    end
    r.basis_mat=M
    return r
  end
end

