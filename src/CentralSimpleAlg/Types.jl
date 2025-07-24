abstract type AbstractCentralSimpleAlgebra{T} <: AbstractAssociativeAlgebra{T} end

abstract type AbstractCentralSimpleAlgebraElem{T} <: AbstractAssociativeAlgebraElem{T} end

@attributes mutable struct QuaternionAlgebra{T} <: AbstractCentralSimpleAlgebra{T}
  base_ring::Ring
  mult_table::Array{T,3}
  one::Vector{T}
  zero::Vector{T}
  std::Tuple{T,T}
  basis#::Vector{AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}
  is_simple::Int
  trace_basis_elem::Vector{T}
  maximal_order
  std_inv# standard involution

  function QuaternionAlgebra{T}() where {T}
    z = new{T}()
    if T <: Field
      z.is_simple = 1
    else
      z.is_simple = 0
    end
    return z
  end
end

mutable struct CentralSimpleAlgebraElem{T,S} <: AbstractCentralSimpleAlgebraElem{T}
  parent::S
  coeffs::Vector{T}

  function CentralSimpleAlgebraElem{T,S}(A::S) where {T,S}
    z = new{T,S}()
    z.parent = A
    z.coeffs = Vector{T}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function CentralSimpleAlgebraElem{T,S}(A::QuaternionAlgebra{T}) where {T,S}
    z = new{T,QuaternionAlgebra{T}}()
    z.parent = A
    z.coeffs = Vector{T}(undef, 4)
    for i = 1:4
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function CentralSimpleAlgebraElem{T,S}(A::S, coeffs::Vector{T}) where {T,S}
    z = new{T,S}()
    z.parent = A
    z.coeffs = coeffs
    return z
  end
end


################################################################################
#
#  MatAlgebra / MatAlgebraElem
#
################################################################################

# T == elem_type(base_ring), S == dense_matrix_type(coefficient_ring)
@attributes mutable struct MatAlgebra{T,S<:MatElem} <: AbstractCentralSimpleAlgebra{T}
  base_ring::Ring
  coefficient_ring::NCRing
  one::S
  basis
  basis_matrix # matrix over the base_ring
  basis_matrix_rref
  basis_matrix_solve_ctx
  dim::Int
  degree::Int
  is_simple::Int
  issemisimple::Int
  is_commutative::Int
  decomposition
  maximal_order
  mult_table::Array{T,3} # e_i*e_j = sum_k mult_table[i, j, k]*e_k
  canonical_basis::Int # whether A[(j - 1)*n + i] == E_ij, where E_ij = (e_kl)_kl with e_kl = 1 if i =k and j = l and e_kl = 0 otherwise.
  center#Tuple{StructureConstantAlgebra{T}, mor(StructureConstantAlgebra{T}, StructureConstantAlgebra{T})
  trace_basis_elem::Vector{T}
  gens

  maps_to_numberfields
  isomorphic_full_matrix_algebra#Tuple{MatAlgebra{T}, mor(StructureConstantAlgebra{T}, MatAlgebra{T})

  function MatAlgebra{T,S}(R::Ring) where {T,S}
    A = new{T,S}()
    A.base_ring = R
    A.coefficient_ring = R
    if R <: Field
      A.is_simple = 1
    else
      A.is_simple = 0
    end
    A.issemisimple = 0
    A.is_commutative = 0
    A.canonical_basis = 0
    return A
  end

  function MatAlgebra{T,S}(R1::Ring, R2::NCRing) where {T,S}
    A = new{T,S}()
    A.base_ring = R1
    A.coefficient_ring = R2
    A.is_simple = 0
    A.issemisimple = 0
    A.is_commutative = 0
    A.canonical_basis = 0
    return A
  end
end

mutable struct MatAlgebraElem{T,S<:MatElem} <: AbstractCentralSimpleAlgebraElem{T}
  parent::MatAlgebra{T,S}
  matrix::S # over the coefficient ring of the parent
  coeffs::Vector{T} # over the base ring of the parent
  has_coeffs::Bool

  function MatAlgebraElem{T,S}(A::MatAlgebra{T,S}) where {T,S}
    z = new{T,S}()
    z.parent = A
    z.matrix = zero_matrix(base_ring(A), degree(A), degree(A))
    z.has_coeffs = false
    return z
  end

  function MatAlgebraElem{T,S}(A::MatAlgebra{T,S}, M::S) where {T,S}
    z = new{T,S}()
    z.parent = A
    z.matrix = M
    z.has_coeffs = false
    return z
  end
end
