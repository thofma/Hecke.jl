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

