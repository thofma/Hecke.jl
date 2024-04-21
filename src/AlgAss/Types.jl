abstract type AbstractAssociativeAlgebra{T} <: NCRing end

abstract type AbstractAssociativeAlgebraElem{T} <: NCRingElem end

################################################################################
#
#  StructureConstantAlgebra / AssociativeAlgebraElem
#
################################################################################

# Associative algebras defined by structure constants (multiplication table)
@attributes mutable struct StructureConstantAlgebra{T} <: AbstractAssociativeAlgebra{T}
  base_ring::Ring
  mult_table::Array{T, 3} # e_i*e_j = sum_k mult_table[i, j, k]*e_k
  one::Vector{T}
  has_one::Bool
  iszero::Bool
  is_commutative::Int       # 0: don't know
                           # 1: known to be commutative
                           # 2: known to be not commutative
  basis#::Vector{AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}
  gens#::Vector{AssociativeAlgebraElem{T, StructureConstantAlgebra{T}} # "Small" number of algebra generators
  trace_basis_elem::Vector{T}
  is_simple::Int
  issemisimple::Int

  decomposition#::Vector{Tuple{StructureConstantAlgebra{T}, mor(StructureConstantAlgebra{T}, StructureConstantAlgebra{T})}
  center#Tuple{StructureConstantAlgebra{T}, mor(StructureConstantAlgebra{T}, StructureConstantAlgebra{T})
  maps_to_numberfields
  maximal_order
  isomorphic_full_matrix_algebra#Tuple{MatAlgebra{T}, mor(StructureConstantAlgebra{T}, MatAlgebra{T})

  # Constructor with default values
  function StructureConstantAlgebra{T}(R::Ring) where {T}
    A = new{T}()
    A.base_ring = R
    A.is_commutative = 0
    A.is_simple = 0
    A.issemisimple = 0
    return A
  end

  function StructureConstantAlgebra{T}(R::Ring, mult_table::Array{T, 3}, one::Vector{T}) where {T}
    A = StructureConstantAlgebra{T}(R)
    A.mult_table = mult_table
    A.one = one
    A.has_one = true
    A.iszero = (size(mult_table, 1) == 0)
    return A
  end

  function StructureConstantAlgebra{T}(R::Ring, mult_table::Array{T, 3}) where {T}
    A = StructureConstantAlgebra{T}(R)
    A.mult_table = mult_table
    A.iszero = (size(mult_table, 1) == 0)
    return A
  end
end

@attributes mutable struct QuaternionAlgebra{T} <: AbstractAssociativeAlgebra{T}
  base_ring::Ring
  mult_table::Array{T, 3}
  one::Vector{T}
  zero::Vector{T}
  std::Tuple{T, T}
  basis#::Vector{AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}
  is_simple::Int                           # Always 1
  trace_basis_elem::Vector{T}
  maximal_order
  std_inv# standard involution

  function QuaternionAlgebra{T}() where {T}
    z = new{T}()
    z.is_simple = 1
    return z
  end

end

mutable struct AssociativeAlgebraElem{T, S} <: AbstractAssociativeAlgebraElem{T}
  parent::S
  coeffs::Vector{T}

  function AssociativeAlgebraElem{T, S}(A::S) where {T, S}
    z = new{T, S}()
    z.parent = A
    z.coeffs = Vector{T}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function AssociativeAlgebraElem{T, S}(A::StructureConstantAlgebra{T}) where {T, S}
    z = new{T, StructureConstantAlgebra{T}}()
    z.parent = A
    z.coeffs = Vector{T}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function AssociativeAlgebraElem{T, S}(A::QuaternionAlgebra{T}) where {T, S}
    z = new{T, QuaternionAlgebra{T}}()
    z.parent = A
    z.coeffs = Vector{T}(undef, 4)
    for i = 1:4
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  # This does not make a copy of coeffs
  function AssociativeAlgebraElem{T, S}(A::S, coeffs::Vector{T}) where {T, S}
    z = new{T, S}()
    z.parent = A
    z.coeffs = coeffs
    return z
  end
end

################################################################################
#
#  GroupAlgebra / GroupAlgebraElem
#
################################################################################

# Group rings
@attributes mutable struct GroupAlgebra{T, S, R} <: AbstractAssociativeAlgebra{T}
  base_ring::Ring
  group::S
  group_to_base::Dict{R, Int}
  base_to_group::Vector{R}
  one::Vector{T}
  basis#::Vector{AssociativeAlgebraElem{T, StructureConstantAlgebra{T}}
  gens#::Vector{AssociativeAlgebraElem{T, StructureConstantAlgebra{T}} # "Small" number of algebra generators
  mult_table::Matrix{Int} # b_i * b_j = b_(mult_table[i, j])
  is_commutative::Int
  trace_basis_elem::Vector{T}
  is_simple::Int
  issemisimple::Int

  decomposition
  center
  maps_to_numberfields
  maximal_order

  function GroupAlgebra(K::Ring, G::FinGenAbGroup, cached::Bool = true)
    A = GroupAlgebra(K, G, op = +, cached = cached)
    A.is_commutative = true
    return A
  end

  function GroupAlgebra(K::Ring, G; op = *, cached = true)
    return get_cached!(GroupAlgebraID, (K, G, op), cached) do
      A = new{elem_type(K), typeof(G), elem_type(G)}()
      A.is_commutative = 0
      A.is_simple = 0
      A.issemisimple = 0
      A.base_ring = K
      A.group = G
      d = Int(order(G))
      A.group_to_base = Dict{elem_type(G), Int}()
      A.base_to_group = Vector{elem_type(G)}(undef, d)
      A.mult_table = zeros(Int, d, d)

      i = 2
      for g in collect(G)
        if isone(g)
          A.group_to_base[deepcopy(g)] = 1
          A.base_to_group[1] = deepcopy(g)
          continue
        end
        A.group_to_base[deepcopy(g)] = i
        A.base_to_group[i] = deepcopy(g)
        i += 1
      end

      v = Vector{elem_type(K)}(undef, d)
      for i in 1:d
        v[i] = zero(K)
      end
      v[1] = one(K)

      A.one = v

      for i = 1:d
        for j = 1:d
          l = op(A.base_to_group[i], A.base_to_group[j])
          A.mult_table[i, j] = A.group_to_base[l]
        end
      end

      @assert all(A.mult_table[1, i] == i for i in 1:dim(A))

      return A
    end::GroupAlgebra{elem_type(K), typeof(G), elem_type(G)}
  end
end

const GroupAlgebraID = AbstractAlgebra.CacheDictType{Tuple{Ring, Any, Any}, GroupAlgebra}()

mutable struct GroupAlgebraElem{T, S} <: AbstractAssociativeAlgebraElem{T}
  parent::S
  coeffs::Vector{T}

  function GroupAlgebraElem{T, S}(A::S) where {T, S}
    z = new{T, S}()
    z.parent = A
    z.coeffs = Vector{T}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function GroupAlgebraElem{T, S}(A::S, g::U) where {T, S, U}
    return A[A.group_to_base[g]]
  end

  # This does not make a copy of coeffs
  function GroupAlgebraElem{T, S}(A::S, coeffs::Vector{T}) where {T, S}
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
#  MatAlgebra / MatAlgebraElem
#
################################################################################

# T == elem_type(base_ring), S == dense_matrix_type(coefficient_ring)
@attributes mutable struct MatAlgebra{T, S} <: AbstractAssociativeAlgebra{T}
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
  mult_table::Array{T, 3} # e_i*e_j = sum_k mult_table[i, j, k]*e_k
  canonical_basis::Int # whether A[(j - 1)*n + i] == E_ij, where E_ij = (e_kl)_kl with e_kl = 1 if i =k and j = l and e_kl = 0 otherwise.
  center#Tuple{StructureConstantAlgebra{T}, mor(StructureConstantAlgebra{T}, StructureConstantAlgebra{T})
  trace_basis_elem::Vector{T}
  gens

  maps_to_numberfields
  isomorphic_full_matrix_algebra#Tuple{MatAlgebra{T}, mor(StructureConstantAlgebra{T}, MatAlgebra{T})

  function MatAlgebra{T, S}(R::Ring) where {T, S}
    A = new{T, S}()
    A.base_ring = R
    A.coefficient_ring = R
    A.is_simple = 0
    A.issemisimple = 0
    A.is_commutative = 0
    A.canonical_basis = 0
    return A
  end

  function MatAlgebra{T, S}(R1::Ring, R2::NCRing) where {T, S}
    A = new{T, S}()
    A.base_ring = R1
    A.coefficient_ring = R2
    A.is_simple = 0
    A.issemisimple = 0
    A.is_commutative = 0
    A.canonical_basis = 0
    return A
  end
end

mutable struct MatAlgebraElem{T, S, Mat} <: AbstractAssociativeAlgebraElem{T}
  parent::S
  matrix::Mat # over the coefficient ring of the parent
  coeffs::Vector{T} # over the base ring of the parent
  has_coeffs::Bool

  function MatAlgebraElem{T, S, Mat}(A::S) where {T, S, Mat}
    z = new{T, S, Mat}()
    z.parent = A
    z.matrix = zero_matrix(base_ring(A), degree(A), degree(A))
    z.has_coeffs = false
    return z
  end

  function MatAlgebraElem{T, S, Mat}(A::S, M::Mat) where {T, S, Mat}
    z = new{T, S, Mat}()
    z.parent = A
    z.matrix = M
    z.has_coeffs = false
    return z
  end
end
