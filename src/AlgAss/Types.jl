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
  isomorphic_full_matrix_algebra#Tuple{AlgMat{T}, mor(AlgAss{T}, AlgMat{T})

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

mutable struct AlgQuat{T} <: AbsAlgAss{T}
  base_ring::Ring
  mult_table::Array{T, 3}
  one::Vector{T}
  zero::Vector{T}
  std::Tuple{T, T}
  basis#::Vector{AlgAssElem{T, AlgAss{T}}
  issimple::Int                           # Always 1
  trace_basis_elem::Vector{T}
  maximal_order
  std_inv# standard involution
  
  function AlgQuat{T}() where {T} 
    z = new{T}()
    z.issimple = 1
    return z
  end

end

mutable struct AlgAssElem{T, S} <: AbsAlgAssElem{T}
  parent::S
  coeffs::Vector{T}

  function AlgAssElem{T, S}(A::S) where {T, S}
    z = new{T, S}()
    z.parent = A
    z.coeffs = Vector{T}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function AlgAssElem{T, S}(A::AlgAss{T}) where {T, S}
    z = new{T, AlgAss{T}}()
    z.parent = A
    z.coeffs = Vector{T}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function AlgAssElem{T, S}(A::AlgQuat{T}) where {T, S}
    z = new{T, AlgQuat{T}}()
    z.parent = A
    z.coeffs = Vector{T}(undef, 4)
    for i = 1:4
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  # This does not make a copy of coeffs
  function AlgAssElem{T, S}(A::S, coeffs::Vector{T}) where {T, S}
    z = new{T, S}()
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
  base_to_group::Dict{Int, R}
  one::Vector{T}
  basis#::Vector{AlgAssElem{T, AlgAss{T}}
  gens#::Vector{AlgAssElem{T, AlgAss{T}} # "Small" number of algebra generators
  mult_table::Matrix{Int} # b_i * b_j = b_(mult_table[i, j])
  iscommutative::Int
  trace_basis_elem::Vector{T}
  issimple::Int
  issemisimple::Int

  decomposition
  center
  maps_to_numberfields
  maximal_order

  function AlgGrp(K::Ring, G::GrpAbFinGen, cached::Bool = true)
    A = AlgGrp(K, G, op = +, cached = cached)
    A.iscommutative = true
    return A
  end

  function AlgGrp(K::Ring, G; op = *, cached = true)
    if cached && haskey(AlgGrpDict, (K, G, op))
      return AlgGrpDict[(K, G, op)]::AlgGrp{elem_type(K), typeof(G), elem_type(G)}
    end

    A = new{elem_type(K), typeof(G), elem_type(G)}()
    A.iscommutative = 0
    A.issimple = 0
    A.issemisimple = 0
    A.base_ring = K
    A.group = G
    d = Int(order(G))
    A.group_to_base = Dict{elem_type(G), Int}()
    A.base_to_group = Dict{Int, elem_type(G)}()
    A.mult_table = zeros(Int, d, d)

    for (i, g) in enumerate(G)
      A.group_to_base[deepcopy(g)] = i
      A.base_to_group[i] = deepcopy(g)
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

    if cached
      AlgGrpDict[(K, G, op)] = A
    end

    return A
  end
end

const AlgGrpDict = IdDict()

mutable struct AlgGrpElem{T, S} <: AbsAlgAssElem{T}
  parent::S
  coeffs::Vector{T}

  function AlgGrpElem{T, S}(A::S) where {T, S}
    z = new{T, S}()
    z.parent = A
    z.coeffs = Vector{T}(undef, size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  function AlgGrpElem{T, S}(A::S, g::U) where {T, S, U}
    return A[A.group_to_base[g]]
  end

  # This does not make a copy of coeffs
  function AlgGrpElem{T, S}(A::S, coeffs::Vector{T}) where {T, S}
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

  maps_to_numberfields
  isomorphic_full_matrix_algebra#Tuple{AlgMat{T}, mor(AlgAss{T}, AlgMat{T})

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
