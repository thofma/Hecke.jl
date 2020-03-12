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

  isnice::Bool
  nice_order#Tuple{AlgAssAbsOrd, T}
  nice_order_ideal::T

  function AlgAssRelOrd{S, T}(A::AbsAlgAss{S}) where {S, T}
    z = new{S, T}()
    z.algebra = A
    z.dim = dim(A)
    z.ismaximal = 0
    z.isnice = false
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
  algebra::AbsAlgAss{S}

  pseudo_basis::Vector{Tuple{AbsAlgAssElem{S}, T}}
  # The basis matrices are in the BASIS of the ALGEBRA!
  basis_pmatrix::PMat{S, T}
  basis_matrix::Generic.MatSpaceElem{S}
  basis_mat_inv::Generic.MatSpaceElem{S}

  # Basis pseudo-matrices with respect to orders
  basis_pmatrix_wrt::Dict{AlgAssRelOrd{S, T}, PMat{S, T}}

  # Left and right order:
  # The largest orders of which the ideal is a left resp. right ideal.
  left_order::AlgAssRelOrd{S, T}
  right_order::AlgAssRelOrd{S, T}

  # Any order contained in the left or right order, that is, an order of which
  # the ideal is a (possibly fractional) ideal.
  order::AlgAssRelOrd{S, T}

  # isleft and isright with respect to `order`
  isleft::Int                      # 0 Not known
                                   # 1 Known to be a left ideal
                                   # 2 Known not to be a left ideal
  isright::Int                     # as for isleft

  iszero::Int                      # 0: don't know, 1: known to be zero, 2: known to be not zero

  norm::Dict{AlgAssRelOrd{S, T}, T} # The ideal has different norms with respect
                                    # to different orders
  normred::Dict{AlgAssRelOrd{S, T}, T}

  function AlgAssRelOrdIdl{S, T}(A::AbsAlgAss{S}) where {S, T}
    z = new{S, T}()
    z.algebra = A
    z.isleft = 0
    z.isright = 0
    z.iszero = 0
    z.basis_pmatrix_wrt = Dict{AlgAssRelOrd{S, T}, PMat{S, T}}()
    z.norm = Dict{AlgAssRelOrd{S, T}, T}()
    z.normred = Dict{AlgAssRelOrd{S, T}, T}()
    return z
  end

  function AlgAssRelOrdIdl{S, T}(A::AbsAlgAss{S}, M::PMat{S, T}) where {S, T}
    z = AlgAssRelOrdIdl{S, T}(A)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    return z
  end
end
