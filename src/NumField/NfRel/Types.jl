###############################################################################
#
#  RelNumFieldOrder
#
###############################################################################

# I don't like that we have to drag S around
# Still hoping for julia/#18466

mutable struct NfRelOrdSet{T}
  nf::NumField{T}

  function NfRelOrdSet{T}(K::NumField{T}) where {T}
    a = new(K)
    return a
  end
end

@attributes mutable struct RelNumFieldOrder{T, S, U} <: NumFieldOrder
  nf::NumField{T}
  basis_nf::Vector{U}
  basis_matrix::Generic.MatSpaceElem{T}
  basis_mat_inv::Generic.MatSpaceElem{T}
  basis_pmatrix::PMat{T, S}
  pseudo_basis::Vector{Tuple{U, S}}

  disc_abs::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem} # used if T == AbsSimpleNumFieldElem
  disc_rel#::RelNumFieldOrderIdeal{T} # used otherwise; is a forward declaration
  parent::NfRelOrdSet{T}

  is_equation_order::Bool

  is_maximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  trace_mat::Generic.MatSpaceElem{T}

  index::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem} #Only if the base field is AbsSimpleNumField

  inv_coeff_ideals::Vector{S}
  index_div

  function RelNumFieldOrder{T, S, U}(K::NumField{T}) where {T, S, U}
    z = new{T, S, U}()
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.is_equation_order = false
    z.is_maximal = 0
    z.index_div = Dict{ideal_type(order_type(base_field(K))), Vector{Tuple{ideal_type(z), Int}}}()
    return z
  end

  function RelNumFieldOrder{T, S, U}(K::NumField{T}, M::PMat{T, S}) where {T, S, U}
    z = RelNumFieldOrder{T, S, U}(K)
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    z.index_div = Dict{ideal_type(order_type(base_field(K))), Vector{Tuple{ideal_type(z), Int}}}()
    return z
  end

  function RelNumFieldOrder{T, S, U}(K::NumField{T}, M::Generic.MatSpaceElem{T}) where {T, S, U}
    z = RelNumFieldOrder{T, S, U}(K)
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.basis_matrix = M
    z.basis_pmatrix = pseudo_matrix(M)
    z.index_div = Dict{ideal_type(order_type(base_field(K))), Vector{Tuple{ideal_type(z), Int}}}()
    return z
  end
end

###############################################################################
#
#  RelNumFieldOrderElem
#
###############################################################################

mutable struct RelNumFieldOrderElem{T, U} <: NumFieldOrderElem
  parent#::RelNumFieldOrder{T, S} # I don't want to drag the S around
  elem_in_nf::U
  coordinates::Vector{T}
  has_coord::Bool

  function RelNumFieldOrderElem{T, U}(O::RelNumFieldOrder{T}) where {T, U}
    z = new{T, U}()
    z.parent = O
    z.elem_in_nf = zero(nf(O))
    z.coordinates = Vector{T}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function RelNumFieldOrderElem{T, U}(O::RelNumFieldOrder{T}, a::U) where {T, U}
    z = new{T, U}()
    z.parent = O
    z.elem_in_nf = a
    z.coordinates = Vector{T}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function RelNumFieldOrderElem{T, U}(O::RelNumFieldOrder{T}, a::U, arr::Vector{T}) where {T, U}
    z = new{T, U}()
    z.parent = O
    z.elem_in_nf = a
    z.coordinates = arr
    z.has_coord = true
    return z
  end
end

###############################################################################
#
#  RelNumFieldOrderFractionalIdeal
#
###############################################################################

mutable struct NfRelOrdFracIdlSet{T, S, U}
  order::RelNumFieldOrder{T, S, U}

  function NfRelOrdFracIdlSet{T, S, U}(O::RelNumFieldOrder{T, S, U}) where {T, S, U}
    a = new(O)
    return a
  end
end

mutable struct RelNumFieldOrderFractionalIdeal{T, S, U} <: NumFieldOrderFractionalIdeal
  order::RelNumFieldOrder{T, S, U}
  parent::NfRelOrdFracIdlSet{T, S, U}
  basis_pmatrix::PMat{T, S}
  pseudo_basis::Vector{Tuple{U, S}}
  basis_matrix::Generic.MatSpaceElem{T}
  basis_mat_inv::Generic.MatSpaceElem{T}
  den::ZZRingElem

  norm
  has_norm::Bool

  function RelNumFieldOrderFractionalIdeal{T, S, U}(O::RelNumFieldOrder{T, S, U}) where {T, S, U}
    z = new{T, S, U}()
    z.order = O
    z.parent = NfRelOrdFracIdlSet{T, S, U}(O)
    z.has_norm = false
    return z
  end

  function RelNumFieldOrderFractionalIdeal{T, S, U}(O::RelNumFieldOrder{T, S, U}, M::PMat{T, S}) where {T, S, U}
    z = RelNumFieldOrderFractionalIdeal{T, S, U}(O)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    return z
  end
end

###############################################################################
#
#  RelNumFieldOrderIdeal
#
###############################################################################

mutable struct NfRelOrdIdlSet{T, S, U}
  order::RelNumFieldOrder{T, S, U}

  function NfRelOrdIdlSet{T, S, U}(O::RelNumFieldOrder{T, S, U}) where {T, S, U}
    a = new(O)
    return a
  end
end

@attributes mutable struct RelNumFieldOrderIdeal{T, S, U} <: NumFieldOrderIdeal
  order::RelNumFieldOrder{T, S, U}
  parent::NfRelOrdIdlSet{T, S, U}
  basis_pmatrix::PMat{T, S}
  pseudo_basis::Vector{Tuple{U, S}}
  basis_matrix::Generic.MatSpaceElem{T}
  basis_mat_inv::Generic.MatSpaceElem{T}

  norm
  has_norm::Bool
  is_prime::Int            # 0: don't know
                           # 1 known to be prime
                           # 2 known to be not prime
  splitting_type::Tuple{Int, Int}

  minimum
  non_index_div_poly::FqPolyRingElem # only used if the ideal is a prime ideal not dividing the index
  p_uniformizer::RelNumFieldOrderElem{T, U}
  anti_uniformizer::U

  function RelNumFieldOrderIdeal{T, S, U}(O::RelNumFieldOrder{T, S, U}) where {T, S, U}
    z = new{T, S, U}()
    z.order = O
    z.parent = NfRelOrdIdlSet{T, S, U}(O)
    z.has_norm = false
    z.is_prime = 0
    z.splitting_type = (0,0)
    return z
  end

  function RelNumFieldOrderIdeal{T, S, U}(O::RelNumFieldOrder{T, S, U}, M::PMat{T, S}) where {T, S, U}
    z = RelNumFieldOrderIdeal{T, S, U}(O)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    return z
  end
end

################################################################################
#
#  RelNonSimpleNumField / RelNonSimpleNumFieldElem
#
################################################################################

@attributes mutable struct RelNonSimpleNumField{T} <: NonSimpleNumField{T}
  base_ring::Nemo.Field
  pol::Vector{Nemo.Generic.MPoly{T}}
  abs_pol::Vector{Generic.Poly{T}}
  S::Vector{Symbol}
  basis_traces::Vector{Vector{T}}

  function RelNonSimpleNumField(abs_pol::Array{Generic.Poly{T}}, f::Vector{Nemo.Generic.MPoly{T}}, S::Vector{Symbol}; cached::Bool = false) where T
    r = new{T}()
    r.pol = f
    r.abs_pol = abs_pol
    r.base_ring = base_ring(f[1])
    r.S = S
    return r
  end
end

mutable struct RelNonSimpleNumFieldElem{T} <: NonSimpleNumFieldElem{T}
  data::Nemo.Generic.MPoly{T}
  parent::RelNonSimpleNumField{T}

  RelNonSimpleNumFieldElem{T}(g::Generic.MPoly{T}) where {T} = new{T}(g)
end

################################################################################
#
#  Quotient rings of orders
#
################################################################################

# T1 is the type of the order, T2 the type of the ideal,
# T3 the type of the basis pseudo matrix of the ideal
mutable struct RelOrdQuoRing{T1, T2, T3} <: Ring
  base_ring::T1
  ideal::T2
  basis_pmatrix::T3

  function RelOrdQuoRing{T1, T2, T3}(O::T1, I::T2) where { T1, T2, T3 }
    z = new{T1, T2, T3}()
    z.base_ring = O
    z.ideal = I
    z.basis_pmatrix = basis_pmatrix_wrt(I, O)
    return z
  end
end

function RelOrdQuoRing(O::T1, I::T2) where { T1, T2 }
  @assert T2 == ideal_type(O)
  return RelOrdQuoRing{T1, T2, typeof(basis_pmatrix(I, copy = false))}(O, I)
end

# T1, T2 and T3 as for RelOrdQuoRing, S is the elem_type of the order
mutable struct RelOrdQuoRingElem{T1, T2, T3, S} <: RingElem
  elem::S
  parent::RelOrdQuoRing{T1, T2, T3}

  function RelOrdQuoRingElem{T1, T2, T3, S}(Q::RelOrdQuoRing{T1, T2, T3}, x::S) where { T1, T2, T3, S }
    z = new{T1, T2, T3, S}()
    z.elem = mod(x, Q)
    z.parent = Q
    return z
  end
end

function RelOrdQuoRingElem(Q::RelOrdQuoRing{T1, T2, T3}, x::S) where { T1, T2, T3, S }
  return RelOrdQuoRingElem{T1, T2, T3, S}(Q, x)
end
