###############################################################################
#
#  NfRelOrd
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

mutable struct NfRelOrd{T, S} <: Ring
  nf::NumField{T}
  basis_nf::Vector{NumFieldElem{T}}
  basis_matrix::Generic.MatSpaceElem{T}
  basis_mat_inv::Generic.MatSpaceElem{T}
  basis_pmatrix::PMat{T, S}
  pseudo_basis::Vector{Tuple{NumFieldElem{T}, S}}

  disc_abs::NfOrdIdl # used if T == nf_elem
  disc_rel#::NfRelOrdIdl{T} # used otherwise; is a forward declaration
  parent::NfRelOrdSet{T}

  isequation_order::Bool

  ismaximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  trace_mat::Generic.MatSpaceElem{T}

  inv_coeff_ideals::Vector{S}

  function NfRelOrd{T, S}(K::NumField{T}) where {T, S}
    z = new{T, S}()
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.isequation_order = false
    z.ismaximal = 0
    return z
  end

  function NfRelOrd{T, S}(K::NumField{T}, M::PMat{T, S}) where {T, S}
    z = NfRelOrd{T, S}(K)
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    return z
  end

  function NfRelOrd{T, S}(K::NumField{T}, M::Generic.MatSpaceElem{T}) where {T, S}
    z = NfRelOrd{T, S}(K)
    z.nf = K
    z.parent = NfRelOrdSet{T}(K)
    z.basis_matrix = M
    z.basis_pmatrix = pseudo_matrix(M)
    return z
  end
end

###############################################################################
#
#  NfRelOrdElem
#
###############################################################################

mutable struct NfRelOrdElem{T} <: RingElem
  parent#::NfRelOrd{T, S} # I don't want to drag the S around
  elem_in_nf::NumFieldElem{T}
  coordinates::Vector{T}
  has_coord::Bool

  function NfRelOrdElem{T}(O::NfRelOrd{T}) where {T}
    z = new{T}()
    z.parent = O
    z.elem_in_nf = zero(nf(O))
    z.coordinates = Vector{T}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function NfRelOrdElem{T}(O::NfRelOrd{T}, a::NumFieldElem{T}) where {T}
    z = new{T}()
    z.parent = O
    z.elem_in_nf = a
    z.coordinates = Vector{T}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function NfRelOrdElem{T}(O::NfRelOrd{T}, a::NumFieldElem{T}, arr::Vector{T}) where {T}
    z = new{T}()
    z.parent = O
    z.elem_in_nf = a
    z.coordinates = arr
    z.has_coord = true
    return z
  end
end

###############################################################################
#
#  NfRelOrdFracIdl
#
###############################################################################

mutable struct NfRelOrdFracIdlSet{T, S}
  order::NfRelOrd{T, S}

  function NfRelOrdFracIdlSet{T, S}(O::NfRelOrd{T, S}) where {T, S}
    a = new(O)
    return a
  end
end

mutable struct NfRelOrdFracIdl{T, S}
  order::NfRelOrd{T, S}
  parent::NfRelOrdFracIdlSet{T, S}
  basis_pmatrix::PMat{T, S}
  pseudo_basis::Vector{Tuple{NumFieldElem{T}, S}}
  basis_matrix::Generic.MatSpaceElem{T}
  basis_mat_inv::Generic.MatSpaceElem{T}
  den::fmpz

  norm
  has_norm::Bool

  function NfRelOrdFracIdl{T, S}(O::NfRelOrd{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdFracIdlSet{T, S}(O)
    z.has_norm = false
    return z
  end

  function NfRelOrdFracIdl{T, S}(O::NfRelOrd{T, S}, M::PMat{T, S}) where {T, S}
    z = NfRelOrdFracIdl{T, S}(O)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    return z
  end

  function NfRelOrdFracIdl{T, S}(O::NfRelOrd{T, S}, a::Array{Tuple{T1, S}}) where {T1 <: NumFieldElem{T}, S} where T
    z = NfRelOrdFracIdl{T, S}(O)
    z.pseudo_basis = a
    return z
  end
end

###############################################################################
#
#  NfRelOrdIdl
#
###############################################################################

mutable struct NfRelOrdIdlSet{T, S}
  order::NfRelOrd{T, S}

  function NfRelOrdIdlSet{T, S}(O::NfRelOrd{T, S}) where {T, S}
    a = new(O)
    return a
  end
end

mutable struct NfRelOrdIdl{T, S}
  order::NfRelOrd{T, S}
  parent::NfRelOrdIdlSet{T, S}
  basis_pmatrix::PMat{T, S}
  pseudo_basis::Vector{Tuple{NumFieldElem{T}, S}}
  basis_matrix::Generic.MatSpaceElem{T}
  basis_mat_inv::Generic.MatSpaceElem{T}

  norm
  has_norm::Bool
  is_prime::Int            # 0: don't know
                           # 1 known to be prime
                           # 2 known to be not prime
  splitting_type::Tuple{Int, Int}

  minimum
  non_index_div_poly::fq_poly # only used if the ideal is a prime ideal not dividing the index
  p_uniformizer::NfRelOrdElem{T}
  anti_uniformizer::NumFieldElem{T}

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}) where {T, S}
    z = new{T, S}()
    z.order = O
    z.parent = NfRelOrdIdlSet{T, S}(O)
    z.has_norm = false
    z.is_prime = 0
    z.splitting_type = (0,0)
    return z
  end

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}, M::PMat{T, S}) where {T, S}
    z = NfRelOrdIdl{T, S}(O)
    z.basis_pmatrix = M
    z.basis_matrix = M.matrix
    return z
  end

  function NfRelOrdIdl{T, S}(O::NfRelOrd{T, S}, a::Array{Tuple{T1, S}}) where {T1 <: NumFieldElem{T}, S} where T
    z = NfRelOrdIdl{T, S}(O)
    z.pseudo_basis = a
    return z
  end
end

################################################################################
#
#  NfRel_ns / NfRel_nsElem
#
################################################################################

mutable struct NfRel_ns{T} <: NonSimpleNumField{T}
  base_ring::Nemo.Field
  pol::Array{Nemo.Generic.MPoly{T}, 1}
  abs_pol::Array{Generic.Poly{T}, 1}
  S::Array{Symbol, 1}
  auxilliary_data::Array{Any, 1}

  function NfRel_ns(abs_pol::Array{Generic.Poly{T}}, f::Array{Nemo.Generic.MPoly{T}, 1}, S::Array{Symbol, 1}; cached::Bool = false) where T
    r = new{T}()
    r.pol = f
    r.abs_pol = abs_pol
    r.base_ring = base_ring(f[1])
    r.S = S
    r.auxilliary_data = Array{Any}(undef, 5)
    return r
  end
end

mutable struct NfRel_nsElem{T} <: NonSimpleNumFieldElem{T}
  data::Nemo.Generic.MPoly{T}
  parent::NfRel_ns{T}

  NfRel_nsElem{T}(g::Generic.MPoly{T}) where {T} = new{T}(g)
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
    z.basis_pmatrix = basis_pmatrix(I)
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
