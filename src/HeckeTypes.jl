################################################################################
#
#  Z/nZ modelled with UInt's
#
################################################################################

struct nmod_struct
  n::UInt    # mp_limb_t
  ninv::UInt # mp_limb_t
  norm::UInt # mp_limb_t
end

mutable struct nmod_struct_non
  n::UInt    # mp_limb_t
  ninv::UInt # mp_limb_t
  norm::UInt # mp_limb_t
end

################################################################################
#
#  Transformations for matrices
#
################################################################################

abstract type Trafo end

mutable struct TrafoScale{T} <: Trafo
  i::Int
  c::T

  function TrafoScale{T}(i::Int, c::T) where {T}
    return new{T}(i, c)
  end
end

mutable struct TrafoSwap{T} <: Trafo
  i::Int
  j::Int

  function TrafoSwap{T}(i, j) where {T}
    return new{T}(i, j)
  end
end

# j -> j + s*i
mutable struct TrafoAddScaled{T} <: Trafo
  i::Int
  j::Int
  s::T

  function TrafoAddScaled{T}(i::Int, j::Int, s::T) where {T}
    return new{T}(i, j, s)
  end
end

TrafoAddScaled(i::Int, j::Int, s::T) where {T} = TrafoAddScaled{T}(i, j, s)

# if from left, then
# row i -> a*row i + b * row j
# row j -> c*row i + d * row j
mutable struct TrafoParaAddScaled{T} <: Trafo
  i::Int
  j::Int
  a::T
  b::T
  c::T
  d::T

  function TrafoParaAddScaled{T}(i::Int, j::Int, a::T, b::T, c::T, d::T) where {T}
    return new{T}(i, j, a, b, c, d)
  end
end

TrafoParaAddScaled(i::Int, j::Int, a::T, b::T, c::T, d::T) where {T} =
      TrafoParaAddScaled{T}(i, j, a, b, c, d)

mutable struct TrafoId{T} <: Trafo
end

mutable struct TrafoPartialDense{S} <: Trafo
  i::Int
  rows::UnitRange{Int}
  cols::UnitRange{Int}
  U::S

  function TrafoPartialDense{S}(i::Int, rows::UnitRange{Int},
                                cols::UnitRange{Int}, U::S) where {S}
    return new(i, rows, cols, U)
  end
end

function TrafoPartialDense(i::Int, rows::UnitRange{Int},
                           cols::UnitRange{Int}, U::S) where S
  return TrafoPartialDense{S}(i, rows, cols, U)
end

# this is shorthand for the permutation matrix corresponding to
# (i i+1)(i+1 i+2)...(rows-1 rows)
mutable struct TrafoDeleteZero{T} <: Trafo
  i::Int
end

################################################################################
#
#  Wrapper for fmpz_preinvn_struct
#
################################################################################

mutable struct fmpz_preinvn_struct
  dinv::Ptr{UInt}
  n::Int
  norm::Int

  function fmpz_preinvn_struct(f::fmpz)
    z = new()
    ccall((:fmpz_preinvn_init, :libflint), Void,
          (Ptr{fmpz_preinvn_struct}, Ptr{fmpz}), &z, &f)
    finalizer(z, _fmpz_preinvn_struct_clear_fn)
    return z
  end
end

################################################################################
#
#  Root context for fmpq_polys and roots modelled as acbs
#
################################################################################

struct acb_roots
  p::Int
  roots::Array{acb, 1}
  real_roots::Array{arb, 1}
  complex_roots::Array{acb, 1}
end

mutable struct acb_root_ctx
  poly::fmpq_poly
  _roots::Ptr{acb_struct}
  prec::Int
  roots::Array{acb, 1}
  real_roots::Array{arb, 1}
  complex_roots::Array{acb, 1}
  signature::Tuple{Int, Int}

  function acb_root_ctx(x::fmpq_poly, p::Int = 32)
    z = new()
    z.roots = _roots(x, p, p)
    z.poly = x
    z.prec = p
    z._roots = acb_vec(degree(x))
    r, s = signature(x)
    z.signature = (r, s)

    for i = 1:degree(x)
      ccall((:acb_set, :libarb), Void, (Ptr{acb_struct}, Ptr{acb}),
            z._roots + (i - 1) * sizeof(acb_struct), &z.roots[i])
    end

    z.prec = p
    A = Array{arb}(z.signature[1])
    B = Array{acb}(z.signature[2])

    for i in 1:r
      @assert isreal(z.roots[i])
      A[i] = real(z.roots[i])
    end

    j = 0
    for i in r+1:degree(x)
      if ispositive(imag(z.roots[i]))
        j += 1
        B[j] = z.roots[i]
      end
    end

    @assert j == s

    z.real_roots = A
    z.complex_roots = B

    finalizer(z, _acb_root_ctx_clear_fn)

    return z
  end
end

function _acb_root_ctx_clear_fn(x::acb_root_ctx)
  ccall((:_acb_vec_clear, :libarb), Void,
              (Ptr{acb_struct}, Int), x._roots, degree(x.poly))
end

################################################################################
#
#  SRow/SMat
#
################################################################################

mutable struct SMatSLP_add_row{T}
  row::Int
  col::Int
  val::T
end

mutable struct SMatSLP_swap_row
  row::Int
  col::Int
end

################################################################################
#
#  Abstract map type
#
################################################################################

abstract type HeckeMap <: SetMap end

################################################################################
#
#  Sparse rows
#
################################################################################

const SRowSpaceDict = ObjectIdDict()

mutable struct SRowSpace{T} <: Ring
  base_ring::Ring

  function SrowSpace(R::Ring, cached::Bool = false)
    if haskey(SRowSpaceDict, R)
      return SRowSpace[R]::SRowSpace{T}
    else
      z = new{T}(R)
      if cached
        SRowSpace[R] = z
      end
      return z
    end
  end
end

mutable struct SRow{T}
  #in this row, in column pos[1] we have value values[1]
  values::Array{T, 1}
  pos::Array{Int, 1}
  #parent::SRowSpace{T}

  function SRow{T}() where T
    r = new{T}()
    r.values = Array{T, 1}()
    r.pos = Array{Int, 1}()
    return r
  end

  function SRow{T}(A::Array{Tuple{Int, T}, 1}) where T
    r = new{T}()
    r.values = [x[2] for x in A]
    r.pos = [x[1] for x in A]
    return r
  end

  function SRow{T}(A::Array{Tuple{Int, Int}, 1}) where T
    r = new{T}()
    r.values = [T(x[2]) for x in A]
    r.pos = [x[1] for x in A]
    return r
  end

  function SRow{T}(A::SRow{S}) where {T, S}
    r = new{T}()
    r.values = Array{T}(length(A.pos))
    r.pos = copy(A.pos)
    for i=1:length(r.values)
      r.values[i] = T(A.values[i])
    end
    return r
  end

  function SRow{T}(pos::Array{Int, 1}, val::Array{T, 1}) where {T}
    length(pos) == length(val) || error("Arrays must have same length")
    r = new{T}()
    r.values = val
    r.pos = pos
    return r
  end
end

################################################################################
#
#  Sparse matrices 
#
################################################################################

const SMatSpaceDict = ObjectIdDict()

mutable struct SMatSpace{T} <: Ring
  rows::Int
  cols::Int
  base_ring::Ring

  function SMatSpace{T}(R::Ring, r::Int, c::Int, cached = false) where {T}
    if haskey(SMatSpaceDict, (R, r, c))
      return SMatSpaceDict[R, r, c,]::SMatSpace{T}
    else
      z = new{T}(r, c, R)
      if cached
        SMatSpaceDict[R, r, c] = z
      end
      return z
    end
  end
end

mutable struct SMat{T}
  r::Int
  c::Int
  rows::Array{SRow{T}, 1}
  nnz::Int
  base_ring::Ring

  function SMat{T}() where {T}
    r = new{T}()
    r.rows = Array{SRow{T}}(0)
    r.nnz = 0
    r.r = 0
    r.c = 0
    return r
  end

  function SMat{T}(a::SMat{S}) where {S, T}
    r = new{T}()
    r.rows = Array{SRow{T}}(length(a.rows))
    for i=1:rows(a)
      r.rows[i] = SRow{T}(a.rows[i])
    end
    r.c = a.c
    r.r = a.r
    r.nnz = a.nnz
    return r
  end
end

################################################################################
#
#  enum_ctx
#
################################################################################

# now that x is a fmpz_mat, the type for x is not really used
mutable struct enum_ctx{Tx, TC, TU}
  G::fmpz_mat
  n::Int
  limit :: Int # stop recursion at level limit, defaults to n
  d::Union{Integer, fmpz} #we actually want G/d
  C::Array{TC, 2} # the pseudo-cholesky form - we don't have fmpq_mat
  last_non_zero::Int
  x::fmpz_mat # 1 x n
  U::Array{TU, 1}
  L::Array{TU, 1}
  l::Array{TU, 1}
  tail::Array{TU, 1}
  c::fmpz # the length of the elements we want
  t::fmpz_mat # if set, a transformation to be applied to all elements
  t_den::fmpz
  cnt::Int

  function enum_ctx{Tx, TC, TU}() where {Tx, TC, TU}
    return new{Tx, TC, TU}()
  end
end

################################################################################
#
#  EnumCtxArb
#
################################################################################

mutable struct EnumCtxArb
  G::arb_mat
  L::Array{fmpz_mat, 1}
  x::fmpz_mat
  p::Int

  function EnumCtxArb(G::arb_mat)
    z = new()
    z.G = G
    z.x = zero_matrix(FlintZZ, 1, rows(G))
    z.p = prec(base_ring(G))
    return z
  end
end

################################################################################
#
#  FakeFmpqMatSpace/FakeFmpqMat
#
################################################################################

export FakeFmpqMat, FakeFmpqMatSpace

const FakeFmpqMatSpaceID = ObjectIdDict()

mutable struct FakeFmpqMatSpace
  rows::Int
  cols::Int

  function FakeFmpqMatSpace(r::Int, c::Int, cached::Bool=false)
    try
      return FakeFmpqMatSpaceID[r,c]::FakeFmpqMatSpace
    catch
      z = new(r,c)
      if cached
        FakeFmpqMatSpaceID[r,c] = z
      end
      return z
    end
  end
end

mutable struct FakeFmpqMat
  num::fmpz_mat
  den::fmpz
  parent::FakeFmpqMatSpace
  rows::Int
  cols::Int

  function FakeFmpqMat()
    z = new()
    return z
  end

  function FakeFmpqMat(x::fmpz_mat, y::fmpz, simplified::Bool = false)
    z = new()
    z.num = x
    z.den = y
    z.rows = rows(x)
    z.cols = cols(x)
    if !simplified
      simplify_content!(z)
    end
#    z.parent = FakeFmpqMatSpace(z.rows, z.cols)
    return z
  end

  function FakeFmpqMat(x::Tuple{fmpz_mat, fmpz})
    z = new()
    z.num = x[1]
    z.den = x[2]
    z.rows = rows(x[1])
    z.cols = cols(x[1])
    simplify_content!(z)
#    z.parent = FakeFmpqMatSpace(z.rows, z.cols)
    return z
  end

  function FakeFmpqMat(x::fmpz_mat)
    z = new()
    z.num = x
    z.den = fmpz(1)
    z.rows = rows(x)
    z.cols = cols(x)
#    z.parent = FakeFmpqMatSpace(z.rows, z.cols)
    return z
  end

  function FakeFmpqMat(x::fmpq_mat)
    z = new()
    d = denominator(x[1, 1])
    for i in 1:rows(x)
      for j in 1:cols(x)
        d = lcm(d, denominator(x[i, j]))
      end
    end
    n = zero_matrix(FlintZZ, rows(x), cols(x))
    #n = fmpz_mat(rows(x), cols(x))
    #n.base_ring = FlintIntegerRing()
    for i in 1:rows(x)
      for j in 1:cols(x)
        n[i, j] = FlintZZ(d*x[i, j])
      end
    end
#    z.parent = FakeFmpqMatSpace(rows(x), cols(x))
    z.rows = rows(x)
    z.cols = cols(x)
    z.num = n
    z.den = d
    return z
  end
end

################################################################################
#
#  FacElemMon/FacElem
#
################################################################################

mutable struct FacElemMon{S} <: Ring
  base_ring::S  # for the base
  basis_conjugates_log::Dict{RingElem, Tuple{Int, Array{arb, 1}}}
  basis_conjugates::Dict{RingElem, Tuple{Int, Array{arb, 1}}}
  conj_log_cache::Dict{Int, Dict{nf_elem, Array{arb, 1}}}

  function FacElemMon{S}(R::S, cached::Bool = false) where {S}
    if haskey(FacElemMonDict, R)
      return FacElemMonDict[R]::FacElemMon{S}
    else
      z = new()
      z.base_ring = R
      z.basis_conjugates_log = Dict{RingElem, Array{arb, 1}}()
      z.basis_conjugates = Dict{RingElem, Array{arb, 1}}()
      z.conj_log_cache = Dict{Int, Dict{nf_elem, arb}}()
      if cached
        FacElemMonDict[R] = z
      end
      return z
    end
  end
end

FacElemMon(R::S) where {S} = FacElemMon{S}(R)

mutable struct FacElem{B, S}
  fac::Dict{B, fmpz}
  hash::UInt
  parent::FacElemMon{S}

  function FacElem{B, S}() where {B, S}
    z = new{B, S}()
    z.fac = Dict{B, fmpz}()
    z.hash = UInt(0)
    return z
  end
end


################################################################################
#
#  NfOrdSet/NfOrd
#
################################################################################

export NfAbsOrdSet

mutable struct NfAbsOrdSet{T}
  nf::T

  function NfAbsOrdSet{T}(a::T, cached::Bool = false) where {T}
    if haskey(NfAbsOrdSetID, a)
      return NfAbsOrdSetID[a]::NfAbsOrdSet{T}
    else
      if cached
        NfAbsOrdSetID[a] = new(a)
        return NfAbsOrdSetID[a]::NfAbsOrdSet{T}
      else 
        return new{T}(a)::NfAbsOrdSet{T}
      end
    end
  end
end

NfAbsOrdSet(a::T) where {T} = NfAbsOrdSet{T}(a)

const NfAbsOrdSetID = ObjectIdDict()

const NfOrdSet = NfAbsOrdSet

export NfOrd, NfAbsOrd

mutable struct NfAbsOrd{S, T} <: Ring
  nf::S
  basis_nf::Vector{T}        # Basis as array of number field elements
  basis_ord#::Vector{NfAbsOrdElem}    # Basis as array of order elements
  basis_mat::FakeFmpqMat           # Basis matrix of order wrt basis of K
  basis_mat_inv::FakeFmpqMat       # Inverse of basis matrix
  gen_index::fmpq                  # The det of basis_mat_inv as fmpq
  index::fmpz                      # The det of basis_mat_inv
                                   # (this is the index of the equation order
                                   #  in the given order)
  disc::fmpz                       # Discriminant
  parent::NfAbsOrdSet{S}           # Parent object
  isequation_order::Bool           # Equation order of ambient number field?
  signature::Tuple{Int, Int}       # Signature of the ambient number field
                                   # (-1, 0) means "not set"
  #conjugate_data::acb_root_ctx
  minkowski_mat::Tuple{arb_mat, Int}        # Minkowski matrix
  torsion_units#::Tuple{Vector{NfAbsOrd}, NfAbsOrd}
  unit_group::Map                  # Abstract types in the field is usually bad,
                                   # but here it can be neglected.
                                   # We annotate the getter function
                                   # (unit_group(O)) with type assertions.

  ismaximal::Int                   # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  primesofmaximality::Vector{fmpz} # primes at the which the order is known to
                                   # to be maximal

  norm_change_const::Tuple{Float64, Float64}
                                   # Tuple c1, c2 as in the paper of
                                   # Fieker-Friedrich
                                   # (-1, -1) means "not set"
  trace_mat::fmpz_mat              # The trace matrix (if known)

  auxilliary_data::Array{Any, 1}   # eg. for the class group: the
                                   # type dependencies make it difficult

  tcontain::FakeFmpqMat            # Temporary variable for _check_elem_in_order
                                   # and den.
  tidempotents::fmpz_mat           # Temporary variable for idempotents()

  index_div::Dict{fmpz, Any}       # the index divisor splitting
                                   # Any = Array{NfAbsOrdIdl, Int}
                                   # but forward references are illegal

   function NfAbsOrd{S, T}(a::S) where {S, T}
    # "Default" constructor with default values.
    r = new{S, elem_type(S)}()
    r.nf = a
    r.parent = NfAbsOrdSet(a)
    r.signature = (-1,0)
    r.primesofmaximality = Vector{fmpz}()
    r.norm_change_const = (-1.0, -1.0)
    r.auxilliary_data = Array{Any}(10)
    r.isequation_order = false
    r.ismaximal = 0
    r.tcontain = FakeFmpqMat(zero_matrix(FlintZZ, 1, degree(a)))
    r.tidempotents = zero_matrix(FlintZZ, 1 + 2*degree(a), 1 + 2*degree(a))
    r.index_div = Dict{fmpz, Any}()
    return r
  end

  function NfAbsOrd{S, T}(K::S, x::FakeFmpqMat, xinv::FakeFmpqMat, B::Vector{T}, cached::Bool = false) where {S, T}
    if haskey(NfAbsOrdID, (K, x))
      return NfAbsOrdID[(K, x)]
    else
      z = NfAbsOrd{S, T}(K)
      n = degree(K)
      z.basis_nf = B
      z.basis_mat = x
      z.basis_mat_inv = xinv
      if cached
        NfAbsOrdID[(K, x)] = z
      end
      return z
    end
  end

  function NfAbsOrd{S, T}(K::S, x::FakeFmpqMat, cached::Bool = false) where {S, T}
    if haskey(NfAbsOrdID, (K, x))
      return NfAbsOrdID[(K, x)]
    else
      z = NfAbsOrd{S, T}(K)
      n = degree(K)
      B_K = basis(K)
      d = Vector{T}(n)
      for i in 1:n
        d[i] = elem_from_mat_row(K, x.num, i, x.den)
      end
      z.basis_nf = d
      z.basis_mat = x
      if cached
        NfAbsOrdID[(K, x)] = z
      end
      return z
    end
  end

  function NfAbsOrd{S, T}(b::Array{T, 1}, cached::Bool = false) where {S, T}
    K = parent(b[1])
    A = FakeFmpqMat(basis_mat(b))
    if haskey(NfAbsOrdID, (K,A))
      return NfAbsOrdID[(K,A)]
    else
      z = NfAbsOrd{parent_type(T), T}(K)
      z.basis_nf = b
      z.basis_mat = A
      if cached
        NfAbsOrdID[(K, A)] = z
      end
      return z
    end
  end
end

NfAbsOrd(K::S, x::FakeFmpqMat, xinv::FakeFmpqMat, B::Vector{T}, cached::Bool = false) where {S, T} = NfAbsOrd{S, T}(K, x, xinv, B, cached)

NfAbsOrd(K::S, x::FakeFmpqMat, cached::Bool = false) where {S} = NfAbsOrd{S, elem_type(S)}(K, x, cached)

NfAbsOrd(b::Array{T, 1}, cached::Bool = false) where {T} = NfAbsOrd{parent_type(T), T}(b, cached)

const NfOrd = NfAbsOrd{AnticNumberField, nf_elem}

const NfAbsOrdID = Dict{Tuple{AnticNumberField, FakeFmpqMat}, NfOrd}()

################################################################################
#
#  NfOrd/NfOrdElem
#
################################################################################

export NfOrdElem

export NfAbsOrdElem

mutable struct NfAbsOrdElem{S, T} <: RingElem
  elem_in_nf::T
  elem_in_basis::Vector{fmpz}
  has_coord::Bool
  parent::NfAbsOrd{S, T}

  function NfAbsOrdElem{S, T}(O::NfAbsOrd{S, T}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_nf = nf(O)()
    z.elem_in_basis = Vector{fmpz}(degree(O))
    z.has_coord = false
    return z
  end

  function NfAbsOrdElem{S, T}(O::NfAbsOrd{S, T}, a::T) where {S, T}
    z = new{S, T}()
    z.elem_in_nf = a
    z.elem_in_basis = Vector{fmpz}(degree(O))
    z.parent = O
    z.has_coord = false
    return z
  end

  function NfAbsOrdElem{S, T}(O::NfAbsOrd{S, T}, a::T, arr::Vector{fmpz}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_nf = a
    z.has_coord = true
    z.elem_in_basis = arr
    return z
  end

  function NfAbsOrdElem{S, T}(O::NfAbsOrd{S, T}, arr::Vector{fmpz}) where {S, T}
    z = new{S, T}()
    z.elem_in_nf = dot(O.basis_nf, arr)
    z.has_coord = true
    z.elem_in_basis = arr
    z.parent = O
    return z
  end

  function NfAbsOrdElem{S, T}(O::NfAbsOrd{S, T}, arr::Vector{U}) where {S, T, U <: Integer}
    return NfAbsOrdElem{S, T}(O, map(FlintZZ, arr))
  end

  function NfAbsOrdElem{S, T}(x::NfAbsOrdElem{S, T}) where {S, T}
    return deepcopy(x)  ### Check parent?
  end
end

NfAbsOrdElem(O::NfAbsOrd{S, T}) where {S, T} = NfAbsOrdElem{S, T}(O)

NfAbsOrdElem(O::NfAbsOrd{S, T}, a::T) where {S, T} = NfAbsOrdElem{S, T}(O, a)

NfAbsOrdElem(O::NfAbsOrd{S, T}, a::T, arr::Vector{fmpz}) where {S, T} = NfAbsOrdElem{S, T}(O, a, arr)

NfAbsOrdElem(O::NfAbsOrd{S, T}, arr::Vector{fmpz}) where {S, T} = NfAbsOrdElem{S, T}(O, arr)

NfAbsOrdElem(O::NfAbsOrd{S, T}, arr::Vector{U}) where {S, T, U <: Integer} = NfAbsOrdElem{S, T}(O, arr)

#NfAbsOrdElem(O::NfAbsOrd{S, T}, p::Integer) where {S, T} = NfAbsOrdElem{S, T}(O, p)

#NfAbsOrdElem(O::NfAbsOrd{S, T}, p::fmpz) where {S, T} = NfAbsOrdElem{S, T}(O, p)

const NfOrdElem = NfAbsOrdElem{AnticNumberField, nf_elem}

################################################################################
#
#  NfOrdIdlSet/NfOrdIdl
#
################################################################################

export NfOrdIdl

export NfAbsOrdIdl

mutable struct NfAbsOrdIdlSet{S, T}
  order::NfAbsOrd{S, T}

  function NfAbsOrdIdlSet{S, T}(O::NfAbsOrd{S, T}, cached::Bool = false) where {S, T}
    if haskey(NfAbsOrdIdlSetID, O)
      return NfAbsOrdIdlSetID[O]::NfAbsOrdIdlSet{S, T}
    else
      r = new{S, T}(O)
      if cached
        NfAbsOrdIdlSetID[O] = r
      end
      return r::NfAbsOrdIdlSet{S, T}
    end
  end
end

NfAbsOrdIdlSet(O::NfAbsOrd{S, T}, cached::Bool = false) where {S, T} = NfAbsOrdIdlSet{S, T}(O, cached)

const NfOrdIdlSet = NfAbsOrdIdlSet{AnticNumberField, nf_elem}

const NfAbsOrdIdlSetID = Dict{NfAbsOrd, NfAbsOrdIdlSet}()

@doc """
  NfOrdIdl(O::NfOrd, a::fmpz_mat) -> NfOrdIdl

    Creates the ideal of O with basis matrix a.
    No sanity checks. No data is copied, a should not be used anymore.

  NfOrdIdl(a::fmpz, b::NfOrdElem) -> NfOrdIdl

    Creates the ideal (a,b) of the order of b.
    No sanity checks. Note data is copied, a and b should not be used anymore.

  NfOrdIdl(O::NfOrd, a::fmpz, b::nf_elem) -> NfOrdIdl

    Creates the ideal (a,b) of O.
    No sanity checks. No data is copied, a and b should be used anymore.

  NfOrdIdl(x::NfOrdElem) -> NfOrdIdl

    Creates the principal ideal (x) of the order of O.
    No sanity checks. No data is copied, x should not be used anymore.

""" ->
type NfAbsOrdIdl{S, T}
  basis::Array{NfAbsOrdElem{S, T}, 1}
  basis_mat::fmpz_mat
  basis_mat_inv::FakeFmpqMat
  gen_one::fmpz
  gen_two::NfAbsOrdElem{S, T}
  gens_short::Bool
  gens_normal::fmpz
  gens_weakly_normal::Bool # true if Norm(A) = gcd(Norm, Norm)
                           # weaker than normality - at least potentially
  norm::fmpz
  minimum::fmpz
  is_prime::Int            # 0: don't know
                           # 1 known to be prime
                           # 2 known to be not prime
  iszero::Int             # as above
  is_principal::Int        # as above
  princ_gen::NfAbsOrdElem{S, T}
  princ_gen_special::Tuple{Int, Int, fmpz}
                           # Check if the ideal is generated by an integer
                           # First entry encodes the following:
                           # 0: don't know
                           # 1: second entry generates the ideal
                           # 2: third entry generates the ideal
  splitting_type::Tuple{Int, Int}
                           #
  anti_uniformizer::nf_elem

  valuation::Function      # a function returning "the" valuation -
                           # mind that the ideal is not prime

  parent::NfAbsOrdIdlSet{S, T}
  
  gens::Vector{NfAbsOrdElem{S, T}}  # A set of generators of the ideal 

  ## For residue fields of non-index divisors
  prim_elem::NfAbsOrdElem{S, T}
  min_poly_prim_elem::fmpz_poly  # minimal polynomial modulo P
  basis_in_prim::Vector{fmpz_mat} #

  function NfAbsOrdIdl{S, T}(O::NfAbsOrd{S, T}) where {S, T}
    # populate the bits types (Bool, Int) with default values
    r = new{S, T}()
    r.parent = NfAbsOrdIdlSet(O)
    r.gens_short = false
    r.gens_weakly_normal = false
    r.iszero = 0
    r.is_prime = 0
    r.is_principal = 0
    r.splitting_type = (0,0)
    return r
  end

  function NfAbsOrdIdl{S, T}(O::NfAbsOrd{S, T}, a::fmpz_mat) where {S, T}
    # create ideal of O with basis_matrix a
    # Note that the constructor 'destroys' a, a should not be used anymore
    r = NfAbsOrdIdl(O)
    r.basis_mat = a
    return r
  end

  function NfAbsOrdIdl{S, T}(a::fmpz, b::NfAbsOrdElem{S, T}) where {S, T}
    # create ideal (a,b) of order(b)
    r = NfAbsOrdIdl(parent(b))
    r.gen_one = a
    r.gen_two = b
    return r
  end

  function NfAbsOrdIdl{S, T}(O::NfAbsOrd{S, T}, a::fmpz, b::nf_elem) where {S, T}
    # create ideal (a,b) of O
    r = NfAbsOrdIdl(a, O(b, false))
    return r
  end

  function NfAbsOrdIdl{S, T}(O::NfAbsOrd{S, T}, a::NfAbsOrdElem{S, T}) where {S, T}
    return NfAbsOrdIdl(a)
  end

  function NfAbsOrdIdl{S, T}(x::NfAbsOrdElem{S, T}) where {S, T}
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    O = parent(x)
    C = NfAbsOrdIdl{S, T}(O)
    C.princ_gen = x
    C.is_principal = 1

    if iszero(x)
      C.iszero = 1
    end

    C.gen_one = abs(norm(x))
    C.gen_two = x

    C.gens_normal = C.gen_one
    C.gens_weakly_normal = true

    return C
  end

  function NfAbsOrdIdl{S, T}(O::NfAbsOrd{S, T}, x::Int) where {S, T}
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    C = NfAbsOrdIdl(O)
    C.princ_gen = O(x)
    C.is_principal = 1
    C.basis_mat = abs(x)*identity_matrix(FlintZZ, degree(O))
    C.princ_gen_special = (1, abs(x), fmpz(0))
    C.gen_one = x
    C.gen_two = O(x)
    C.norm = abs(x)^degree(O)
    C.minimum = fmpz(abs(x))
    C.gens_normal = x
    C.gens_weakly_normal = true
    return C
  end

  function NfAbsOrdIdl{S, T}(O::NfAbsOrd{S, T}, x::fmpz) where {S, T}
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    C = NfAbsOrdIdl(O)
    C.princ_gen = O(x)
    C.is_principal = 1
    C.basis_mat = abs(x)*identity_matrix(FlintZZ, degree(O))
    C.princ_gen_special = (2, Int(0), abs(x))
    C.gen_one = x
    C.gen_two = O(x)
    C.norm = abs(x)^degree(O)
    C.minimum = abs(x)
    C.gens_normal = x
    C.gens_weakly_normal = true
    return C
  end
end

NfAbsOrdIdl(a::fmpz, b::NfAbsOrdElem{S, T}) where {S, T} = NfAbsOrdIdl{S, T}(a, b)

NfAbsOrdIdl(O::NfAbsOrd{S, T}) where {S, T} = NfAbsOrdIdl{S, T}(O)

NfAbsOrdIdl(a::NfAbsOrdElem{S, T}) where {S, T} = NfAbsOrdIdl{S, T}(a)

NfAbsOrdIdl(O::NfAbsOrd{S, T}, a::fmpz_mat) where {S, T} = NfAbsOrdIdl{S, T}(O, a)

NfAbsOrdIdl(O::NfAbsOrd{S, T}, x::Int) where {S, T} = NfAbsOrdIdl{S, T}(O, x)

NfAbsOrdIdl(O::NfAbsOrd{S, T}, x::fmpz) where {S, T} = NfAbsOrdIdl{S, T}(O, x)

const NfOrdIdl = NfAbsOrdIdl{AnticNumberField, nf_elem}

################################################################################
#
#  NfOrdFracIdlSet/NfOrdFracIdl
#
################################################################################

mutable struct NfOrdFracIdlSet
   order::NfOrd

   function NfOrdFracIdlSet(O::NfOrd, cached::Bool=false)
     try
       return NfOrdFracIdlSetID[O]::NfOrdFracIdlSet
     catch
       r = new()
       r.order = O
       if cached
         NfOrdFracIdlSetID[O] = r
       end
       return r::NfOrdFracIdlSet
     end
   end
end

const NfOrdFracIdlSetID = Dict{NfOrd, NfOrdFracIdlSet}()

mutable struct NfOrdFracIdl
  num::NfOrdIdl
  den::fmpz
  norm::fmpq
  basis_mat::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat
  parent::NfOrdFracIdlSet

  function NfOrdFracIdl(O::NfOrd)
    z = new()
    z.parent = NfOrdFracIdlSet(O)
    return z
  end

  function NfOrdFracIdl(O::NfOrd, a::NfOrdIdl, b::fmpz)
    z = new()
    z.parent = NfOrdFracIdlSet(O)
    z.basis_mat = FakeFmpqMat(basis_mat(a), b)
    z.num = a
    z.den = b
    return z
  end

  function NfOrdFracIdl(O::NfOrd, a::FakeFmpqMat)
    z = new()
    z.parent = NfOrdFracIdlSet(O)
    z.basis_mat = a
    return z
  end

  function NfOrdFracIdl(x::NfOrdIdl, y::fmpz)
    z = new()
    z.parent = NfOrdFracIdlSet(order(x))
    z.num = x
    z.den = y
    return z
  end
  
  function NfOrdFracIdl(O::NfOrd, a::nf_elem)
    z = new()
    z.parent = NfOrdFracIdlSet(O)
    z.num = ideal(O, O(denominator(a, O)*a))
    z.den = denominator(a, O)
    z.basis_mat = hnf(FakeFmpqMat(representation_matrix(O(denominator(a, O)*a)), denominator(a, O)))
    return z
  end

end

################################################################################
#
#  UnitGrpCtx
#
################################################################################

mutable struct UnitGrpCtx{T <: Union{nf_elem, FacElem{nf_elem}}}
  order::NfOrd
  rank::Int
  full_rank::Bool
  units::Array{T, 1}
  regulator::arb
  tentative_regulator::arb
  regulator_precision::Int
  torsion_units::Array{NfOrdElem, 1}
  torsion_units_order::Int
  torsion_units_gen::NfOrdElem
  conj_log_cache::Dict{Int, Dict{nf_elem, arb}}
  conj_log_mat_cutoff::Dict{Int, arb_mat}
  conj_log_mat_cutoff_inv::Dict{Int, arb_mat}
  conj_log_mat::Tuple{arb_mat, Int}
  conj_log_mat_transpose::Tuple{arb_mat, Int}
  conj_log_mat_times_transpose::Tuple{arb_mat, Int}
  rel_add_prec::Int
  tors_prec::Int
  indep_prec::Int

  residue::arb

  unit_map::Map
  finished::Bool

  function UnitGrpCtx{T}(O::NfOrd) where {T}
    z = new{T}()
    z.order = O
    z.rank = -1
    z.full_rank = false
    z.regulator_precision = -1
    z.torsion_units_order = -1
    z.units = Array{T, 1}()
    z.conj_log_mat_cutoff = Dict{Int, arb_mat}()
    z.conj_log_mat_cutoff_inv = Dict{Int, arb_mat}()
    z.rel_add_prec = 32
    z.tors_prec = 16
    z.indep_prec = 16
    z.finished = false
    return z
  end
end

################################################################################
#
#  analytic_func
#
################################################################################

mutable struct analytic_func{T<:Number}
  coeff::Array{T, 1}
  valid::Tuple{T, T}

  function analytic_func{T}() where {T}
    return new{T}()
  end
end

################################################################################
#
#  BigComplex
#
################################################################################

mutable struct BigComplex
  re::BigFloat
  im::BigFloat
  function BigComplex(r::BigFloat)
    c = new()
    c.re = r
    c.im = zero(r)
    return c
  end

  function BigComplex(r::BigInt)
    return BigComplex(BigFloat(r))
  end

  function BigComplex(r::fmpz)
    return BigComplex(BigFloat(BigInt(r)))
  end

  function BigComplex(r::BigFloat, i::BigFloat)
    c = new()
    c.re = r
    c.im = i
    return c
  end

  function BigComplex(r::Complex{Float64})
    return BigComplex(BigFloat(Base.real(r)), BigFloat(Base.imag(r)))
  end

  function BigComplex(r::acb)
    return BigComplex(BigFloat(midpoint(real(r))), BigFloat(midpoint(imag(r))))
  end
end

################################################################################
#
#  roots_ctx
#
################################################################################

mutable struct roots_ctx
  f::fmpz_poly
  r_d::Array{BigComplex, 1}  # the 1st r1 ones will be real
  r::Array{BigComplex, 1}    # the complexes and at the end, the conjugated
  r1::Int
  r2::Int
  minkowski_mat::Array{BigFloat, 2} # caching: I currently
                                    # cannot extend number fields, so I cache it
                                    # here...
  minkowski_mat_p::Int

  cache::Array{BigFloat, 2} # to avoid allocation elsewhere.
  cache_z1::fmpz_mat
  cache_z2::fmpz_mat
  function roots_ctx()
    r = new()
    return r
  end
  function roots_ctx(K::AnticNumberField)
    try
      c = _get_roots_ctx_of_nf(K)::roots_ctx
      return c
    catch
      c = conjugates_init(K.pol)
      _set_roots_ctx_of_nf(K, c)
      return c
    end
  end
end

################################################################################
#
#  _RealRing
#
################################################################################

mutable struct _RealRing
  t1::BigFloat
  t2::BigFloat
  z1::BigInt
  zz1::fmpz
  function _RealRing()
    r = new()
    r.t1 = BigFloat(0)
    r.t2 = BigFloat(0)
    r.z1 = BigInt(0)
    r.zz1 = fmpz(0)
    return r
  end
end

RealRing() = R

################################################################################
#
#  Node
#
################################################################################

mutable struct node{T}
  content::T
  left::node{T}
  right::node{T}

  function node{T}(a::T) where {T}
    f = new{T}()
    f.content = a
    return f
  end

  function node{T}(a::T, b::node{T}, c::node{T}) where {T}
    f = node{T}(a)
    f.content = a
    f.right = b
    f.left = c
    return f
  end
end

################################################################################
#
#  FactorBase
#
################################################################################

mutable struct FactorBase{T}
  prod::T
  base::Union{Set{T}, AbstractArray{T, 1}}
  ptree::node{T}

  function FactorBase{T}(a::T, b::Set{T}) where {T}
    f = new{T}()
    f.prod = a
    f.base = b
    return f
  end

  function FactorBase{T}(a::T, b::AbstractArray{T, 1}) where {T}
    f = new{T}()
    f.prod = a
    f.base = b
    return f
  end
end

################################################################################
#
#  NfFactorBase
#
################################################################################

mutable struct FactorBaseSingleP
  P::fmpz
  pt::FactorBase{nmod_poly}
  lp::Array{Tuple{Int,NfOrdIdl}, 1}
  lf::Array{nmod_poly, 1}
  doit::Function

  function FactorBaseSingleP(p::fmpz, lp::Array{Tuple{Int, NfOrdIdl}, 1})
    FB = new()
    FB.lp = lp
    FB.P = p
    O = order(lp[1][2])
    K = O.nf

    if length(lp) >= 3 && !isindex_divisor(O, p) # ie. index divisor or so
      Zx = PolynomialRing(FlintZZ, "x")[1]
      Fpx = PolynomialRing(ResidueRing(FlintZZ, UInt(p), cached=false), "x", cached=false)[1]
      Qx = parent(K.pol)
      fp = Fpx(Zx(K.pol))
      lf = [ gcd(fp, Fpx(Zx(Qx(K(P[2].gen_two)))))::nmod_poly for P = lp]
      FB.lf = lf
      FB.pt = FactorBase(Set(lf), check = false)
    end  
    return FB
  end
end

function fb_doit(a::nf_elem, v::Int, sP::FactorBaseSingleP)
  if length(sP.lp) < 3 || isindex_divisor(order(sP.lp[1][2]), sP.P) # ie. index divisor or so
    return fb_naive_doit(a, v, sP)
  end
  d = denominator(a)
  if isone(gcd(d, sP.P)) return fb_int_doit(a, v, sP); end
  return fb_naive_doit(a, v, sP);
end

function fb_naive_doit(a::nf_elem, v::Int, sP::FactorBaseSingleP)
  lp = sP.lp
  r = Array{Tuple{Int, Int},1}()
  for x=1:length(lp)
    vl = valuation(a, lp[x][2])
    v -= vl*lp[x][2].splitting_type[2]
    if vl !=0
      push!(r, (lp[x][1], vl))
    end
  end
  return r, v
end

function fb_int_doit(a::nf_elem, v::Int, sP::FactorBaseSingleP)
  g = parent(sP.lf[1])(a)
  g = gcd(g, sP.pt.prod)
  fl = issmooth(sP.pt, g)[1]
  if fl
    d = factor(sP.pt, g)
    r = Array{Tuple{Int, Int}, 1}()
    vv=v
    for x in keys(d)
      id = findfirst(sP.lf, x)
      vv -= sP.lp[id][2].splitting_type[2]
      push!(r, (sP.lp[id][1], 1))
    end
    if vv == 0
      return r, vv
    end
    r = Array{Tuple{Int, Int}, 1}()
    for x in keys(d)
      id = findfirst(sP.lf, x)
      vl  = valuation(a, sP.lp[id][2])
      v -= sP.lp[id][2].splitting_type[2]*vl
      push!(r, (sP.lp[id][1], vl))
    end
    return r, v
  else
    return Array{Tuple{Int, Int}, 1}(), -1
  end
end

mutable struct NfFactorBase
  fb::Dict{fmpz, FactorBaseSingleP}
  size::Int
  fb_int::FactorBase{fmpz}
  ideals::Array{NfOrdIdl, 1}
  rw::Array{Int, 1}
  mx::Int

  function NfFactorBase()
    r = new(Dict{fmpz, Array{Tuple{Int, NfOrdIdl}, 1}}())
    r.size = 0
    return r
  end
end


################################################################################
#
#  sparse Z-modules
#
################################################################################

mutable struct ModuleCtxNmod
  R::NmodRing
  basis::SMat{nmod}
  gens::SMat{nmod}

  function ModuleCtxNmod()
    return new()
  end

  function ModuleCtxNmod(R::NmodRing, dim::Int)
    M = new()
    M.R = R
    M.basis = SMat(M.R)
    M.basis.c = dim
    M.gens = SMat(M.R)
    return M
  end

  function ModuleCtxNmod(p::Int, dim::Int)
    M = new()
    M.R = ResidueRing(FlintZZ, p, cached=false)
    M.basis = SMat(M.R)
    M.basis.c = dim
    M.gens = SMat(M.R)
    return M
  end
end

mutable struct ModuleCtx_fmpz
  bas_gens::SMat{fmpz}  # contains a max. indep system
  max_indep::SMat{fmpz} # the bas_gens in upper-triangular shape
  basis::SMat{fmpz}     # if set, probably a basis (in upper-triangular)
  rel_gens::SMat{fmpz}  # more elements, used for relations
  Mp::ModuleCtxNmod
  rel_reps_p::SMat{nmod}  # rel_reps_p[i] * Mp.basis = rel_gens[i] - if set
                        # at least mod p...
  basis_idx::fmpz
  essential_elementary_divisors::Array{fmpz, 1}
  new::Bool
  trafo::Any            # transformations bla

  function ModuleCtx_fmpz(dim::Int, p::Int = next_prime(2^20))
    M = new()
    M.max_indep = SMat(FlintZZ)
    M.max_indep.c = dim
    M.bas_gens = SMat(FlintZZ)
    M.bas_gens.c = dim
    M.rel_gens = SMat(FlintZZ)
    M.rel_gens.c = dim
    R = ResidueRing(FlintZZ, p, cached=false)
    M.rel_reps_p = SMat(R)
    M.new = false
    M.Mp = ModuleCtxNmod(R, dim)
    return M
  end
end

################################################################################
#
#  ClassGrpCtx
#
################################################################################

mutable struct RandIdlCtx
  base::Array{NfOrdIdl, 1}
  ibase::Array{NfOrdFracIdl, 1}
  rand::NfOrdIdl
  exp::Array{Int, 1}
  ub::fmpz
  lb::fmpz
  last::Set{Array{Int, 1}}
  function RandIdlCtx()
    return new()
  end
end

const nf_elem_or_fac_elem = Union{nf_elem, FacElem{nf_elem, AnticNumberField}}

mutable struct ClassGrpCtx{T}  # T should be a matrix type: either fmpz_mat or SMat{}
  FB::NfFactorBase

  M::ModuleCtx_fmpz
  R_gen::Array{nf_elem_or_fac_elem, 1}# the relations
  R_rel::Array{nf_elem_or_fac_elem, 1}
  RS::Set{UInt} #only the hash-values

  last_piv1::Array{Int, 1}
  mis::Set{Int}

  h::fmpz
  c::roots_ctx

  rel_cnt::Int
  bad_rel::Int
  hnf_call::Int
  time::Dict{Symbol, Float64}

  last::Int
  op::Array # of pairs: Map, perm where Map is a field automorphism
            # and perm is the induced operation on the factor base
            # difficult to type since we have many map types...
  aut_grp::Array # op contains the generators, sub_grp the entire group

  largePrimeCnt::Int
  B2::Int
  largePrime::Dict{fmpz_poly, Tuple{nf_elem, fmpq}}
  largePrime_success::Int
  largePrime_no_success::Int

  normStat::Dict{Int, Int}
  expect::Int

  randomClsEnv::RandIdlCtx

  val_base::fmpz_mat      # a basis for the possible infinite randomization
                          # vectors: conditions are
                          #  - sum over all = 0
                          #  - indices corresponding to complex pairs are
                          #    identical
                          # done via lll + nullspace

  rel_mat_full_rank::Bool
  H_trafo::Array{Any, 1}

  dl_data # Tuple{Int, fmpz_mat, AbelianGrp, fmpz_mat}
  cl_map::Map
  finished::Bool

  function ClassGrpCtx{T}() where {T}
    r = new{T}()
    r.R_gen = Array{nf_elem_or_fac_elem, 1}()
    r.R_rel = Array{nf_elem_or_fac_elem, 1}()
    r.RS = Set{UInt}()
    r.largePrimeCnt = 0
    r.largePrime = Dict{fmpz_poly, Tuple{nf_elem, fmpq}}()
    r.largePrime_success = 0
    r.largePrime_no_success = 0
    r.normStat = Dict{Int, Int}()
    r.time = Dict{Symbol, Float64}()
    r.B2 = 0
    r.H_trafo = []
    r.finished = false
    return r
  end
end

################################################################################
#
#  IdealRelationCtx
#
################################################################################

mutable struct IdealRelationsCtx{Tx, TU, TC}
  A::NfOrdIdl
  v::Array{Int, 1}  # the infinite valuation will be exp(v[i])
  E::enum_ctx{Tx, TU, TC}
  c::fmpz           # the last length
  cnt::Int
  bad::Int
  restart::Int
  M::fmpz_mat
  vl::Int
  rr::Range{Int}

  function IdealRelationsCtx{Tx, TU, TC}(clg::ClassGrpCtx, A::NfOrdIdl;
                 prec::Int = 100, val::Int=0, limit::Int = 0) where {Tx, TU, TC}
    v = matrix(FlintZZ, 1, rows(clg.val_base), Base.rand(-val:val, 1,
                    rows(clg.val_base)))*clg.val_base
    E = enum_ctx_from_ideal(A, v, prec = prec, limit = limit,
       Tx = Tx, TU = TU, TC = TC)::enum_ctx{Tx, TU, TC}
    I = new{Tx, TU, TC}()
    I.E = E
    I.A = A
    I.c = 0
    I.cnt = 0
    I.bad = 0
    I.restart = 0
    I.vl = 0
    I.rr = 1:0
    I.M = zero_matrix(FlintZZ, 1, I.E.n)
    return I
  end
end

################################################################################
#
#  Quotient rings of maximal orders of simple number fields
#
################################################################################

mutable struct NfOrdQuoRing <: Ring
  base_ring::NfOrd
  ideal::NfOrdIdl
  basis_mat::fmpz_mat
  basis_mat_array::Array{fmpz, 2}
  preinvn::Array{fmpz_preinvn_struct, 1}
  factor::Dict{NfOrdIdl, Int}

  # temporary variables for divisor and annihilator computations
  # don't use for anything else
  tmp_xxgcd::fmpz_mat # used only by xxgcd in NfOrd/ResidueRing.jl
  tmp_div::fmpz_mat # used only by div in NfOrd/ResidueRing.jl
  tmp_ann::fmpz_mat # used only by annihilator in NfOrd/ResidueRing.jl
  tmp_euc::fmpz_mat # used only by euclid in NfOrd/ResidueRing.jl

  multiplicative_group::Map

  function NfOrdQuoRing(O::NfOrd, I::NfOrdIdl)
    z = new()
    z.base_ring = O
    z.ideal = I
    z.basis_mat = basis_mat(I)
    z.basis_mat_array = Array(z.basis_mat)
    z.preinvn = [ fmpz_preinvn_struct(z.basis_mat[i, i]) for i in 1:degree(O)]
    d = degree(O)
    z.tmp_div = zero_matrix(FlintZZ, 2*d + 1, 2*d + 1)
    z.tmp_xxgcd = zero_matrix(FlintZZ, 3*d + 1, 3*d + 1)
    z.tmp_ann = zero_matrix(FlintZZ, 2*d, d)
    z.tmp_euc = zero_matrix(FlintZZ, 2*d, d)
    minimum(I) # compute the minimum
    return z
  end
end

mutable struct NfOrdQuoRingElem <: RingElem
  elem::NfOrdElem
  parent::NfOrdQuoRing

  function NfOrdQuoRingElem(O::NfOrdQuoRing, x::NfOrdElem)
    z = new()
    z.elem = mod(x, O)
    z.parent = O
    return z
  end
end

################################################################################
#
#  Finitely generated abelian groups and their elements
#
################################################################################

abstract type GrpAb <: Nemo.Group end

abstract type GrpAbElem <: Nemo.GroupElem end

mutable struct GrpAbFinGen <: GrpAb
  rels::fmpz_mat
  hnf::fmpz_mat
  issnf::Bool
  snf::Array{fmpz, 1}
  snf_map::Map{GrpAbFinGen, GrpAbFinGen}
  isfinalized::Bool

  function GrpAbFinGen(R::fmpz_mat, ishnf::Bool = false)
    r = new()
    r.issnf = false
    r.rels = R
    if ishnf
      r.hnf = R
    end
    r.isfinalized = false
    return r
  end
  
  function GrpAbFinGen(R::Array{fmpz, 1}, issnf::Bool = true)
    r = new()
    r.issnf = issnf
    r.snf = R
    r.isfinalized = false
    return r
  end
  
  function GrpAbFinGen(R::Array{T, 1}, issnf::Bool = true) where T <: Integer
    r = new()
    r.issnf = issnf
    r.snf = map(fmpz, R)
    r.isfinalized = false
    return r
  end

end

mutable struct GrpAbFinGenElem <: GrpAbElem
  parent::GrpAbFinGen
  coeff::fmpz_mat

  GrpAbFinGenElem() = new()
end

################################################################################
#
#  Maps
#
################################################################################

include("Map/MapType.jl")

################################################################################
#
#  NoElements
#
################################################################################

mutable struct NoElements <: Exception end

################################################################################
#
#  Infinite places
#
################################################################################

export Plc, InfPlc

abstract type Plc end

mutable struct InfPlc <: Plc
  K::AnticNumberField # Number field
  i::Int              # The position of the root r in conjugates_arb(a),
                      # where a is the primitive element of K
  r::acb              # Approximation of the root
  isreal::Bool        # True if and only if r is real

  function InfPlc(K::AnticNumberField, i::Int)
    z = new()
    z.K = K
    c = conjugate_data_arb(K)
    r1, r2 = c.signature
    if 1 <= i <= r1
      z.i = i
      z.isreal = true
      z.r = c.roots[i]
    elseif r1 + 1 <= i <= r1 + r2
      z.i = i
      z.isreal = false
      z.r = c.complex_roots[i - r1]
    elseif r1 + r2  + 1 <= i <=  r1 + 2*r2
      z.i = i - r2
      z.isreal = false
      z.r = c.complex_roots[i - r1 - r2]
    end
    return z
  end
end

################################################################################
#
#  Types
#
################################################################################

abstract type RelativeExtension{T} <: Nemo.Field end

mutable struct NfRel{T} <: RelativeExtension{T}
  base_ring::Nemo.Field
  pol::Generic.Poly{T}
  S::Symbol
  auxilliary_data::Array{Any, 1}

  function NfRel{T}(f::Generic.Poly{T}, s::Symbol, cached::Bool = false) where {T}
    if haskey(NfRelID, (parent(f), f, s))
      return NfRelID[parent(f), f, s]
    else
      z = new{T}()
      z.base_ring = base_ring(parent(f))
      z.pol = f
      z.S = s
      z.auxilliary_data = Array{Any}(5)
      if cached
        NfRelID[parent(f), f, s] = z
      end
      return z
    end
  end
end

const NfRelID = Dict{Tuple{Generic.PolyRing, Generic.Poly, Symbol},
                     NfRel}()

abstract type RelativeElement{T} <: Nemo.FieldElem end

mutable struct NfRelElem{T} <: RelativeElement{T}
  data::Generic.Poly{T}
  parent::NfRel{T}

  NfRelElem{T}(g::Generic.Poly{T}) where {T} = new{T}(g)
end

################################################################################
#
#  G-Modules
#
################################################################################

abstract type GModule end

export FqGModule, ZpnGModule

mutable struct ZpnGModule <: GModule
  R::Nemo.NmodRing
  V::GrpAbFinGen
  G::Array{nmod_mat,1}
  p::Int
  
  function ZpnGModule(V::GrpAbFinGen,G::Array{nmod_mat,1})
    @assert ngens(V)==cols(G[1]) && ngens(V)==rows(G[1])
    z=new()
    z.G=G
    z.V=V
    z.R=parent(G[1][1,1]) 
    f=factor(fmpz(z.R.n))
    @assert length(f.fac)==1
    z.p=Int(first(keys(f.fac)))
    return z
  end
  
end


mutable struct FqGModule <: GModule
  K::Nemo.FqNmodFiniteField
  G::Array{fq_nmod_mat,1}
  dim::Int
  isirreducible::Bool
  dim_spl_fld::Int
  
  function FqGModule(G::Array{fq_nmod_mat,1})
    z=new()
    z.G=G
    z.K=parent(G[1][1,1])
    z.dim=cols(G[1])
    if z.dim==1
      z.isirreducible=true
      z.dim_spl_fld=1
    else 
      z.dim_spl_fld=0
      z.isirreducible=false
    end
    
    return z
  end
end

###############################################################################
#
#  Graphs and Subgroup Lattice
#
###############################################################################

mutable struct Graph{T, M}
  edges::Dict{T, Dict{T, M}}
  degrees::Dict{T, Int}
  new_low_degrees::Dict{T, Void}

  function Graph{T, M}() where {T, M}
    z = new{T, M}()
    z.edges = Dict{T, Dict{T, M}}()
    z.degrees = Dict{T, Int}()
    z.new_low_degrees = Dict{T, Void}()
    return z
  end
end


mutable struct RelLattice{T <: Any, D <: Any}
  weak_vertices::WeakKeyDict{T, Void}
  graph::Graph{UInt, D}
  block_gc::Dict{T, Void}
  weak_vertices_rev::Dict{UInt, WeakRef}
  to_delete::Array{UInt, 1}
  zero::D # a generic object that will never actually be used.
  mult::Base.Callable #(D, D) -> D
  make_id::Base.Callable   # T -> D

  function RelLattice{T, D}() where {T, D}
    z = new()
    z.weak_vertices = WeakKeyDict{T, Void}()
    z.graph = Graph{UInt, D}()
    z.weak_vertices_rev = Dict{UInt, WeakRef}()
    z.to_delete = Array{UInt, 1}()
    z.block_gc = Dict{GrpAbFinGen, Void}()
    return z
  end
end

function GrpAbLatticeCreate()
  r = GrpAbLattice()
  r.zero = fmpz_mat(0,0)
  r.mult = *
  r.make_id = G::GrpAbFinGen -> identity_matrix(FlintZZ, ngens(G))
  return r
end

const GrpAbLattice = RelLattice{GrpAbFinGen, fmpz_mat}
const GroupLattice = GrpAbLatticeCreate()

###############################################################################
#
#  Pseudo matrix
#
###############################################################################

mutable struct PMat{T, S}
  parent
  matrix::Generic.Mat{T}
  coeffs::Array{S, 1}

  function PMat{T, S}(m::Generic.Mat{T}, c::Array{S, 1}) where {T, S}
    z = new{T, S}()
    z.matrix = m
    z.coeffs = c
    return z
  end

  function PMat{T, S}() where {T, S}
    z = new{T, S}()
    return z
  end
end

################################################################################
#
#  Absolute non-simple number fields
#
################################################################################

mutable struct NfAbsNS <: Nemo.Field
  pol::Array{fmpq_mpoly, 1}
  S::Array{Symbol, 1}
  basis#::Vector{NfAbsNSElem}
  degree::Int
  degrees::Vector{Int}

  function NfAbsNS(f::Array{fmpq_mpoly, 1}, S::Array{Symbol, 1}, cached::Bool = false)
    r = new()
    r.pol = f
    r.S = S
    return r
  end
end

mutable struct NfAbsNSElem <: Nemo.FieldElem
  data::fmpq_mpoly
  parent::NfAbsNS

  NfAbsNSElem(g::fmpq_mpoly) = new(g)
end
