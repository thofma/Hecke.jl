################################################################################
#
#  Maps
#
################################################################################

include("Map/MapType.jl")

################################################################################
#
#  Abstract types for number fields
#
################################################################################

"""
    NonSimpleNumField{T}

Common, abstract, overtype for all number fields that are (by type) generated
by more than one generator. `T` is the type of the elements of the coefficient field.
Typical example is a bi-quadratic field:
    QQ[sqrt 2, sqrt 3]
It can be converted to a simple extension (with maps), see e.g.
`absolute_simple_field` or `simple_extension`.
"""
abstract type NonSimpleNumField{T} <: NumField{T} end

"""
    NonSimpleNumFieldElem{T}

Common, abstract, overtype for elements of non-simple number fields, see
`NonSimpleNumField`
"""
abstract type NonSimpleNumFieldElem{T} <: NumFieldElem{T} end

################################################################################
#
#   Abstract types for orders
#
################################################################################

"""
    NumFieldOrder

Abstract overtype for all orders in number fields. An order is a unitary
subring that has the same ZZ-dimension as the QQ-dimension of the field.
"""
abstract type NumFieldOrder <: Ring end

abstract type NumFieldOrderElem <: RingElem end

################################################################################
#
#   Abstract types for ideals
#
################################################################################

"""
    NumFieldOrderIdeal

Common, abstract, type for all integral ideals in orders. See also
`NumFieldOrder`.
"""
abstract type NumFieldOrderIdeal end

"""
    NumFieldOrderFractionalIdeal

Common, abstract, type for all fractional ideals in orders, fractional
ideals are, as a set, just an integral ideal divided by some integer. See also
`NumFieldOrder`.
"""
abstract type NumFieldOrderFractionalIdeal end

################################################################################
#
#  Transformations for matrices
#
################################################################################

# 1 = scale
# 2 = swap
# 3 = add scaled
# 4 = parallel scaled addition
# 5 = trafo partial dense
# 6 = move row to other row (everything moves up)
# 7 = trafo id
mutable struct SparseTrafoElem{T, S}
  type::Int
  i::Int
  j::Int
  a::T
  b::T
  c::T
  d::T
  rows::UnitRange{Int}
  cols::UnitRange{Int}
  U::S

  function SparseTrafoElem{T, S}() where {T, S}
    z = new{T, S}()
    return z
  end
end

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
end

function TrafoPartialDense(i::Int, rows::AbstractUnitRange{Int},
                           cols::AbstractUnitRange{Int}, U::S) where S
  return TrafoPartialDense{S}(i, UnitRange(rows), UnitRange(cols), U)
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

  function fmpz_preinvn_struct(f::ZZRingElem)
    z = new()
    ccall((:fmpz_preinvn_init, libflint), Nothing,
          (Ref{fmpz_preinvn_struct}, Ref{ZZRingElem}), z, f)
    finalizer(_fmpz_preinvn_struct_clear_fn, z)
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
  roots::Vector{AcbFieldElem}
  real_roots::Vector{ArbFieldElem}
  complex_roots::Vector{AcbFieldElem}
end

mutable struct acb_root_ctx
  poly::QQPolyRingElem
  _roots::Ptr{acb_struct}
  prec::Int
  roots::Vector{AcbFieldElem}
  real_roots::Vector{ArbFieldElem}
  complex_roots::Vector{AcbFieldElem}
  signature::Tuple{Int, Int}

  function acb_root_ctx(x::QQPolyRingElem, p::Int = 32)
    z = new()
    z.roots = _roots(x, p, p)
    z.poly = x
    z.prec = p
    z._roots = acb_vec(degree(x))
    r, s = signature(x)
    z.signature = (r, s)

    for i = 1:degree(x)
      ccall((:acb_set, libarb), Nothing, (Ptr{acb_struct}, Ref{AcbFieldElem}),
            z._roots + (i - 1) * sizeof(acb_struct), z.roots[i])
    end

    z.prec = p
    A = Array{ArbFieldElem}(undef, z.signature[1])
    B = Array{AcbFieldElem}(undef, z.signature[2])

    for i in 1:r
      @assert isreal(z.roots[i])
      A[i] = real(z.roots[i])
    end

    j = 0
    for i in r+1:degree(x)
      if is_positive(imag(z.roots[i]))
        j += 1
        B[j] = z.roots[i]
      end
    end

    @assert j == s

    z.real_roots = A
    z.complex_roots = B

    finalizer(_acb_root_ctx_clear_fn, z)

    return z
  end
end

function _acb_root_ctx_clear_fn(x::acb_root_ctx)
  ccall((:_acb_vec_clear, libarb), Nothing,
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
#  Sparse rows
#
################################################################################

"""
    SRowSpace

Parent type for rows of sparse matrices.
"""
mutable struct SRowSpace{T} <: Ring
  base_ring::Ring

  function SRowSpace{T}(R::Ring, cached::Bool = false) where {T<:RingElem}
    return get_cached!(SRowSpaceDict, R, cached) do
      return new{T}(R)
    end::SRowSpace{T}
  end
end

const SRowSpaceDict = AbstractAlgebra.CacheDictType{Ring, SRowSpace}()

"""
    SRow{T, S}

Type for rows of sparse matrices, to create one use
`sparse_row`
`S` is the type of the array used for the values - see `ZZRingElem_Vector` for
an example.
"""
mutable struct SRow{T, S} # S <: AbstractVector{T}
  #in this row, in column pos[1] we have value values[1]
  base_ring
  values::S
  pos::Vector{Int}

  function SRow(R::NCRing)
    @assert R != ZZ
    S = sparse_inner_type(R)
    r = new{elem_type(R), S}(R, S(), Vector{Int}())
    return r
  end

  function SRow(R::NCRing, p::Vector{Int64}, S::AbstractVector; check::Bool = true)
    if check && any(iszero, S)
      p = copy(p)
      S = deepcopy(S)
      i=1
      while i <= length(p)
        if iszero(S[i])
          deleteat!(S, i)
          deleteat!(p, i)
        else
          i += 1
        end
      end
    end
    r = new{elem_type(R), typeof(S)}(R, S, p)
    @assert r isa sparse_row_type(R)
    return r
  end

  function SRow(R::NCRing, A::Vector{Tuple{Int, T}}) where T
    r = SRow(R)
    for (i, v) = A
      if !iszero(v)
        @assert parent(v) === R
        push!(r.pos, i)
        push!(r.values, v)
      end
    end
    return r
  end

  function SRow(R::NCRing, A::Vector{Tuple{Int, Int}})
    r = SRow(R)
    for (i, v) = A
      if !iszero(v)
        push!(r.pos, i)
        push!(r.values, R(v))
      end
    end
    return r
  end

  function SRow{T, S}(A::SRow{T, S}; copy::Bool = false) where {T, S}
    copy || return A
    @assert Vector{T} === S
    r = new{T, Vector{T}}(base_ring(A), Vector{T}(undef, length(A.pos)), copy(A.pos))
    for i=1:length(r.values)
      r.values[i] = A.values[i]
    end
    return r
  end

  function SRow{T}(R::NCRing, pos::Vector{Int}, val::Vector{T}) where {T}
    length(pos) == length(val) || error("Arrays must have same length")
    r = SRow(R)
    for i=1:length(pos)
      v = val[i]
      if !iszero(v)
        @assert parent(v) === R
        push!(r.pos, pos[i])
        push!(r.values, v)
      end
    end
    r.base_ring = R
    return
  end


end


# helper function used by SRow construct and also by the default
# methods for `sparse_matrix_type` and `sparse_row_type`.
sparse_inner_type(::T) where {T <: Union{NCRing, NCRingElem}} = sparse_inner_type(T)
sparse_inner_type(::Type{T}) where {T <: NCRing} = sparse_inner_type(elem_type(T))
sparse_inner_type(::Type{T}) where {T <: NCRingElem} = Vector{T}

################################################################################
#
#  Sparse matrices
#
################################################################################

"""
    SMatSpace

Parent for sparse matrices. Usually only created from a sparse matrix
via a call to parent.
"""
struct SMatSpace{T}
  rows::Int
  cols::Int
  base_ring::Ring

  function SMatSpace{T}(R::Ring, r::Int, c::Int) where {T}
    return new{T}(r, c, R)
  end
end

"""
    SMat{T}

Type of sparse matrices, to create one use `sparse_matrix`.
"""
mutable struct SMat{T, S}
  r::Int
  c::Int
  rows::Vector{SRow{T, S}}
  nnz::Int
  base_ring::Union{Ring, Nothing}
  tmp::Vector{SRow{T, S}}
  tmp_scalar::Vector{T}

  function SMat{T, S}() where {T, S}
    r = new{T, S}(0,0,Vector{SRow{T, S}}(), 0, nothing, Vector{SRow{T, S}}())
    return r
  end

  function SMat{T, S}(a::SMat{T, S}) where {S, T}
    r = new{T, S}(a.r, a.c, Array{SRow{T, S}}(undef, length(a.rows)), a.nnz, a.base_ring, Vector{SRow{T, S}}())
    for i=1:nrows(a)
      r.rows[i] = a.rows[i]
    end
    return r
  end
end

################################################################################
#
#  enum_ctx
#
################################################################################

# now that x is a ZZMatrix, the type for x is not really used
mutable struct enum_ctx{Tx, TC, TU}
  G::ZZMatrix
  n::Int
  limit::Int # stop recursion at level limit, defaults to n
  d::IntegerUnion #we actually want G/d
  C::Matrix{TC} # the pseudo-cholesky form - we don't have QQMatrix
  last_non_zero::Int
  x::ZZMatrix # 1 x n
  U::Vector{TU}
  L::Vector{TU}
  l::Vector{TU}
  tail::Vector{TU}
  c::ZZRingElem # the length of the elements we want
  t::ZZMatrix # if set, a transformation to be applied to all elements
  t_den::ZZRingElem
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
  G::ArbMatrix
  L::Vector{ZZMatrix}
  x::ZZMatrix
  p::Int

  function EnumCtxArb(G::ArbMatrix)
    z = new()
    z.G = G
    z.x = zero_matrix(ZZ, 1, nrows(G))
    z.p = precision(base_ring(G))
    return z
  end
end

################################################################################
#
#  FakeFmpqMatSpace/FakeFmpqMat
#
################################################################################

struct FakeFmpqMatSpace
  rows::Int
  cols::Int

  function FakeFmpqMatSpace(r::Int, c::Int)
    return new(r,c)
  end
end

"""
    FakeFmpqMat

A container type for a pair: an integer matrix (ZZMatrix) and an integer
denominator.
Used predominantly to represent bases of orders in absolute number fields.
"""
mutable struct FakeFmpqMat
  num::ZZMatrix
  den::ZZRingElem

  function FakeFmpqMat()
    z = new()
    return z
  end

  function FakeFmpqMat(x::ZZMatrix, y::ZZRingElem, simplified::Bool = false)
    z = new()
    z.num = x
    z.den = y
    if !simplified
      simplify_content!(z)
    end
    return z
  end

  function FakeFmpqMat(x::Tuple{ZZMatrix, ZZRingElem}, simplified::Bool = false)
    z = new()
    z.num = x[1]
    z.den = x[2]
    if !simplified
      simplify_content!(z)
    end
    return z
  end

  # TODO: Maybe this should be a copy option
  function FakeFmpqMat(x::ZZMatrix)
    z = new()
    z.num = x
    z.den = one(ZZ)
    return z
  end

  function FakeFmpqMat(x::QQMatrix)
    z = new()

    n, d = _fmpq_mat_to_fmpz_mat_den(x)

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

"""
    FacElemMon{S}

Parent for factored elements, ie. power products.
"""
mutable struct FacElemMon{S}
  base_ring::S  # for the base
  basis_conjugates_log::Dict{RingElem, Tuple{Int, Vector{ArbFieldElem}}}
  basis_conjugates::Dict{RingElem, Tuple{Int, Vector{ArbFieldElem}}}
  conj_log_cache::Dict{Int, Dict{AbsSimpleNumFieldElem, Vector{ArbFieldElem}}}

  function FacElemMon{S}(R::S, cached::Bool = false) where {S}
    return get_cached!(FacElemMonDict, R, cached) do
      new{S}(R,
        Dict{RingElem, Vector{ArbFieldElem}}(),
        Dict{RingElem, Vector{ArbFieldElem}}(),
        Dict{Int, Dict{AbsSimpleNumFieldElem, Vector{ArbFieldElem}}}()
        )
    end::FacElemMon{S}
  end

  function FacElemMon{AbsSimpleNumField}(R::AbsSimpleNumField, cached::Bool = true)
    if haskey(FacElemMonDict, R)
      return FacElemMonDict[R]::FacElemMon{AbsSimpleNumField}
    end
    if has_attribute(R, :fac_elem_mon)
      F = get_attribute(R, :fac_elem_mon)::FacElemMon{AbsSimpleNumField}
      return F
    end
    z = new{AbsSimpleNumField}(R,
      Dict{RingElem, Vector{ArbFieldElem}}(),
      Dict{RingElem, Vector{ArbFieldElem}}(),
      Dict{Int, Dict{AbsSimpleNumFieldElem, Vector{ArbFieldElem}}}()
      )
    if cached
      set_attribute!(R, :fac_elem_mon => z)
    end
    return z
  end
end

FacElemMon(R::S) where {S} = FacElemMon{S}(R)

const FacElemMonDict = AbstractAlgebra.CacheDictType()

"""
    FacElem{B, S}

Type for factored elements, that is elements of the form
    prod a_i^k_i
for elements `a_i` of type `B` in a ring of type `S`.
"""
mutable struct FacElem{B, S}
  fac::Dict{B, ZZRingElem}
  hash::UInt
  parent::FacElemMon{S}

  function FacElem{B, S}() where {B, S}
    z = new{B, S}()
    z.fac = Dict{B, ZZRingElem}()
    z.hash = UInt(0)
    return z
  end
end


################################################################################
#
#  AbsNumFieldOrderSet/AbsSimpleNumFieldOrder
#
################################################################################

mutable struct AbsNumFieldOrderSet{T}
  nf::T

  function AbsNumFieldOrderSet{T}(a::T, cached::Bool = false) where {T}
    return get_cached!(AbsNumFieldOrderSetID, a, cached) do
      return new{T}(a)::AbsNumFieldOrderSet{T}
    end::AbsNumFieldOrderSet{T}
  end
end

AbsNumFieldOrderSet(a::T, cached::Bool = false) where {T} = AbsNumFieldOrderSet{T}(a, cached)

const AbsNumFieldOrderSetID = AbstractAlgebra.CacheDictType{NumField, AbsNumFieldOrderSet}()

@attributes mutable struct AbsNumFieldOrder{S, T} <: NumFieldOrder
  nf::S
  basis_nf::Vector{T}        # Basis as array of number field elements
  basis_ord#::Vector{AbsNumFieldOrderElem}    # Basis as array of order elements
  basis_matrix::FakeFmpqMat           # Basis matrix of order wrt basis of K
  basis_mat_inv::FakeFmpqMat          # Inverse of basis matrix
  gen_index::QQFieldElem              # The det of basis_mat_inv as QQFieldElem
  index::ZZRingElem                   # The det of basis_mat_inv
                                      # (this is the index of the equation order
                                      #  in the given order)
  disc::ZZRingElem                    # Discriminant
  is_equation_order::Bool             # Equation order of ambient number field?

  minkowski_matrix::Tuple{ArbMatrix, Int}        # Minkowski matrix
  minkowski_gram_mat_scaled::Tuple{ZZMatrix, Int} # Minkowski matrix - gram * 2^prec and rounded
  minkowski_gram_CMfields::ZZMatrix
  complex_conjugation_CM::Map

  torsion_units#::Tuple{Int, AbsNumFieldOrderElem}

  is_maximal::Int                  # 0 Not known
                                   # 1 Known to be maximal
                                   # 2 Known to not be maximal

  primesofmaximality::Vector{ZZRingElem} # primes at the which the order is known to
                                   # to be maximal

  norm_change_const::Tuple{BigFloat, BigFloat}
                                   # Tuple c1, c2 as in the paper of
                                   # Fieker-Friedrich
  trace_mat::ZZMatrix              # The trace matrix (if known)

  tcontain::FakeFmpqMat            # Temporary variable for _check_elem_in_order
                                   # and den.
  tcontain_fmpz::ZZRingElem        # Temporary variable for _check_elem_in_order
  tcontain_fmpz2::ZZRingElem       # Temporary variable for _check_elem_in_order
  tidempotents::ZZMatrix           # Temporary variable for idempotents()

  index_div::Dict{ZZRingElem, Vector}    # the index divisor splitting
                                   # Any = Array{AbsNumFieldOrderIdeal, Int}
                                   # but forward references are illegal

  lllO::AbsNumFieldOrder{S, T}             # the same order with a lll-reduced basis

   function AbsNumFieldOrder{S, T}(a::S) where {S, T}
    # "Default" constructor with default values.
    r = new{S, elem_type(S)}()
    r.nf = a
    #r.signature = (-1,0)
    r.primesofmaximality = Vector{ZZRingElem}()
    #r.norm_change_const = (-1.0, -1.0)
    r.is_equation_order = false
    r.is_maximal = 0
    r.tcontain = FakeFmpqMat(zero_matrix(ZZ, 1, degree(a)))
    r.tcontain_fmpz = ZZRingElem()
    r.tcontain_fmpz2 = ZZRingElem()
    r.tidempotents = zero_matrix(ZZ, 1 + 2*degree(a), 1 + 2*degree(a))
    r.index_div = Dict{ZZRingElem, Vector}()
    return r
  end

  function AbsNumFieldOrder{S, T}(K::S, x::FakeFmpqMat, xinv::FakeFmpqMat, B::Vector{T}, cached::Bool = false) where {S, T}
    return get_cached!(AbsNumFieldOrderID, (K, x), cached) do
      z = AbsNumFieldOrder{S, T}(K)
      n = degree(K)
      z.basis_nf = B
      z.basis_matrix = x
      z.basis_mat_inv = xinv
      return z
    end::AbsNumFieldOrder{S, T}
  end

  function AbsNumFieldOrder{S, T}(K::S, x::FakeFmpqMat, cached::Bool = false) where {S, T}
    return get_cached!(AbsNumFieldOrderID, (K, x), cached) do
      z = AbsNumFieldOrder{S, T}(K)
      n = degree(K)
      B_K = basis(K)
      d = Vector{T}(undef, n)
      for i in 1:n
        d[i] = elem_from_mat_row(K, x.num, i, x.den)
      end
      z.basis_nf = d
      z.basis_matrix = x
      return z
    end::AbsNumFieldOrder{S, T}
  end

  function AbsNumFieldOrder{S, T}(b::Vector{T}, cached::Bool = false) where {S, T}
    K = parent(b[1])
    A = basis_matrix(b, FakeFmpqMat)
    return get_cached!(AbsNumFieldOrderID, (K, A), cached) do
      z = AbsNumFieldOrder{parent_type(T), T}(K)
      z.basis_nf = b
      z.basis_matrix = A
      return z
    end::AbsNumFieldOrder{S, T}
  end
end

AbsNumFieldOrder(K::S, x::FakeFmpqMat, xinv::FakeFmpqMat, B::Vector{T}, cached::Bool = false) where {S, T} = AbsNumFieldOrder{S, T}(K, x, xinv, B, cached)

AbsNumFieldOrder(K::S, x::FakeFmpqMat, cached::Bool = false) where {S} = AbsNumFieldOrder{S, elem_type(S)}(K, x, cached)

AbsNumFieldOrder(b::Vector{T}, cached::Bool = false) where {T} = AbsNumFieldOrder{parent_type(T), T}(b, cached)

const AbsNumFieldOrderID = AbstractAlgebra.CacheDictType{Tuple{Any, FakeFmpqMat}, AbsNumFieldOrder}()

const AbsSimpleNumFieldOrder = AbsNumFieldOrder{AbsSimpleNumField, AbsSimpleNumFieldElem}

################################################################################
#
#  AbsSimpleNumFieldOrder/AbsSimpleNumFieldOrderElem
#
################################################################################

mutable struct AbsNumFieldOrderElem{S, T} <: NumFieldOrderElem
  elem_in_nf::T
  coordinates::Vector{ZZRingElem}
  has_coord::Bool
  parent::AbsNumFieldOrder{S, T}

  function AbsNumFieldOrderElem{S, T}(O::AbsNumFieldOrder{S, T}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_nf = nf(O)()
    z.coordinates = Vector{ZZRingElem}(undef, degree(O))
    z.has_coord = false
    return z
  end

  function AbsNumFieldOrderElem{S, T}(O::AbsNumFieldOrder{S, T}, a::T) where {S, T}
    z = new{S, T}()
    z.elem_in_nf = a
    z.coordinates = Vector{ZZRingElem}(undef, degree(O))
    z.parent = O
    z.has_coord = false
    return z
  end

  function AbsNumFieldOrderElem{S, T}(O::AbsNumFieldOrder{S, T}, a::T, arr::Vector{ZZRingElem}) where {S, T}
    z = new{S, T}()
    z.parent = O
    z.elem_in_nf = a
    z.has_coord = true
    z.coordinates = arr
    return z
  end

  function AbsNumFieldOrderElem{S, T}(O::AbsNumFieldOrder{S, T}, arr::ZZMatrix) where {S, T}
    (nrows(arr) > 1 && ncols(arr) > 1) &&
        error("Matrix must have 1 row or 1 column")

    z = new{S, T}()
    y = zero(nf(O))
    for i in 1:degree(O)
      y += arr[i] * O.basis_nf[i]
    end
    z.elem_in_nf = y
    z.has_coord = true
    z.coordinates = reshape(collect(arr), :)
    z.parent = O
    return z
  end

  function AbsNumFieldOrderElem{S, T}(O::AbsNumFieldOrder{S, T}, arr::Vector{ZZRingElem}) where {S, T}
    z = new{S, T}()
    k = nf(O)
    if isa(k, AbsSimpleNumField)
      if is_equation_order(O)
        z.elem_in_nf = k(k.pol.parent(arr))
      else
        #avoids rational (polynomial) arithmetic
        xx = arr*O.basis_matrix.num
        z.elem_in_nf = divexact(k(k.pol.parent(xx)), O.basis_matrix.den)
      end
    else
      z.elem_in_nf = dot(O.basis_nf, arr)
    end
    z.has_coord = true
    z.coordinates = arr
    z.parent = O
    return z
  end

  function AbsNumFieldOrderElem{S, T}(O::AbsNumFieldOrder{S, T}, arr::Vector{U}) where {S, T, U <: Integer}
    return AbsNumFieldOrderElem{S, T}(O, map(ZZ, arr))
  end

  function AbsNumFieldOrderElem{S, T}(x::AbsNumFieldOrderElem{S, T}) where {S, T}
    return deepcopy(x)  ### Check parent?
  end
end

AbsNumFieldOrderElem(O::AbsNumFieldOrder{S, T}) where {S, T} = AbsNumFieldOrderElem{S, T}(O)

AbsNumFieldOrderElem(O::AbsNumFieldOrder{S, T}, a::T) where {S, T} = AbsNumFieldOrderElem{S, T}(O, a)

AbsNumFieldOrderElem(O::AbsNumFieldOrder{S, T}, a::T, arr::Vector{ZZRingElem}) where {S, T} = AbsNumFieldOrderElem{S, T}(O, a, arr)

AbsNumFieldOrderElem(O::AbsNumFieldOrder{S, T}, arr::Vector{ZZRingElem}) where {S, T} = AbsNumFieldOrderElem{S, T}(O, arr)

AbsNumFieldOrderElem(O::AbsNumFieldOrder{S, T}, arr::ZZMatrix) where {S, T} = AbsNumFieldOrderElem{S, T}(O, arr)

AbsNumFieldOrderElem(O::AbsNumFieldOrder{S, T}, arr::Vector{U}) where {S, T, U <: Integer} = AbsNumFieldOrderElem{S, T}(O, arr)

#AbsNumFieldOrderElem(O::AbsNumFieldOrder{S, T}, p::Integer) where {S, T} = AbsNumFieldOrderElem{S, T}(O, p)

#AbsNumFieldOrderElem(O::AbsNumFieldOrder{S, T}, p::ZZRingElem) where {S, T} = AbsNumFieldOrderElem{S, T}(O, p)

const AbsSimpleNumFieldOrderElem = AbsNumFieldOrderElem{AbsSimpleNumField,AbsSimpleNumFieldElem}

################################################################################
#
#  AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}/AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
#
################################################################################

struct AbsNumFieldOrderIdealSet{S, T}
  order::AbsNumFieldOrder{S, T}

  function AbsNumFieldOrderIdealSet{S, T}(O::AbsNumFieldOrder{S, T}, cached::Bool = false) where {S, T}
    return get_cached!(AbsNumFieldOrderIdealSetID, O, cached) do
      return new{S, T}(O)
    end::AbsNumFieldOrderIdealSet{S, T}
  end
end

function AbsNumFieldOrderIdealSet(O::AbsNumFieldOrder{S, T}, cached::Bool = false) where {S, T}
  return AbsNumFieldOrderIdealSet{S, T}(O, cached)
end

const AbsNumFieldOrderIdealSetID = AbstractAlgebra.CacheDictType{AbsNumFieldOrder, AbsNumFieldOrderIdealSet}()

@doc raw"""
    AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(O::AbsSimpleNumFieldOrder, a::ZZMatrix) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

    Creates the ideal of $O$ with basis matrix $a$.
    No sanity checks. No data is copied, $a$ should not be used anymore.

  AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(a::ZZRingElem, b::AbsSimpleNumFieldOrderElem) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

    Creates the ideal $(a,b)$ of the order of $b$.
    No sanity checks. No data is copied, $a$ and $b$ should not be used anymore.

  AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(O::AbsSimpleNumFieldOrder, a::ZZRingElem, b::AbsSimpleNumFieldElem) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

    Creates the ideal $(a,b)$ of $O$.
    No sanity checks. No data is copied, $a$ and $b$ should not be used anymore.

  AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}(x::AbsSimpleNumFieldOrderElem) -> AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

    Creates the principal ideal $(x)$ of the order of $O$.
    No sanity checks. No data is copied, $x$ should not be used anymore.

"""
@attributes mutable struct AbsNumFieldOrderIdeal{S, T} <: NumFieldOrderIdeal
  order::AbsNumFieldOrder{S, T}
  basis::Vector{AbsNumFieldOrderElem{S, T}}
  basis_matrix::ZZMatrix
  basis_mat_inv::FakeFmpqMat
  lll_basis_matrix::ZZMatrix
  gen_one::ZZRingElem
  gen_two::AbsNumFieldOrderElem{S, T}
  gens_short::Bool
  gens_normal::ZZRingElem
  gens_weakly_normal::Bool # true if Norm(A) = gcd(Norm, Norm)
                           # weaker than normality - at least potentially
  norm::ZZRingElem
  minimum::ZZRingElem
  is_prime::Int            # 0: don't know
                           # 1 known to be prime
                           # 2 known to be not prime
  iszero::Int              # as above
  is_principal::Int        # as above
  princ_gen::AbsNumFieldOrderElem{S, T}
  princ_gen_fac_elem::FacElem{T, S}
  princ_gen_special::Tuple{Int, Int, ZZRingElem}
                           # Check if the ideal is generated by an integer
                           # First entry encodes the following:
                           # 0: don't know
                           # 1: second entry generates the ideal
                           # 2: third entry generates the ideal
  splitting_type::Tuple{Int, Int}
                           #ordered as ramification index, inertia degree
  anti_uniformizer::T

  valuation::Function      # a function returning "the" valuation -
                           # mind that the ideal is not prime

  gens::Vector{AbsNumFieldOrderElem{S, T}}  # A set of generators of the ideal

  ## For residue fields of non-index divisors
  prim_elem::AbsNumFieldOrderElem{S, T}
  min_poly_prim_elem::ZZPolyRingElem  # minimal polynomial modulo P
  basis_in_prim::Vector{ZZMatrix} #
  phi::MapFromFunc{ZZRing, FqField}

  function AbsNumFieldOrderIdeal{S, T}(O::AbsNumFieldOrder{S, T}) where {S, T}
    # populate the bits types (Bool, Int) with default values
    r = new{S, T}()
    r.order = O
    r.gens_short = false
    r.gens_weakly_normal = false
    r.iszero = 0
    r.is_prime = 0
    r.is_principal = 0
    r.splitting_type = (0,0)
    return r
  end

  function AbsNumFieldOrderIdeal{S, T}(O::AbsNumFieldOrder{S, T}, a::ZZMatrix) where {S, T}
    # create ideal of O with basis_matrix a
    # Note that the constructor 'destroys' a, a should not be used anymore
    r = AbsNumFieldOrderIdeal(O)
    r.basis_matrix = a
    return r
  end

  function AbsNumFieldOrderIdeal{S, T}(a::ZZRingElem, b::AbsNumFieldOrderElem{S, T}) where {S, T}
    # create ideal (a,b) of order(b)
    r = AbsNumFieldOrderIdeal(parent(b))
    r.gen_one = a
    r.gen_two = b
    return r
  end

  function AbsNumFieldOrderIdeal{S, T}(O::AbsNumFieldOrder{S, T}, a::ZZRingElem, b::AbsSimpleNumFieldElem) where {S, T}
    # create ideal (a,b) of O
    r = AbsNumFieldOrderIdeal(a, O(b, false))
    return r
  end

  function AbsNumFieldOrderIdeal{S, T}(O::AbsNumFieldOrder{S, T}, a::AbsNumFieldOrderElem{S, T}) where {S, T}
    return AbsNumFieldOrderIdeal(a)
  end

  function AbsNumFieldOrderIdeal{S, T}(x::AbsNumFieldOrderElem{S, T}) where {S, T}
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    O = parent(x)
    C = AbsNumFieldOrderIdeal{S, T}(O)
    C.princ_gen = x
    C.princ_gen_fac_elem = FacElem(elem_in_nf(x))
    C.is_principal = 1

    if iszero(x)
      C.iszero = 1
    end
    C.norm = abs(norm(x))
    C.gen_one = C.norm
    C.gen_two = x

    C.gens_normal = C.gen_one
    C.gens_weakly_normal = true

    return C
  end

  function AbsNumFieldOrderIdeal{S, T}(O::AbsNumFieldOrder{S, T}, x::Int) where {S, T}
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    C = AbsNumFieldOrderIdeal(O)
    C.princ_gen = O(x)
    C.princ_gen_fac_elem = FacElem(nf(O)(x))
    C.is_principal = 1
    C.princ_gen_special = (1, abs(x), ZZRingElem(0))
    if is_zero(x)
      C.iszero = 1
    end
    C.gen_one = ZZRingElem(x)
    C.gen_two = O(x)
    C.norm = ZZRingElem(abs(x))^degree(O)
    C.minimum = ZZRingElem(abs(x))
    C.gens_normal = ZZRingElem(x)
    C.gens_weakly_normal = true
    return C
  end

  function AbsNumFieldOrderIdeal{S, T}(O::AbsNumFieldOrder{S, T}, x::ZZRingElem) where {S, T}
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    C = AbsNumFieldOrderIdeal(O)
    C.princ_gen = O(x)
    C.princ_gen_fac_elem = FacElem(nf(O)(x))
    C.is_principal = 1
    C.princ_gen_special = (2, Int(0), abs(x))
    if is_zero(x)
      C.iszero = 1
    end
    C.gen_one = x
    C.gen_two = O(x)
    C.norm = abs(x)^degree(O)
    C.minimum = abs(x)
    C.gens_normal = x
    C.gens_weakly_normal = true
    return C
  end
end

AbsNumFieldOrderIdeal(a::ZZRingElem, b::AbsNumFieldOrderElem{S, T}) where {S, T} = AbsNumFieldOrderIdeal{S, T}(a, b)

AbsNumFieldOrderIdeal(O::AbsNumFieldOrder{S, T}) where {S, T} = AbsNumFieldOrderIdeal{S, T}(O)

AbsNumFieldOrderIdeal(a::AbsNumFieldOrderElem{S, T}) where {S, T} = AbsNumFieldOrderIdeal{S, T}(a)

AbsNumFieldOrderIdeal(O::AbsNumFieldOrder{S, T}, a::ZZMatrix) where {S, T} = AbsNumFieldOrderIdeal{S, T}(O, a)

AbsNumFieldOrderIdeal(O::AbsNumFieldOrder{S, T}, x::Int) where {S, T} = AbsNumFieldOrderIdeal{S, T}(O, x)

AbsNumFieldOrderIdeal(O::AbsNumFieldOrder{S, T}, x::ZZRingElem) where {S, T} = AbsNumFieldOrderIdeal{S, T}(O, x)

const AbsSimpleNumFieldOrderIdeal = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

################################################################################
#
#  AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}/AbsSimpleNumFieldOrderFractionalIdeal
#
################################################################################

mutable struct AbsNumFieldOrderFractionalIdealSet{S, T}
  order::AbsNumFieldOrder{S, T}

  function AbsNumFieldOrderFractionalIdealSet{S, T}(O::AbsNumFieldOrder{S, T}, cached::Bool=false) where {S, T}
    return get_cached!(AbsNumFieldOrderFractionalIdealSetID, O, cached) do
      return new{S, T}(O)
    end::AbsNumFieldOrderFractionalIdealSet{S, T}
  end
end

const AbsNumFieldOrderFractionalIdealSetID = AbstractAlgebra.CacheDictType{AbsNumFieldOrder, AbsNumFieldOrderFractionalIdealSet}()

mutable struct AbsNumFieldOrderFractionalIdeal{S, T} <: NumFieldOrderFractionalIdeal
  order::AbsNumFieldOrder{S, T}
  num::AbsNumFieldOrderIdeal{S, T}
  den::ZZRingElem
  norm::QQFieldElem
  basis_matrix::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat
  basis::Vector{T}

  function AbsNumFieldOrderFractionalIdeal{S, T}(O::AbsNumFieldOrder{S, T}) where {S, T}
    z = new{S, T}()
    z.order = O
    return z
  end

  function AbsNumFieldOrderFractionalIdeal{S, T}(O::AbsNumFieldOrder{S, T}, a::AbsNumFieldOrderIdeal{S, T}, b::ZZRingElem) where {S, T}
    z = new{S, T}()
    z.order = O
    b = abs(b)
    #z.basis_matrix = FakeFmpqMat(basis_matrix(a), deepcopy(b))
    z.num = a
    z.den = b
    return z
  end

  function AbsNumFieldOrderFractionalIdeal{S, T}(O::AbsNumFieldOrder{S, T}, a::FakeFmpqMat) where {S, T}
    z = new{S, T}()
    z.order = O
    z.basis_matrix = a
    return z
  end

  function AbsNumFieldOrderFractionalIdeal{S, T}(x::AbsNumFieldOrderIdeal{S, T}, y::ZZRingElem) where {S, T}
    z = new{S, T}()
    z.order = order(x)
    z.num = x
    z.den = abs(y)
    return z
  end

  function AbsNumFieldOrderFractionalIdeal{S, T}(O::AbsNumFieldOrder{S, T}, a::T) where {S, T}
    z = new{S, T}()
    z.order = O
    d = denominator(a, O)
    z.num = ideal(O, O(d*a, false))
    z.den = d
    #z.basis_matrix = hnf(FakeFmpqMat(representation_matrix(O(denominator(a, O)*a)), denominator(a, O)))
    return z
  end
end

function AbsNumFieldOrderFractionalIdeal(O::AbsNumFieldOrder{S, T}) where {S, T}
  return AbsNumFieldOrderFractionalIdeal{S, T}(O)
end

function AbsNumFieldOrderFractionalIdeal(O::AbsNumFieldOrder{S, T},
                         a::AbsNumFieldOrderIdeal{S, T}, b::ZZRingElem) where {S, T}
  return AbsNumFieldOrderFractionalIdeal{S, T}(O, a, b)
end

function AbsNumFieldOrderFractionalIdeal(O::AbsNumFieldOrder{S, T}, a::FakeFmpqMat) where {S, T}
  return AbsNumFieldOrderFractionalIdeal{S, T}(O, a)
end

function AbsNumFieldOrderFractionalIdeal(x::AbsNumFieldOrderIdeal{S, T}, y::ZZRingElem) where {S, T}
  return AbsNumFieldOrderFractionalIdeal{S, T}(x, y)
end

function AbsNumFieldOrderFractionalIdeal(O::AbsNumFieldOrder{S, T}, a::T) where {S, T}
  return AbsNumFieldOrderFractionalIdeal{S, T}(O, a)
end

const AbsSimpleNumFieldOrderFractionalIdeal = AbsNumFieldOrderFractionalIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

################################################################################
#
#  UnitGrpCtx
#
################################################################################

mutable struct UnitGrpCtx{T <: Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem}}}
  order::AbsSimpleNumFieldOrder
  rank::Int
  full_rank::Bool
  units::Vector{T}
  regulator::ArbFieldElem
  tentative_regulator::ArbFieldElem
  regulator_precision::Int
  #torsion_units::Vector{AbsSimpleNumFieldOrderElem}
  torsion_units_order::Int
  torsion_units_gen::AbsSimpleNumFieldOrderElem
  conj_log_cache::Dict{Int, Dict{AbsSimpleNumFieldElem, ArbFieldElem}}
  conj_log_mat_cutoff::Dict{Int, ArbMatrix}
  conj_log_mat_cutoff_inv::Dict{Int, ArbMatrix}
  conj_log_mat::Tuple{ArbMatrix, Int}
  conj_log_mat_transpose::Tuple{ArbMatrix, Int}
  conj_log_mat_times_transpose::Tuple{ArbMatrix, Int}
  rel_add_prec::Int
  tors_prec::Int
  indep_prec::Int

  residue::ArbFieldElem

  unit_map::Map
  finished::Bool
  auts# automorphisms of the field
  cache::Vector{Dict{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}}
  relations_used::Vector{Int}

  GRH::Bool

  function UnitGrpCtx{T}(O::AbsSimpleNumFieldOrder) where {T}
    z = new{T}()
    z.order = O
    z.rank = -1
    z.full_rank = false
    z.GRH = true
    z.regulator_precision = -1
    z.torsion_units_order = -1
    z.units = Vector{T}()
    z.conj_log_mat_cutoff = Dict{Int, ArbMatrix}()
    z.conj_log_mat_cutoff_inv = Dict{Int, ArbMatrix}()
    z.rel_add_prec = 32
    z.tors_prec = 16
    z.indep_prec = 16
    z.finished = false
    relations_used = Vector{Int}()
    return z
  end
end

################################################################################
#
#  analytic_func
#
################################################################################

mutable struct analytic_func{T<:Number}
  coeff::Vector{T}
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

  function BigComplex(r::ZZRingElem)
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

  function BigComplex(r::AcbFieldElem)
    return BigComplex(BigFloat(midpoint(real(r))), BigFloat(midpoint(imag(r))))
  end
end

################################################################################
#
#  roots_ctx
#
################################################################################

mutable struct roots_ctx
  f::ZZPolyRingElem
  r_d::Vector{BigComplex}  # the 1st r1 ones will be real
  r::Vector{BigComplex}    # the complexes and at the end, the conjugated
  r1::Int
  r2::Int
  minkowski_matrix::Matrix{BigFloat} # caching: I currently
                                    # cannot extend number fields, so I cache it
                                    # here...
  minkowski_mat_p::Int

  cache::Matrix{BigFloat} # to avoid allocation elsewhere.
  cache_z1::ZZMatrix
  cache_z2::ZZMatrix
  function roots_ctx()
    r = new()
    return r
  end
  function roots_ctx(K::AbsSimpleNumField)
    return get_attribute!(K, :roots_ctx) do
      return conjugates_init(K.pol)
    end::roots_ctx
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
  zz1::ZZRingElem
  function _RealRing()
    r = new()
    r.t1 = BigFloat(0)
    r.t2 = BigFloat(0)
    r.z1 = BigInt(0)
    r.zz1 = ZZRingElem(0)
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
  base::Union{Set{T}, AbstractVector{T}}
  ptree::node{T}

  function FactorBase{T}(a::T, b::Set{T}) where {T}
    f = new{T}()
    f.prod = a
    f.base = b
    return f
  end

  function FactorBase{T}(a::T, b::AbstractVector{T}) where {T}
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

mutable struct FactorBaseSingleP{T}
  P::ZZRingElem
  pt::FactorBase{T}
  lp::Vector{Tuple{Int,AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}
  lf::Vector{T}

  function FactorBaseSingleP(p::Integer, lp::Vector{Tuple{Int, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}})
    Fpx = polynomial_ring(residue_ring(ZZ, UInt(p), cached=false)[1], "x", cached=false)[1]
    O = order(lp[1][2])
    K = O.nf
    return FactorBaseSingleP(Fpx(Globals.Zx(K.pol)), lp)
  end

  function FactorBaseSingleP(p::ZZRingElem, lp::Vector{Tuple{Int, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}})
    Fpx = polynomial_ring(residue_ring(ZZ, p, cached=false)[1], "x", cached=false)[1]
    O = order(lp[1][2])
    K = O.nf
    return FactorBaseSingleP(Fpx(Globals.Zx(K.pol)), lp)
  end

  function FactorBaseSingleP(fp::S, lp::Vector{Tuple{Int, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}) where {S}
    FB = new{S}()
    FB.lp = lp
    p = characteristic(base_ring(fp))
    FB.P = p
    O = order(lp[1][2])
    K = O.nf

    if isone(leading_coefficient(K.pol)) && isone(denominator(K.pol)) && (length(lp) >= 3 && !is_index_divisor(O, p)) # ie. index divisor or so
      Qx = parent(K.pol)
      Fpx = parent(fp)
      lf = [ gcd(fp, Fpx(Globals.Zx(Qx(K(P[2].gen_two)))))::S for P = lp]
      FB.lf = lf
      FB.pt = FactorBase(Set(lf), check = false)
    end
    return FB
  end
end

function fb_doit(a::AbsSimpleNumFieldElem, v::Int, sP::FactorBaseSingleP, no::QQFieldElem = QQFieldElem(0))
  if !isdefined(sP, :lf)
    return fb_naive_doit(a, v, sP, no)
  end
  d = denominator(a)
  if isone(gcd(d, sP.P))
    return fb_int_doit(a, v, sP)
  end
  return fb_naive_doit(a, v, sP, no)
end

function fb_naive_doit(a::AbsSimpleNumFieldElem, v::Int, sP::FactorBaseSingleP, no::QQFieldElem = QQFieldElem(0))
  lp = sP.lp
  r = Vector{Tuple{Int, Int}}()
  for x=1:length(lp)
    vl = valuation(a, lp[x][2], no)
    v -= vl*lp[x][2].splitting_type[2]
    if vl !=0
      push!(r, (lp[x][1], vl))
    end
  end
  return r, v
end

function fb_int_doit(a::AbsSimpleNumFieldElem, v::Int, sP::FactorBaseSingleP)
  g = parent(sP.lf[1])(a)
  g = gcd(g, sP.pt.prod)
  fl = is_smooth(sP.pt, g)[1]
  if fl
    d = factor(sP.pt, g)
    r = Vector{Tuple{Int, Int}}()
    vv=v
    for x in keys(d)
      id = something(findfirst(isequal(x), sP.lf), 0)
      vv -= sP.lp[id][2].splitting_type[2]
      push!(r, (sP.lp[id][1], 1))
    end
    if vv == 0
      return r, vv
    end
    r = Vector{Tuple{Int, Int}}()
    for x in keys(d)
      id = something(findfirst(isequal(x), sP.lf), 0)
      vl  = valuation(a, sP.lp[id][2])
      v -= sP.lp[id][2].splitting_type[2]*vl
      push!(r, (sP.lp[id][1], vl))
    end
    return r, v
  else
    return Vector{Tuple{Int, Int}}(), -1
  end
end

mutable struct NfFactorBase
  fb::Dict{ZZRingElem, FactorBaseSingleP}
  size::Int
  fb_int::FactorBase{ZZRingElem}
  ideals::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}
  rw::Vector{Int}
  mx::Int

  function NfFactorBase()
    r = new(Dict{ZZRingElem, Vector{Tuple{Int, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}}}())
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
  R::zzModRing
  basis::SMat{zzModRingElem}
  gens::SMat{zzModRingElem}

  function ModuleCtxNmod()
    return new()
  end

  function ModuleCtxNmod(R::zzModRing, dim::Int)
    M = new()
    M.R = R
    M.basis = sparse_matrix(R)
    M.basis.c = dim
    M.gens = sparse_matrix(R)
    return M
  end

  function ModuleCtxNmod(p::Int, dim::Int)
    M = new()
    M.R = residue_ring(ZZ, p, cached=false)[1]
    M.basis = sparse_matrix(M.R)
    M.basis.c = dim
    M.gens = sparse_matrix(M.R)
    return M
  end
end

mutable struct ModuleCtx_fmpz
  bas_gens::SMat{ZZRingElem}  # contains a max. indep system
  max_indep::SMat{ZZRingElem} # the bas_gens in upper-triangular shape
  basis::SMat{ZZRingElem}     # if set, probably a basis (in upper-triangular)
  rel_gens::SMat{ZZRingElem}  # more elements, used for relations
  Mp::ModuleCtxNmod
  rel_reps_p::SMat{zzModRingElem}  # rel_reps_p[i] * Mp.basis = rel_gens[i] - if set
                        # at least mod p...
  basis_idx::ZZRingElem
  essential_elementary_divisors::Vector{ZZRingElem}
  new::Bool
  trafo::Any            # transformations bla
  done_up_to::Int

  function ModuleCtx_fmpz(dim::Int, p::Int = next_prime(2^20))
    M = new()
    M.max_indep = sparse_matrix(ZZ)
    M.max_indep.c = dim
    M.bas_gens = sparse_matrix(ZZ)
    M.bas_gens.c = dim
    M.rel_gens = sparse_matrix(ZZ)
    M.rel_gens.c = dim
    R = residue_ring(ZZ, p, cached=false)[1]
    M.rel_reps_p = sparse_matrix(R)
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
  base::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}
  ibase::Vector{AbsSimpleNumFieldOrderFractionalIdeal}
  rand::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  exp::Vector{Int}
  ub::ZZRingElem
  lb::ZZRingElem
  last::Set{Vector{Int}}
  function RandIdlCtx()
    return new()
  end
end

const nf_elem_or_fac_elem = Union{AbsSimpleNumFieldElem, FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}}

abstract type NormCtx end

mutable struct ClassGrpCtx{T}  # T should be a matrix type: either ZZMatrix or SMat{}
  FB::NfFactorBase

  M::ModuleCtx_fmpz
  R_gen::Vector{nf_elem_or_fac_elem}# the relations
  R_rel::Vector{nf_elem_or_fac_elem}
  RS::Set{UInt} #only the hash-values

  last_piv1::Vector{Int}
  mis::Set{Int}

  h::ZZRingElem
  c::roots_ctx

  rel_cnt::Int
  bad_rel::Int
  hnf_call::Int
  time::Dict{Symbol, Float64}

  last::Int
  op::Array # of pairs: Map, perm where Map is a field automorphism
            # and perm is the induced operation on the factor base
            # difficult to type since we have many map types...
  aut_grp::Vector #For every automorphism, we have
                  #the permutation it induces on the
                  #factor base

  largePrimeCnt::Int
  B2::Int
  largePrime::Dict{ZZPolyRingElem, Tuple{AbsSimpleNumFieldElem, QQFieldElem}}
  largePrime_success::Int
  largePrime_no_success::Int

  normStat::Dict{Int, Tuple}
  expect::Int

  randomClsEnv::RandIdlCtx

  val_base::ZZMatrix      # a basis for the possible infinite randomization
                          # vectors: conditions are
                          #  - sum over all = 0
                          #  - indices corresponding to complex pairs are
                          #    identical
                          # done via lll + nullspace

  rel_mat_full_rank::Bool
  H_trafo::Vector{Any}

  dl_data # Tuple{Int, ZZMatrix, AbelianGrp, ZZMatrix}
  cl_map::Map
  finished::Bool

  normCtx::NormCtx
  sat_done::Int

  GRH::Bool # Indicate whether correctness of result depends on GRH

  function ClassGrpCtx{T}() where {T}
    r = new{T}()
    r.R_gen = Vector{nf_elem_or_fac_elem}()
    r.R_rel = Vector{nf_elem_or_fac_elem}()
    r.RS = Set{UInt}()
    r.largePrimeCnt = 0
    r.largePrime = Dict{ZZPolyRingElem, Tuple{AbsSimpleNumFieldElem, QQFieldElem}}()
    r.largePrime_success = 0
    r.largePrime_no_success = 0
    r.normStat = Dict{Int, Int}()
    r.time = Dict{Symbol, Float64}()
    r.B2 = 0
    r.H_trafo = []
    r.finished = false
    r.sat_done = 0
    return r
  end
end

################################################################################
#
#  IdealRelationCtx
#
################################################################################

mutable struct IdealRelationsCtx{Tx, TU, TC}
  A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  v::Vector{Int}  # the infinite valuation will be exp(v[i])
  E::enum_ctx{Tx, TU, TC}
  c::ZZRingElem           # the last length
  cnt::Int
  bad::Int
  restart::Int
  M::ZZMatrix
  vl::Int
  rr::UnitRange{Int}

  function IdealRelationsCtx{Tx, TU, TC}(clg::ClassGrpCtx, A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem};
                 prec::Int = 100, val::Int=0, limit::Int = 0) where {Tx, TU, TC}
    v = matrix(ZZ, Base.rand(-val:val, 1,
                    nrows(clg.val_base)))*clg.val_base
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
    I.M = zero_matrix(ZZ, 1, I.E.n)
    return I
  end
end

################################################################################
#
#  Quotient rings of maximal orders of simple number fields
#
################################################################################

# S is the type of the order, T the type of the ideal
@attributes mutable struct AbsOrdQuoRing{S, T} <: Ring
  base_ring::S
  ideal::T
  basis_matrix::ZZMatrix
  basis_mat_array::Matrix{ZZRingElem}
  preinvn::Vector{fmpz_preinvn_struct}
  factor::Dict{T, Int}
  one # cache the simplify! one or isone testing

  # temporary variables for divisor and annihilator computations
  # don't use for anything else
  tmp_gcdxx::ZZMatrix # used only by gcdxx in AbsSimpleNumFieldOrder/residue_ring.jl
  tmp_div::ZZMatrix # used only by div in AbsSimpleNumFieldOrder/residue_ring.jl
  tmp_ann::ZZMatrix # used only by annihilator in AbsSimpleNumFieldOrder/residue_ring.jl
  tmp_euc::ZZMatrix # used only by euclid in AbsSimpleNumFieldOrder/residue_ring.jl

  multiplicative_group::Map

  function AbsOrdQuoRing{S, T}(O::S, I::T) where {S, T}
    z = new{S, T}()
    z.base_ring = O
    z.ideal = I
    z.basis_matrix = integral_basis_matrix_wrt(I, O)
    z.basis_mat_array = Array(z.basis_matrix)
    z.preinvn = [ fmpz_preinvn_struct(z.basis_matrix[i, i]) for i in 1:degree(O)]
    d = degree(O)
    z.tmp_div = zero_matrix(ZZ, 2*d + 1, 2*d + 1)
    z.tmp_gcdxx = zero_matrix(ZZ, 3*d + 1, 3*d + 1)
    z.tmp_ann = zero_matrix(ZZ, 2*d, d)
    z.tmp_euc = zero_matrix(ZZ, 2*d, d)
    z.one = simplify!(one(z))
    return z
  end
end

function AbsOrdQuoRing(O::S, I::T) where {S, T}
  @assert T == ideal_type(O)
  return AbsOrdQuoRing{S, T}(O, I)
end

# S and T as for AbsOrdQuoRing, U is the elem_type of the order
mutable struct AbsOrdQuoRingElem{S, T, U} <: RingElem
  elem::U
  parent::AbsOrdQuoRing{S, T}
  isreduced::Bool


  function AbsOrdQuoRingElem{S, T, U}() where {S, T, U}
    z = new{S, T, U}()
    z.isreduced = false
    return z
  end

  function AbsOrdQuoRingElem{S, T, U}(Q::AbsOrdQuoRing{S, T}, x::U) where {S, T, U}
    z = new{S, T, U}()
    z.elem = x
    z.parent = Q
    z.isreduced = false
    return z
  end
end

function AbsOrdQuoRingElem(Q::AbsOrdQuoRing{S, T}, x::U) where {S, T, U}
  return AbsOrdQuoRingElem{S, T, U}(Q, x)
end

################################################################################
#
#  Finitely generated abelian groups and their elements
#
################################################################################

abstract type GrpAb <: AbstractAlgebra.AdditiveGroup end

abstract type GrpAbElem <: AbstractAlgebra.AdditiveGroupElem end

@attributes mutable struct FinGenAbGroup <: GrpAb
  rels::ZZMatrix
  hnf::ZZMatrix
  is_snf::Bool
  snf::Vector{ZZRingElem}
  snf_map::Map{FinGenAbGroup, FinGenAbGroup}
  exponent::ZZRingElem
  isfinalized::Bool

  function FinGenAbGroup(R::ZZMatrix, is_hnf::Bool = false)
    r = new()
    r.is_snf = false
    r.rels = R
    if is_hnf
      r.hnf = R
    end
    r.isfinalized = false
    return r
  end

  function FinGenAbGroup(R::Vector{ZZRingElem}, is_snf::Bool = true)
    r = new()
    r.is_snf = is_snf
    r.snf = R
    r.isfinalized = false
    return r
  end

  function FinGenAbGroup(R::Vector{T}, is_snf::Bool = true) where T <: Integer
    r = new()
    r.is_snf = is_snf
    r.snf = map(ZZRingElem, R)
    r.isfinalized = false
    return r
  end

end

struct FinGenAbGroupElem <: GrpAbElem
  parent::FinGenAbGroup
  coeff::ZZMatrix

  # This destroy's the input. If you don't want this, use A(::ZZMatrix)
  function FinGenAbGroupElem(A::FinGenAbGroup, a::ZZMatrix)
    assure_reduced!(A, a)
    return new(A, a)
  end

end

################################################################################
#
#  Binary Quadratic Forms
#
################################################################################

mutable struct QuadBin{T}
  base_ring         #::parent_type(T)
  a::T
  b::T
  c::T
  disc::T           # discriminant
  nonproper_cycle   # Vector{QuadBin{T}}

  function QuadBin(a::T, b::T, c::T) where {T}
    z = new{T}()
    z.a = a
    z.b = b
    z.c = c
    return z
  end
end

function QuadBin(a::Integer, b::Integer, c::Integer)
  return QuadBin(ZZ, a, b, c)
end

function QuadBin(R, a, b, c)
  z = QuadBin(R(a), R(b), R(c))
  z.base_ring = R
  return z
end

################################################################################
#
#  NoElements
#
################################################################################

mutable struct NoElements <: Exception end

abstract type NumFieldEmb{T} end

################################################################################
#
#  Number field embeddings
#
################################################################################

mutable struct AbsSimpleNumFieldEmbedding <: NumFieldEmb{AbsSimpleNumField}
  K::AbsSimpleNumField  # Number Field
  i::Int               # The position of the root r in conjugates_arb(a),
                       # where a is the primitive element of K
  r::AcbFieldElem               # Approximation of the root
  isreal::Bool         # True if and only if the embedding is real.
  conjugate::Int       # The conjuagte embedding
  uniformizer::AbsSimpleNumFieldElem # An element which is positive at the embedding
                       # and negative at all the other real embeddings.
                       # Makes sense only if the place is real.

  function AbsSimpleNumFieldEmbedding(K::AbsSimpleNumField, c::acb_roots, i::Int)
    z = new()
    z.K = K
    r1, r2 = length(c.real_roots), length(c.complex_roots)
    if 1 <= i <= r1
      z.i = i
      z.isreal = true
      z.r = c.roots[i]
      z.conjugate = i
    elseif r1 + 1 <= i <= r1 + r2
      z.i = i
      z.isreal = false
      z.r = c.complex_roots[i - r1]
      z.conjugate = i + r2
    elseif r1 + r2  + 1 <= i <=  r1 + 2*r2
      z.i = i
      z.isreal = false
      z.r = conj(c.complex_roots[i - r1 - r2])
      z.conjugate = i - r2
    end
    return z
  end
end

################################################################################
#
#  Infinite places
#
################################################################################

abstract type Plc end

# The field is not necessary, but we want to parametrize by it
mutable struct InfPlc{K, E} <: Plc
  field::K
  embedding::E

  function InfPlc(embedding::E) where {E}
    K = number_field(embedding)
    return new{typeof(K), E}(K, embedding)
  end
end

################################################################################
#
#  Types
#
################################################################################

@attributes mutable struct RelSimpleNumField{T} <: SimpleNumField{T}
  base_ring::Nemo.Field
  pol::Generic.Poly{T}
  S::Symbol
  trace_basis::Vector{T}

  function RelSimpleNumField{T}(f::Generic.Poly{T}, s::Symbol, cached::Bool = false) where {T}
    return get_cached!(RelSimpleNumFieldID, (parent(f), f, s), cached) do
      z = new{T}()
      z.base_ring = base_ring(parent(f))
      z.pol = f
      z.S = s
      return z
    end::RelSimpleNumField{T}
  end
end

const RelSimpleNumFieldID = AbstractAlgebra.CacheDictType{Tuple{Generic.PolyRing, Generic.Poly, Symbol},
                     RelSimpleNumField}()


mutable struct RelSimpleNumFieldElem{T} <: SimpleNumFieldElem{T}
  data::Generic.Poly{T}
  parent::RelSimpleNumField{T}

  RelSimpleNumFieldElem{T}(g::Generic.Poly{T}) where {T} = new{T}(g)
end

elem_type(::Type{RelSimpleNumField{T}}) where {T} = RelSimpleNumFieldElem{T}

parent_type(::Type{RelSimpleNumFieldElem{T}}) where {T} = RelSimpleNumField{T}


################################################################################
#
#  G-Modules
#
################################################################################

abstract type GModule end

mutable struct ZpnGModule <: GModule
  R::Nemo.zzModRing
  V::FinGenAbGroup
  G::Vector{zzModMatrix}
  p::Int

  function ZpnGModule(V::FinGenAbGroup,G::Vector{zzModMatrix})
    @assert ngens(V)==ncols(G[1]) && ngens(V)==nrows(G[1])
    z=new()
    z.G=G
    z.V=V
    z.R=parent(G[1][1,1])
    f=factor(ZZRingElem(z.R.n))
    @assert length(f.fac)==1
    z.p=Int(first(keys(f.fac)))
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
  new_low_degrees::Dict{T, Nothing}

  function Graph{T, M}() where {T, M}
    z = new{T, M}()
    z.edges = Dict{T, Dict{T, M}}()
    z.degrees = Dict{T, Int}()
    z.new_low_degrees = Dict{T, Nothing}()
    return z
  end
end


mutable struct RelLattice{T <: Any, D <: Any}
  weak_vertices::WeakKeyDict{T, Nothing}
  graph::Graph{UInt, D}
  block_gc::Dict{T, Nothing}
  weak_vertices_rev::Dict{UInt, WeakRef}
  to_delete::Vector{UInt}
  zero::D # a generic object that will never actually be used.
  mult::Base.Callable #(D, D) -> D
  make_id::Base.Callable   # T -> D

  function RelLattice{T, D}() where {T, D}
    z = new()
    z.weak_vertices = WeakKeyDict{T, Nothing}()
    z.graph = Graph{UInt, D}()
    z.weak_vertices_rev = Dict{UInt, WeakRef}()
    z.to_delete = Vector{UInt}()
    z.block_gc = Dict{FinGenAbGroup, Nothing}()
    return z
  end
end

function GrpAbLatticeCreate()
  r = GrpAbLattice()
  r.zero = ZZMatrix(0,0)
  r.mult = *
  r.make_id = G::FinGenAbGroup -> identity_matrix(ZZ, ngens(G))
  return r
end

const GrpAbLattice = RelLattice{FinGenAbGroup, ZZMatrix}
const GroupLattice = GrpAbLatticeCreate()

###############################################################################
#
#  Pseudo matrix
#
###############################################################################

mutable struct PMat{T, S}
  base_ring
  matrix::Generic.MatSpaceElem{T}
  coeffs::Vector{S}

  function PMat{T, S}(m::Generic.MatSpaceElem{T}, c::Vector{S}) where {T, S}
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

@attributes mutable struct AbsNonSimpleNumField <: NonSimpleNumField{QQFieldElem}
  pol::Vector{QQMPolyRingElem}
  abs_pol::Vector{QQPolyRingElem}
  S::Vector{Symbol}
  basis#::Vector{AbsNonSimpleNumFieldElem}
  degree::Int
  degrees::Vector{Int}
  signature::Tuple{Int, Int}
  traces::Vector{Vector{QQFieldElem}}

  function AbsNonSimpleNumField(ff::Vector{QQPolyRingElem}, f::Vector{QQMPolyRingElem}, S::Vector{Symbol}, cached::Bool = false)
    r = new()
    r.abs_pol = ff
    r.pol = f
    r.S = S
    r.signature = (-1, -1)
    return r
  end
end

mutable struct AbsNonSimpleNumFieldElem <: NonSimpleNumFieldElem{QQFieldElem}
  data::QQMPolyRingElem
  parent::AbsNonSimpleNumField

  function AbsNonSimpleNumFieldElem(K::AbsNonSimpleNumField, g::QQMPolyRingElem)
    return new(g, K)
  end

end

################################################################################
#
#   Local fields
#
################################################################################

include("LocalField/Types.jl")

################################################################################
# for p/qAdic completions
################################################################################
#cannot use Ref here, has to be Ptr as the underlying stuff is
#not Julia allocated (but flint)
mutable struct fmpz_poly_raw  ## ZZPolyRingElem without parent like in c
  coeffs::Ptr{Nothing}
  alloc::Int
  length::Int

  function fmpz_poly_raw()
    error("should not get called")
    z = new()
    ccall((:fmpz_poly_init, libflint), Nothing, (Ref{ZZPolyRingElem},), z)
    finalizer(_fmpz_poly_raw_clear_fn, z)
    return z
  end

  function _fmpz_poly_raw_clear_fn(a::ZZPolyRingElem)
    ccall((:fmpz_poly_clear, libflint), Nothing, (Ref{ZZPolyRingElem},), a)
  end
end

mutable struct fmpz_poly_factor
  c::Int   # really an ZZRingElem  - but there is no fmpz_raw to be flint compatible
  poly::Ptr{fmpz_poly_raw}
  exp::Ptr{Int}
  _num::Int
  _alloc::Int

  function fmpz_poly_factor()
    z = new()
    ccall((:fmpz_poly_factor_init, libflint), Nothing,
            (Ref{fmpz_poly_factor}, ), z)
    finalizer(_fmpz_poly_factor_clear_fn, z)
    return z
  end

  function _fmpz_poly_factor_clear_fn(a::fmpz_poly_factor)
    ccall((:fmpz_poly_factor_clear, libflint), Nothing,
            (Ref{fmpz_poly_factor}, ), a)
  end
end

mutable struct HenselCtx
  f::ZZPolyRingElem
  p::UInt

  LF :: fmpz_poly_factor
  link::Ptr{Int}
  v::Ptr{fmpz_poly_raw}
  w::Ptr{fmpz_poly_raw}
  N::UInt
  prev::UInt
  r::Int  #for the cleanup
  lf:: Nemo.nmod_poly_factor

  function HenselCtx(f::ZZPolyRingElem, p::ZZRingElem)
    a = new()
    a.f = f
    a.p = UInt(p)
    Zx,x = polynomial_ring(ZZ, "x", cached=false)
    Rx,x = polynomial_ring(Native.GF(UInt(p), cached=false), "x", cached=false)
    a.lf = Nemo.nmod_poly_factor(UInt(p))
    ccall((:nmod_poly_factor, libflint), UInt,
          (Ref{Nemo.nmod_poly_factor}, Ref{fpPolyRingElem}), (a.lf), Rx(f))
    r = a.lf.num
    a.r = r
    a.LF = fmpz_poly_factor()
#    @assert r > 1  #flint restriction
    a.v = ccall((:flint_malloc, libflint), Ptr{fmpz_poly_raw}, (Int, ), (2*r-2)*sizeof(fmpz_poly_raw))
    a.w = ccall((:flint_malloc, libflint), Ptr{fmpz_poly_raw}, (Int, ), (2*r-2)*sizeof(fmpz_poly_raw))
    for i=1:(2*r-2)
      ccall((:fmpz_poly_init, libflint), Nothing, (Ptr{fmpz_poly_raw}, ), a.v+(i-1)*sizeof(fmpz_poly_raw))
      ccall((:fmpz_poly_init, libflint), Nothing, (Ptr{fmpz_poly_raw}, ), a.w+(i-1)*sizeof(fmpz_poly_raw))
    end
    a.link = ccall((:flint_calloc, libflint), Ptr{Int}, (Int, Int), 2*r-2, sizeof(Int))
    a.N = 0
    a.prev = 0
    finalizer(HenselCtx_free, a)
    return a
  end

  function free_fmpz_poly_array(p::Ref{fmpz_poly_raw}, r::Int)
    for i=1:(2*r-2)
      ccall((:fmpz_poly_clear, libflint), Nothing, (Ref{fmpz_poly_raw}, ), p+(i-1)*sizeof(fmpz_poly_raw))
    end
    ccall((:flint_free, libflint), Nothing, (Ref{fmpz_poly_raw}, ), p)
  end
  function free_int_array(a::Ref{Int})
    ccall((:flint_free, libflint), Nothing, (Ref{Int}, ), a)
  end
  function HenselCtx_free(a::HenselCtx)
    free_fmpz_poly_array(a.v, a.r)
    free_fmpz_poly_array(a.w, a.r)
    free_int_array(a.link)
  end
end

mutable struct qAdicRootCtx
  f::ZZPolyRingElem
  p::Int
  n::Int
  Q::Vector{QadicField}
  H::Hecke.HenselCtx
  R::Vector{QadicFieldElem}
  is_splitting::Bool
  function qAdicRootCtx(f::ZZPolyRingElem, p::Int; splitting_field::Bool = false)
    r = new()
    r.f = f
    r.p = p
    r.H = H = Hecke.factor_mod_pk_init(f, p)
    lf = Hecke.factor_mod_pk(Array, H, 1)
    if splitting_field
      d = lcm([degree(y[1]) for y = lf])
      R = qadic_field(p, d, precision = 1)[1]
      Q = [R]
      r.is_splitting = true
    else
      Q = [qadic_field(p, x, precision = 1)[1] for x = Set(degree(y[1]) for y = lf)]
      r.is_splitting = false
    end
    @assert all(x->isone(x[2]), lf)
    r.Q = Q
    return r
  end
end

################################################################################
#
#  Unsafe rationals
#
################################################################################

struct UnsafeRational{T} <: Number
  num::T
  den::T
end

###############################################################################
#
#  KInftyRing / KInftyElem
#
###############################################################################

mutable struct KInftyRing{T <: FieldElement} <: Hecke.Ring
  K::Generic.RationalFunctionField{T}

  function KInftyRing{T}(K::Generic.RationalFunctionField{T}, cached::Bool) where T <: FieldElement
    return AbstractAlgebra.get_cached!(KInftyID, K, cached) do
      new{T}(K)
    end::KInftyRing{T}
  end
end

const KInftyID = AbstractAlgebra.CacheDictType{Generic.RationalFunctionField, Hecke.Ring}()

mutable struct KInftyElem{T <: FieldElement} <: Hecke.RingElem
  d::Generic.RationalFunctionFieldElem{T}
  parent::KInftyRing{T}
end

################################################################################
#
#  Aliases
#
################################################################################

const AbsSimpleNumFieldOrderQuoRing = AbsOrdQuoRing{AbsSimpleNumFieldOrder, AbsSimpleNumFieldOrderIdeal}

const AbsSimpleNumFieldOrderQuoRingElem = AbsOrdQuoRingElem{AbsSimpleNumFieldOrder, AbsSimpleNumFieldOrderIdeal, AbsSimpleNumFieldOrderElem}

