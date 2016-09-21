################################################################################
#
#  Z/nZ modelled with UInt's
#
################################################################################

immutable nmod_struct
  n::UInt    # mp_limb_t
  ninv::UInt # mp_limb_t
  norm::UInt # mp_limb_t
end

type nmod_struct_non
  n::UInt    # mp_limb_t
  ninv::UInt # mp_limb_t
  norm::UInt # mp_limb_t
end

immutable ZZModUInt <: Ring
  mod::nmod_struct

  function ZZModUInt(n::UInt)
    mod = nmod_struct_non(0, 0, 0)
    ccall((:nmod_init, :libflint), Void, (Ptr{nmod_struct_non}, UInt), &mod, n)
    return new(nmod_struct(mod.n, mod.ninv, mod.norm))
  end
end

immutable UIntMod <: RingElem
  m::UInt
  parent::ZZModUInt

  function UIntMod(R::ZZModUInt)
    z = new()
    z.m = UInt(0)
    z.parent = R
  end

  function UIntMod(R::ZZModUInt, m::UInt)
    z = new(m, R)
    return z
  end
end

################################################################################
#
#  Transformations for matrices
#
################################################################################

abstract Trafo

type TrafoSwap{T} <: Trafo
  i::Int
  j::Int

  function TrafoSwap(i, j)
    return new{T}(i, j)
  end
end

type TrafoAddScaled{T} <: Trafo
  i::Int
  j::Int
  s::T

  function TrafoAddScaled(i::Int, j::Int, s::T)
    return new{T}(i, j, s)
  end
end

TrafoAddScaled{T}(i::Int, j::Int, s::T) = TrafoAddScaled{T}(i, j, s)

# if from right, then
# row i -> a*row i + b * row j
# row j -> c*row i + d * row j
type TrafoParaAddScaled{T} <: Trafo
  i::Int
  j::Int
  a::T
  b::T
  c::T
  d::T

  function TrafoParaAddScaled(i::Int, j::Int, a::T, b::T, c::T, d::T)
    return new{T}(i, j, a, b, c, d)
  end
end

TrafoParaAddScaled{T}(i::Int, j::Int, a::T, b::T, c::T, d::T) =
      TrafoParaAddScaled{T}(i, j, a, b, c, d)

type TrafoId{T} <: Trafo
end

type TrafoPartialDense{S} <: Trafo
  i::Int
  rows::UnitRange{Int}
  cols::UnitRange{Int}
  U::S
  
  function TrafoPartialDense(i::Int, rows::UnitRange{Int},
                             cols::UnitRange{Int}, U::S)
    return new(i, rows, cols, U)
  end
end

function TrafoPartialDense{S}(i::Int, rows::UnitRange{Int},
                              cols::UnitRange{Int}, U::S)
  return TrafoPartialDense{S}(i, rows, cols, U)
end

# this is shorthand for the permutation matrix corresponding to
# (i i+1)(i+1 i+2)...(rows-1 rows)
type TrafoDeleteZero{T} <: Trafo
  i::Int
end

################################################################################
#
#  Wrapper for fmpz_preinvn_struct
#
################################################################################

type fmpz_preinvn_struct
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
type acb_root_ctx
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
    A = Array(arb, z.signature[1])
    B = Array(acb, z.signature[2])

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
              (Ptr{acb_struct}, Clong), x._roots, degree(x.poly))
end

################################################################################
#
#  SmatRow/Smat
#
################################################################################

type SmatSLP_add_row{T}
  row::Int
  col::Int
  val::T 
end

type SmatSLP_swap_row
  row::Int
  col::Int
end

################################################################################
#
#  Abstract types
#
################################################################################

abstract Map{D, C}

type SmatRow{T}
  #in this row, in column pos[1] we have value values[1]
  values::Array{T, 1}
  pos::Array{Int, 1}
  function SmatRow()
    r = new()
    r.values = Array{T, 1}()
    r.pos = Array{Int, 1}()
    return r
  end

  function SmatRow(A::Array{Tuple{Int, T}, 1})
    r = new()
    r.values = [x[2] for x in A]
    r.pos = [x[1] for x in A]
    return r
  end

  function SmatRow(A::Array{Tuple{Int, Int}, 1})
    r = new()
    r.values = [T(x[2]) for x in A]
    r.pos = [x[1] for x in A]
    return r
  end

  function SmatRow{S}(A::SmatRow{S})
    r = new()
    r.values = Array(T, length(A.pos))
    r.pos = copy(A.pos)
    for i=1:length(r.values)
      r.values[i] = T(A.values[i])
    end
    return r
  end
end

type Smat{T}
  r::Int
  c::Int
  rows::Array{SmatRow{T}, 1}
  nnz::Int

  function Smat()
    r = new()
    r.rows = Array(SmatRow{T}, 0)
    r.nnz = 0
    r.r = 0
    r.c = 0
    return r
  end

  function Smat{S}(a::Smat{S})
    r = new()
    r.rows = Array(SmatRow{T}, length(a.rows))
    for i=1:rows(a)
      r.rows[i] = SmatRow{T}(a.rows[i])
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
type enum_ctx{Tx, TC, TU}
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
  function enum_ctx()
    return new()
  end
end

################################################################################
#
#  EnumCtxArb
#
################################################################################

type EnumCtxArb
  G::arb_mat
  L::Array{fmpz_mat, 1}
  x::fmpz_mat
  p::Int

  function EnumCtxArb(G::arb_mat)
    z = new()
    z.G = G
    z.x = MatrixSpace(ZZ, 1, rows(G))()
    z.p = prec(base_ring(G))
    return z
  end
end

################################################################################
#
#  FakeFmpqMatSpace/FakeFmpqMat
#
################################################################################

const FakeFmpqMatSpaceID = ObjectIdDict()

type FakeFmpqMatSpace
  rows::Int
  cols::Int

  function FakeFmpqMatSpace(r::Int, c::Int)
    try
      return FakeFmpqMatSpaceID[r,c]::FakeFmpqMatSpace
    catch
      z = new(r,c)
      FakeFmpqMatSpaceID[r,c] = z
      return z
    end
  end
end

type FakeFmpqMat
  num::fmpz_mat
  den::fmpz
  parent::FakeFmpqMatSpace
  rows::Int
  cols::Int

  function FakeFmpqMat(x::fmpz_mat, y::fmpz)
    z = new()
    z.num = x
    z.den = y
    z.rows = rows(x)
    z.cols = cols(x)
    simplify_content!(z)
    z.parent = FakeFmpqMatSpace(z.rows, z.cols)
    return z
  end

  function FakeFmpqMat(x::Tuple{fmpz_mat, fmpz})
    z = new()
    z.num = x[1]
    z.den = x[2]
    z.rows = rows(x[1])
    z.cols = cols(x[1])
    simplify_content!(z)
    z.parent = FakeFmpqMatSpace(z.rows, z.cols)
    return z
  end

  function FakeFmpqMat(x::fmpz_mat)
    z = new()
    z.num = x
    z.den = ZZ(1)
    z.rows = rows(x)
    z.cols = cols(x)
    z.parent = FakeFmpqMatSpace(z.rows, z.cols)
    return z
  end
end

################################################################################
#
#  FacElemMon/FacElem
#
################################################################################

type FacElemMon{T <: RingElem} <: Ring
  base_ring::Ring  # for the base
  basis_conjugates_log::Dict{RingElem, Tuple{Int, Array{arb, 1}}}
  basis_conjugates::Dict{RingElem, Tuple{Int, Array{arb, 1}}}
  conj_log_cache::Dict{Int, Dict{nf_elem, Array{arb, 1}}}

  function FacElemMon(R::Ring)
    if haskey(FacElemMonDict, R)
      return FacElemMonDict[R]::FacElemMon
    else
      z = new()
      z.base_ring = R
      z.basis_conjugates_log = Dict{RingElem, Array{arb, 1}}()
      z.basis_conjugates = Dict{RingElem, Array{arb, 1}}()
      z.conj_log_cache = Dict{Int, Dict{nf_elem, arb}}()
      FacElemMonDict[R] = z
      return z
    end
  end
end

type FacElem{B}
  fac::Dict{B, fmpz}
  parent::FacElemMon

  function FacElem()
    z = new()
    z.fac = Dict{B, fmpz}()
    return z
  end
end

################################################################################
#
#  NfOrd/NfOrdElem
#
################################################################################

export NfOrdElem

abstract NfOrd <: Ring

type NfOrdElem{T <: NfOrd} <: RingElem
  elem_in_nf::nf_elem
  elem_in_basis::Array{fmpz, 1}
  has_coord::Bool
  parent::T

  function NfOrdElem(O::T)
    z = new{T}()
    z.parent = O
    z.elem_in_nf = nf(O)() 
    z.elem_in_basis = Array(fmpz, degree(O))
    z.has_coord = false
    return z
  end

  function NfOrdElem(O::T, a::nf_elem)
    z = new{T}()
    z.elem_in_nf = a
    z.elem_in_basis = Array(fmpz, degree(O))
    z.parent = O
    z.has_coord = false
    return z
  end

  function NfOrdElem(O::T, a::nf_elem, arr::Array{fmpz, 1})
    z = new{T}()
    z.parent = O
    z.elem_in_nf = a
    z.has_coord = true
    z.elem_in_basis = arr
    return z
  end

  function NfOrdElem(O::T, arr::Array{fmpz, 1})
    z = new{T}()
    z.elem_in_nf = dot(O.basis_nf, arr)
    z.has_coord = true
    z.elem_in_basis = arr
    z.parent = O
    return z
  end

  function NfOrdElem{S <: Integer}(O::T, arr::Array{S, 1})
    return NfOrdElem{T}(O, map(FlintZZ, arr))
  end

  function NfOrdElem(x::NfOrdElem{T})
    return deepcopy(x)  ### Check parent?
  end
end

################################################################################
#
#  NfOrd
#
################################################################################

export NfOrdGenSet, NfOrdGen

const NfOrdGenSetID = ObjectIdDict()

type NfOrdGenSet
  nf::AnticNumberField

  function NfOrdGenSet(a::AnticNumberField)
  try
    return NfOrdGenSetID[a]::NfOrdGenSet
  end
    NfOrdGenSetID[a] = new(a)
    return NfOrdGenSetID[a]
  end
end

#const NfOrdID = Dict{Tuple{AnticNumberField, FakeFmpqMat}, NfOrd}()
const NfOrdGenID = ObjectIdDict()

type NfOrdGen <: NfOrd
  nf::AnticNumberField
  basis_nf::Array{nf_elem, 1}      # Basis as number field elements
  basis_ord                        # Basis as order elements
  basis_mat::FakeFmpqMat           # Basis matrix with respect
                                   # to number field basis
  basis_mat_inv::FakeFmpqMat       # Inverse of basis matrix
  gen_index::fmpq                  # Generalized index
  index::fmpz                      # Index
  disc::fmpz                       # Discriminant
  disc_fac::Dict{fmpz, Int}        # Factorization of the discriminant
  isequationorder::Bool            # Flag for being equation order
  parent::NfOrdGenSet              # Parent object
  signature::Tuple{Int, Int}       # Signature of the associated number field
                                   # (-1, 0) means 'not set'
  minkowski_mat::Tuple{arb_mat, Int}
                                   # Minkowski matrix
  torsion_units::Tuple{Array{NfOrdElem, 1}, NfOrdElem}
                                   # (Torsion units, generator of torsion)
  norm_change_const::Tuple{Float64, Float64}
                                   # Tuple c1, c2 as in the paper of 
                                   # Fieker-Friedrich

  function NfOrdGen()
    z = new()
    # Populate with 'default' values
    z.signature = (-1,0)      
    z.norm_change_const = (-1.0, -1.0)
    z.isequationorder = false
    return z
  end

  function NfOrdGen(K::AnticNumberField)
    A = FakeFmpqMat(one(MatrixSpace(FlintZZ, degree(K), degree(K))))
    if haskey(NfOrdGenID, (K,A))
      return NfOrdGenID[(K,A)]::NfOrdGen
    else
      z = NfOrdGen()
      z.parent = NfOrdGenSet(K)
      z.nf = K
      z.basis_mat = A
      z.basis_nf = basis(K)
      z.basis_ord = Array{NfOrdElem{NfOrdGen}, 1}(degree(K))
      z.basis_ord[1] = z(K(1), false)
      for i in 2:degree(K)
        z.basis_ord[i] = z(gen(K)^(i-1), false)
      end
      NfOrdGenID[(K, A)] = z
      return z::NfOrdGen
    end
  end

  # Construct the order with basis matrix x
  function NfOrdGen(K::AnticNumberField, x::FakeFmpqMat)
    x = hnf(x)
    if haskey(NfOrdGenID, (K,x))
      return NfOrdGenID[(K,x)]::NfOrdGen
    else
      z = NfOrdGen()
      z.parent = NfOrdGenSet(K)
      z.nf = K
      z.basis_mat = x
      B = Array(NfOrdElem{NfOrdGen}, degree(K))
      BB = Array(nf_elem, degree(K))
      for i in 1:degree(K)
        t = elem_from_mat_row(K, x.num, i, x.den)
        BB[i] = t
        B[i] = z(t, false) 
      end
      z.basis_ord = B
      z.basis_nf = BB
      z.parent = NfOrdGenSet(z.nf)
      NfOrdGenID[(K,x)] = z
      return z::NfOrdGen
    end
  end

  # Construct the order with basis a
  function NfOrdGen(a::Array{nf_elem, 1})
    K = parent(a[1])
    A = hnf(basis_mat(a))
    if haskey(NfOrdGenID, (K,A))
      return NfOrdGenID[(K,A)]::NfOrdGen
    else
      z = NfOrdGen()
      z.parent = NfOrdGenSet(K)
      z.nf = K
      z.basis_nf = a
      z.basis_mat = A
      z.basis_ord = Array(NfOrdElem{NfOrdGen}, degree(K))
      for i in 1:degree(K)
        z.basis_ord[i] = z(a[i], false)
      end
      NfOrdGenID[(K,A)] = z
      return z::NfOrdGen
    end
  end
end

################################################################################
#
#  NfOrdIdl/NfOrdIdlSet/NfOrdIdl
#
################################################################################

abstract NfOrdIdlSet

abstract NfOrdIdl

NfOrdGenIdlSetID = ObjectIdDict()

type NfOrdGenIdlSet <: NfOrdIdlSet
  order::NfOrdGen
  
  function NfOrdGenIdlSet(a::NfOrdGen)
    try
      return NfOrdGenIdlSetID[a]
    catch
      NfOrdGenIdlSetID[a] = new(a)
      return NfOrdGenIdlSetID[a]
    end
  end
end

type NfOrdGenIdl <: NfOrdIdl
  basis::Array{NfOrdElem{NfOrdGen}, 1}
  basis_mat::fmpz_mat
  basis_mat_inv::FakeFmpqMat
  parent::NfOrdGenIdlSet

  norm::fmpz
  minimum::fmpz
  princ_gen::NfOrdElem{NfOrdGen}
  princ_gen_special::Tuple{Int, Int, fmpz}
                           # first entry encodes the following:
                           # 0: don't know
                           # 1: second entry generates the ideal
                           # 2: third entry generates the ideal

  function NfOrdGenIdl(O::NfOrdGen)
    z = new()
    z.parent = NfOrdGenIdlSet(O)
    z.princ_gen_special = (0, 0, fmpz(0))
    return z
  end
    
  function NfOrdGenIdl(O::NfOrdGen, a::Int)
    z = new()
    z.parent = NfOrdGenIdlSet(O)
    z.basis_mat = MatrixSpace(ZZ, degree(O), degree(O))(abs(a))
    z.princ_gen_special = (1, abs(a), fmpz(0))
    z.princ_gen = O(a)
    z.minimum = fmpz(abs(a))
    return z
  end

  function NfOrdGenIdl(O::NfOrdGen, a::fmpz)
    z = new()
    z.parent = NfOrdGenIdlSet(O)
    z.basis_mat = MatrixSpace(ZZ, degree(O), degree(O))(abs(a))
    z.princ_gen_special = (2, Int(0), abs(a))
    z.princ_gen = O(a)
    z.minimum = abs(a)
    return z
  end

  function NfOrdGenIdl(O::NfOrdGen, a::NfOrdElem{NfOrdGen})
    z = new()
    z.parent = NfOrdGenIdlSet(O)
    m = representation_mat(a)
    z.basis_mat = _hnf(m, :lowerleft)
    z.princ_gen = a
    z.princ_gen_special = (0, 0, fmpz(0))
    return z
  end

  function NfOrdGenIdl(O::NfOrdGen, a::fmpz_mat)
    @hassert :NfOrd 2 is_hnf(transpose(a)) # a must be lowerleft HNF
    z = new()
    z.parent = NfOrdGenIdlSet(O)
    z.basis_mat = a
    z.princ_gen_special = (0, 0, fmpz(0))
    return z
  end
end

################################################################################
#
#  NfOrdFracIdlSet/NfOrdFracIdl
#
################################################################################

abstract NfOrdFracIdlSet

abstract NfOrdFracIdl

NfOrdGenFracIdlSetID = ObjectIdDict()

type NfOrdGenFracIdlSet <: NfOrdFracIdlSet
  order::NfOrdGen
  
  function NfOrdGenFracIdlSet(a::NfOrdGen)
    try
      return NfOrdGenFracIdlSetID[a]
    catch
      NfOrdGenFracIdlSetID[a] = new(a)
      return NfOrdGenFracIdlSetID[a]
    end
  end
end

type NfOrdGenFracIdl <: NfOrdFracIdl
  basis::Array{nf_elem, 1}
  num::NfOrdGenIdl
  den::fmpz
  basis_mat::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat
  parent::NfOrdGenFracIdlSet
  norm::fmpq
  princ_gen::nf_elem
  
  function NfOrdGenFracIdl(O::NfOrdGen, a::FakeFmpqMat)
    z = new()
    z.parent = NfOrdGenFracIdlSet(O)
    z.basis_mat = a
    return z
  end

  function NfOrdGenFracIdl(O::NfOrdGen, a::NfOrdGenIdl, b::fmpz)
    z = new()
    z.parent = NfOrdGenFracIdlSet(O)
    z.basis_mat = FakeFmpqMat(basis_mat(a), b)
    return z
  end

  function NfOrdGenFracIdl(O::NfOrdGen, a::nf_elem)
    z = new()
    z.parent = NfOrdGenFracIdlSet(O)
    z.basis_mat = hnf(FakeFmpqMat(representation_mat(O(den(a, O)*a)), den(a, O)))
    return z
  end
end

################################################################################
#
#  NfMaxOrdSet/NfMaxOrd
#
################################################################################

const NfMaxOrdID = Dict{Tuple{AnticNumberField, FakeFmpqMat}, NfOrd}()

const NfMaxOrdSetID = ObjectIdDict()

type NfMaxOrdSet
  nf::AnticNumberField

  function NfMaxOrdSet(a::AnticNumberField)
  try
    return NfMaxOrdSetID[a]::NfMaxOrdSet
  end
    NfMaxOrdSetID[a] = new(a)
    return NfMaxOrdSetID[a]
  end
end

type NfMaxOrd <: NfOrd
  nf::AnticNumberField
  basis_nf::Array{nf_elem, 1}      # Array of number field elements
  basis_ord                        # Array of order elements
  basis_mat::FakeFmpqMat           # basis matrix of order wrt basis of K
  basis_mat_inv::FakeFmpqMat       # inverse of basis matrix
  gen_index::fmpq                  # the det of basis_mat_inv
  index::fmpz                      # the det of basis_mat_inv
  disc::fmpz                       # discriminant
  parent::NfMaxOrdSet              # parent object
  isequationorder::Bool            #
  signature::Tuple{Int, Int}       # signature of the parent object
                                   # (-1, 0) means 'not set'
  #conjugate_data::acb_root_ctx
  minkowski_mat::Tuple{arb_mat, Int}        # Minkowski matrix
  torsion_units::Tuple{Array{NfOrdElem, 1}, NfOrdElem}
  unit_group::Map                  # Abstract types in the field is usually bad,
                                   # but here it can be neglected.
                                   # We annotate the concrete type when doing
                                   # unit_group(O)

  norm_change_const::Tuple{Float64, Float64}
                                   # Tuple c1, c2 as in the paper of 
                                   # Fieker-Friedrich

  auxilliary_data::Array{Any, 1}   # eg. for the class group: the
                                   # type dependencies make it difficult

  function NfMaxOrd(a::AnticNumberField)
    r = new(a)
    r.parent = NfMaxOrdSet(a)
    r.signature = (-1,0)
    r.norm_change_const = (-1.0, -1.0)
    r.auxilliary_data = Array(Any, 5)
    r.isequationorder = false
    return r
  end

  function NfMaxOrd(K::AnticNumberField, x::FakeFmpqMat)
    if haskey(NfMaxOrdID, (K,x))
      return NfMaxOrdID[(K,x)]::NfMaxOrd
    end
    z = NfMaxOrd(K)
    n = degree(K)
    B_K = basis(K)
    d = Array(nf_elem, n)
    for i in 1:n
      d[i] = elem_from_mat_row(K, x.num, i, x.den)
    end
    z.basis_nf = d
    z.basis_mat = x
    z.basis_mat_inv = inv(x)
    B = Array(NfOrdElem{NfMaxOrd}, n)
    for i in 1:n
      v = fill(zero(ZZ), n)
      v[i] = ZZ(1)
      B[i] = z(d[i], v)
    end

    z.basis_ord = B
    NfMaxOrdID[(K,x)] = z
    return z
  end

  function NfMaxOrd(b::Array{nf_elem, 1})
    K = parent(b[1])
    n = degree(K)
    A = FakeFmpqMat(basis_mat(K,b))

    if haskey(NfMaxOrdID, (K,A))
      return NfMaxOrdID[(K,A)]::NfMaxOrd
    end

    z = NfMaxOrd(K)
    z.basis_nf = b
    z.basis_mat = A
    z.basis_mat_inv = inv(A)

    B = Array(NfOrdElem{NfMaxOrd}, n)

    for i in 1:n
      v = fill(zero(ZZ), n)
      v[i] = ZZ(1)
      B[i] = z(b[i], v)
    end

    z.basis_ord = B

    NfMaxOrdID[(K,A)] = z
    return z
  end
end

################################################################################
#
#  NfMaxOrdIdlSet/NfMaxOrdIdl
#
################################################################################

const NfMaxOrdIdlSetID = ObjectIdDict()

type NfMaxOrdIdlSet <: NfOrdIdlSet
  order::NfMaxOrd

  function NfMaxOrdIdlSet(O::NfMaxOrd)
    if haskey(NfMaxOrdIdlSetID, O)
      return NfMaxOrdIdlSetID[O]::NfMaxOrdIdlSet
    else
      r = new(O)
      NfMaxOrdIdlSetID[O] = r
      return r::NfMaxOrdIdlSet
    end
  end
end

@doc """
  NfMaxOrdIdl(O::NfMaxOrd, a::fmpz_mat) -> NfMaxOrdIdl

    Creates the ideal of O with basis matrix a.
    No sanity checks. No data is copied, a should not be used anymore.

  NfMaxOrdIdl(a::fmpz, b::NfOrdElem) -> NfMaxOrdIdl

    Creates the ideal (a,b) of the order of b.
    No sanity checks. Note data is copied, a and b should not be used anymore.
  
  NfMaxOrdIdl(O::NfMaxOrd, a::fmpz, b::nf_elem) -> NfMaxOrdIdl

    Creates the ideal (a,b) of O.
    No sanity checks. No data is copied, a and b should be used anymore.
  
  NfMaxOrdIdl(x::NfOrdElem) -> NfMaxOrdIdl

    Creates the principal ideal (x) of the order of O.
    No sanity checks. No data is copied, x should not be used anymore.

""" ->
type NfMaxOrdIdl <: NfOrdIdl
  basis::Array{NfOrdElem{NfMaxOrd}, 1}
  basis_mat::fmpz_mat
  basis_mat_inv::FakeFmpqMat
  gen_one::fmpz
  gen_two::NfOrdElem{NfMaxOrd}
  gens_short::Bool
  gens_normal::fmpz
  gens_weakly_normal::Bool # true if Norm(A) = gcd(Norm, Norm)
                           # weaker than normality - at least potentialy
  norm::fmpz
  minimum::fmpz
  is_prime::Int            # 0: don't know
                           # 1 known to be prime
                           # 2 known to be not prime
  is_zero::Int             # as above
  is_principal::Int        # as above
  princ_gen::NfOrdElem{NfMaxOrd}
  princ_gen_special::Tuple{Int, Int, fmpz}
                           # first entry encodes the following:
                           # 0: don't know
                           # 1: second entry generates the ideal
                           # 2: third entry generates the ideal
  splitting_type::Tuple{Int, Int}
                           #
  anti_uniformizer::NfOrdElem{NfMaxOrd}
                           # If A is unramified, prime with minimum p,
                           # this element is in pA^-1
                           # Used for the residue map

  valuation::Function      # a function returning "the" valuation -
                           # mind that the ideal is not prime

  parent::NfMaxOrdIdlSet
  
  function NfMaxOrdIdl(O::NfMaxOrd)
    # populate the bits types (Bool, Int) with default values
    r = new()
    r.parent = NfMaxOrdIdlSet(O)
    r.gens_short = false
    r.gens_weakly_normal = false
    r.is_zero = 0
    r.is_prime = 0
    r.is_principal = 0
    r.splitting_type = (0,0)
    return r
  end

  function NfMaxOrdIdl(O::NfMaxOrd, a::fmpz_mat)
    # create ideal of O with basis_matrix a
    # Note that the constructor 'destroys' a, a should not be used anymore
    r = NfMaxOrdIdl(O)
    r.basis_mat = a
    return r
  end

  function NfMaxOrdIdl(a::fmpz, b::NfOrdElem{NfMaxOrd})
    # create ideal (a,b) of order(b)
    r = NfMaxOrdIdl(parent(b))
    r.gen_one = a
    r.gen_two = b
    return r
  end
 
  function NfMaxOrdIdl(O::NfMaxOrd, a::fmpz, b::nf_elem)
    # create ideal (a,b) of O
    r = NfMaxOrdIdl(a, O(b, false))
    return r
  end

  function NfMaxOrdIdl(x::NfOrdElem{NfMaxOrd})
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    O = parent(x)
    C = NfMaxOrdIdl(O)
    C.princ_gen = x
    C.is_principal = 1

    if iszero(x)
      C.is_zero = 1
    end

    C.gen_one = norm(x)
    C.gen_two = x

    C.gens_normal = C.gen_one
    C.gens_weakly_normal = true

    return C
  end

  function NfMaxOrdIdl(O::NfMaxOrd, x::Int)
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    C = NfMaxOrdIdl(O)
    C.princ_gen = O(x)
    C.princ_gen_special = (1, Int(x), fmpz(0))
    return C
  end

  function NfMaxOrdIdl(O::NfMaxOrd, x::fmpz)
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    C = NfMaxOrdIdl(O)
    C.princ_gen = O(x)
    C.princ_gen_special = (2, Int(0), abs(x))
    return C
  end

end

################################################################################
#
#  NfMaxOrdFracIdlSet/NfMaxOrdFracIdl
#
################################################################################

const NfMaxOrdFracIdlSetID = Dict{NfMaxOrd, NfOrdFracIdlSet}()

type NfMaxOrdFracIdlSet <: NfOrdFracIdlSet
   order::NfMaxOrd
   function NfMaxOrdFracIdlSet(O::NfMaxOrd)
     try
       return NfMaxOrdFracIdlSetID[O]::NfMaxOrdFracIdlSet
     catch
       r = new()
       r.order = O
       NfMaxOrdFracIdlSetID[O] = r
       return r::NfMaxOrdFracIdlSet
     end
   end
end

type NfMaxOrdFracIdl <: NfOrdFracIdl
  num::NfMaxOrdIdl
  den::fmpz
  basis_mat::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat
  parent::NfMaxOrdFracIdlSet

  function NfMaxOrdFracIdl(x::NfMaxOrdIdl, y::fmpz)
    z = new()
    z.parent = NfMaxOrdFracIdlSet(order(x))
    z.num = x
    z.den = y
    return z
  end
end

################################################################################
#
#  UnitGrpCtx
#
################################################################################

type UnitGrpCtx{T <: Union{nf_elem, FacElem{nf_elem}}}
  order::NfOrd
  rank::Int
  full_rank::Bool
  units::Array{T, 1}
  regulator::arb
  tentative_regulator::arb
  regulator_precision::Int
  torsion_units::Array{NfOrdElem{NfMaxOrd}, 1}
  torsion_units_order::Int
  torsion_units_gen::NfOrdElem{NfMaxOrd}
  conj_log_cache::Dict{Int, Dict{nf_elem, arb}}
  conj_log_mat_cutoff::Dict{Int, arb_mat}
  conj_log_mat_cutoff_inv::Dict{Int, arb_mat}
  rel_add_prec::Int

  function UnitGrpCtx(O::NfOrd)
    z = new()
    z.order = O
    z.rank = -1
    z.full_rank = false
    z.regulator_precision = -1
    z.torsion_units_order = -1
    z.units = Array{T, 1}()
    z.conj_log_mat_cutoff = Dict{Int, arb_mat}()
    z.conj_log_mat_cutoff_inv = Dict{Int, arb_mat}()
    z.rel_add_prec = 32
    return z
  end
end

################################################################################
#
#  analytic_func
#
################################################################################

type analytic_func{T<:Number}
  coeff::Array{T, 1}
  valid::Tuple{T, T}
  function analytic_func()
    return new()
  end
end

################################################################################
#
#  BigComplex
#
################################################################################

type BigComplex 
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

type roots_ctx
  f::fmpz_poly
  r_d::Array{BigComplex, 1}  # the 1st r1 ones will be real
  r::Array{BigComplex, 1}    # the complexes and at the end, the conjugated
  r1::Int
  r2::Int
  minkowski_mat::Array{BigFloat, 2} # cacheing: I currently
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
end

################################################################################
#
#  _RealRing
#
################################################################################

type _RealRing
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

type node{T}
  content::T
  left::node{T}
  right::node{T}

  function node(a::T)
    f = new()
    f.content = a
    return f
  end

  function node(a::T, b::node{T}, c::node{T})
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

type FactorBase{T}
  prod::T
  base::Union{Set{T}, AbstractArray{T, 1}}
  ptree::node{T}

  function FactorBase(a::T, b::Set{T})
    f = new()
    f.prod = a
    f.base = b
    return f
  end
  function FactorBase(a::T, b::AbstractArray{T, 1})
    f = new()
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

type FactorBaseSingleP
  P::fmpz
  pt::FactorBase{nmod_poly}
  lp::Array{Tuple{Int,NfMaxOrdIdl}, 1}
  doit::Function
  
  function FactorBaseSingleP(p::fmpz, lp::Array{Tuple{Int, NfMaxOrdIdl}, 1})
    FB = new()
    FB.lp = lp
    FB.P = p
    O = order(lp[1][2])
    K = O.nf

    naive_doit = function(a::nf_elem, v::Int)
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

    if length(lp) < 3 || is_index_divisor(O, p) # ie. index divisor or so
      int_doit = naive_doit
    else
      Zx = PolynomialRing(ZZ, "x")[1]
      Fpx = PolynomialRing(ResidueRing(ZZ, p), "x")[1]
      Qx = parent(K.pol)
      fp = Fpx(Zx(K.pol))
      lf = [ gcd(fp, Fpx(Zx(Qx(K(P[2].gen_two)))))::nmod_poly for P = lp]

      FB.pt = FactorBase(Set(lf), check = false)
      int_doit = function(a::nf_elem, v::Int)
        g = Fpx(a)
        g = gcd(g, fp)
        fl = is_smooth(FB.pt, g)[1]
        if fl
          d = factor(FB.pt, g)
          r = Array{Tuple{Int, Int}, 1}()
          vv=v
          for x in keys(d)
            id = findfirst(lf, x)
            vv -= FB.lp[id][2].splitting_type[2]
            push!(r, (FB.lp[id][1], 1))
          end
          if vv == 0
            return r, vv
          end
          r = Array{Tuple{Int, Int}, 1}()
          for x in keys(d)
            id = findfirst(lf, x)
            vl  = valuation(a, lp[id][2])
            v -= FB.lp[id][2].splitting_type[2]*vl
            push!(r, (FB.lp[id][1], vl))
          end
          return r, v
        else
          return Array{Tuple{Int, Int}, 1}(), -1
        end
      end  
    end
    FB.doit = function(a::nf_elem, v::Int)
      d = den(a)
      if isone(gcd(d, p)) return int_doit(a, v); end
      return naive_doit(a, v); 
    end  
    return FB
  end
end  

type NfFactorBase
  fb::Dict{fmpz, FactorBaseSingleP}
  size::Int
  fb_int::FactorBase{fmpz}
  ideals::Array{NfMaxOrdIdl, 1}
  rw::Array{Int, 1}
  mx::Int

  function NfFactorBase()
    r = new(Dict{fmpz, Array{Tuple{Int, NfMaxOrdIdl}, 1}}())
    r.size = 0
    return r
  end
end

################################################################################
#
#  ClassGrpCtx
#
################################################################################

type ClassGrpCtx{T}  # T should be a matrix type: either fmpz_mat or Smat{}
  FB::NfFactorBase
  M::T                    # the relation matrix, columns index by the
                          # factor basis, rows by the relations
  R::Array{nf_elem, 1}    # the relations
  RS::Set{nf_elem}
  H::T                    # the last hnf, at least the non-trivial part
                          # of it
  last_H::Int             # the number of rows of M that went into H
  last_piv1::Array{Int, 1}
  H_is_modular::Bool
  mis::Set{Int}
  h::fmpz
  c::roots_ctx
  rel_cnt::Int
  bad_rel::Int
  hnf_call::Int
  hnf_time::Float64
  last::Int

  largePrimeCnt::Int
  B2::Int
  largePrime::Dict{fmpz_poly, Tuple{nf_elem, fmpq}}
  largePrime_success::Int
  largePrime_no_success::Int
  relNorm::Array{Tuple{nf_elem, fmpz}, 1}
  relPartialNorm::Array{Tuple{nf_elem, fmpz}, 1}
  randomClsEnv::Array{NfMaxOrdIdl, 1}

  val_base::fmpz_mat      # a basis for the possible infinite ranodmization 
                          # vectors: conditions are
                          #  - sum over all = 0
                          #  - indices correspoding to complex pairs are
                          #    identical
                          # done via lll + nullspace

  rel_mat_mod::Smat{UIntMod}  # the echelonization of relation matrix modulo
                              # a small prime
  rel_mat_full_rank::Bool
  H_trafo::Array{Any, 1}

  function ClassGrpCtx()
    r = new()
    r.R = Array{nf_elem, 1}()
    r.RS = Set(r.R)
    r.largePrimeCnt = 0
    r.largePrime = Dict{fmpz_poly, Tuple{nf_elem, fmpq}}()
    r.largePrime_success = 0
    r.largePrime_no_success = 0
    r.relNorm=Array{Tuple{nf_elem, fmpz}, 1}()
    r.relPartialNorm=Array{Tuple{nf_elem, fmpz}, 1}()
    r.B2 = 0
    r.H_is_modular = true
    r.rel_mat_full_rank = false
    r.H_trafo = []
    r.H = T()
    return r
  end  
end

################################################################################
#
#  IdealRelationCtx
#
################################################################################

type IdealRelationsCtx{Tx, TU, TC}
  A::NfMaxOrdIdl
  v::Array{Int, 1}  # the infinite valuation will be exp(v[i])
  E::enum_ctx{Tx, TU, TC}
  c::fmpz           # the last length
  cnt::Int
  bad::Int
  restart::Int
  M::fmpz_mat
  vl::Int
  rr::Range{Int}

  function IdealRelationsCtx(clg::ClassGrpCtx, A::NfMaxOrdIdl;
                  prec::Int = 100, val::Int=0, limit::Int = 0)
    v = MatrixSpace(FlintZZ, 1, rows(clg.val_base))(Base.rand(-val:val, 1,
                    rows(clg.val_base)))*clg.val_base
    E = enum_ctx_from_ideal(clg.c, A, v, prec = prec, limit = limit,
       Tx = Tx, TU = TU, TC = TC)::enum_ctx{Tx, TU, TC}
    I = new()
    I.E = E
    I.A = A
    I.c = 0
    I.cnt = 0
    I.bad = 0
    I.restart = 0
    I.vl = 0
    I.rr = 1:0
    I.M = MatrixSpace(FlintZZ, 1, I.E.n)()
    return I
  end
end

################################################################################
#
#  Quotient rings of maximal orders of simple number fields
#
################################################################################

type NfMaxOrdQuoRing <: Ring
  base_ring::NfMaxOrd
  ideal::NfMaxOrdIdl
  basis_mat::fmpz_mat
  preinvn::Array{fmpz_preinvn_struct, 1}

  # temporary variables for divisor and annihilator computations
  # don't use for anything else
  tmp_xxgcd::fmpz_mat # used only by xxgcd in NfMaxOrd/ResidueRing.jl
  tmp_div::fmpz_mat # used only by div in NfMaxOrd/ResidueRing.jl
  tmp_ann::fmpz_mat # used only by annihilator in NfMaxOrd/ResidueRing.jl
  tmp_euc::fmpz_mat # used only by euclid in NfMaxOrd/ResidueRing.jl

  function NfMaxOrdQuoRing(O::NfMaxOrd, I::NfMaxOrdIdl)
    z = new()
    z.base_ring = O
    z.ideal = I
    z.basis_mat = basis_mat(I)
    z.preinvn = [ fmpz_preinvn_struct(z.basis_mat[i, i]) for i in 1:degree(O)]
    d = degree(O)
    z.tmp_div = MatrixSpace(ZZ, 2*d + 1, 2*d + 1)()
    z.tmp_xxgcd = MatrixSpace(ZZ, 3*d + 1, 3*d + 1)()
    z.tmp_ann = MatrixSpace(ZZ, 2*d, d)()
    z.tmp_euc = MatrixSpace(ZZ, 2*d, d)()
    minimum(I) # compute the minimum
    return z
  end
end

type NfMaxOrdQuoRingElem <: RingElem
  elem::NfOrdElem{NfMaxOrd}
  parent::NfMaxOrdQuoRing

  function NfMaxOrdQuoRingElem(O::NfMaxOrdQuoRing, x::NfOrdElem{NfMaxOrd})
    z = new()
    z.elem = mod(x, ideal(O), O.preinvn)
    z.parent = O
    return z
  end
end

################################################################################
#
# Abelian Groups and their elements
#
################################################################################

abstract  GrpAb <: Nemo.Group
abstract  GrpAbElem <: Nemo.GroupElem
abstract  FinGenGrpAb <: GrpAb

type FinGenGrpAbSnf <: FinGenGrpAb
  snf::Array{fmpz, 1}
end

type FinGenGrpAbGen <: FinGenGrpAb
  rels::fmpz_mat
  hnf::fmpz_mat
  snf_map::Map{FinGenGrpAbGen, FinGenGrpAbSnf}

  function FinGenGrpAbGen(R::fmpz_mat; is_hnf::Bool = false)
    r = new()
    r.rels = R
    if is_hnf
      r.hnf = R
    end
    return r
  end  
end

type FinGenGrpAbElem{T <: FinGenGrpAb} <: GrpAbElem
  parent::T
  coeff::fmpz_mat
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

type NoElements <: Exception end

