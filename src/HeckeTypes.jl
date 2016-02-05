################################################################################
#
#  SmatRow/Smat
#
################################################################################
abstract abstest

type t1{A <: abstest, B} 
  x::A 
  y::B
end

type t2{C, T} <: abstest 
  x::C 
  y::T

  function t2(::Type{C}, ::Type{T})
    z = new{C, T}()  
    z.x = C(1)
    z.y = z
  end
end

t2{C, T}(::Type{C}, ::Type{T}) = t2{C, T}(C, T) 

Base.show{C, T}(io::IO, x::t2{C, T}) = print(io, "t2 with type $C and $T")

global const SLP_AddRow_typ = 1
global const SLP_SwapRows_typ = 2

type SmatSLP{T}
  row::Int
  col::Int
  typ::Int
  val::T  ##only used for AddRow
end

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
#  FactoredElemMon/FactoredElem
#
################################################################################

type FactoredElemMon{T <: RingElem} <: Ring
  base_ring::Ring  # for the base
  basis_conjugates_log::Dict{RingElem, Tuple{Int, Array{arb, 1}}}
  basis_conjugates::Dict{RingElem, Tuple{Int, Array{arb, 1}}}
  conj_log_cache::Dict{Int, Dict{nf_elem, Array{arb, 1}}}

  function FactoredElemMon(R::Ring)
    if haskey(FactoredElemMonDict, R)
      return FactoredElemMonDict[R]::FactoredElemMon
    else
      z = new()
      z.base_ring = R
      z.basis_conjugates_log = Dict{RingElem, Array{arb, 1}}()
      z.basis_conjugates = Dict{RingElem, Array{arb, 1}}()
      z.conj_log_cache = Dict{Int, Dict{nf_elem, arb}}()
      FactoredElemMonDict[R] = z
      return z
    end
  end
end

type FactoredElem{B}
  fac::Dict{B, fmpz}
  parent::FactoredElemMon

  function FactoredElem()
    z = new()
    z.fac = Dict{B, fmpz}()
    return z
  end
end

################################################################################
#
#  GenNfOrd/NfOrderElem
#
################################################################################

abstract GenNfOrd <: Ring{Antic}

type NfOrderElem <: RingElem
  elem_in_nf::nf_elem
  elem_in_basis::Array{fmpz, 1}
  has_coord::Bool
  parent::GenNfOrd

  function NfOrderElem(O::GenNfOrd)
    z = new()
    z.parent = O
    z.elem_in_nf = nf(O)() 
    z.elem_in_basis = Array(fmpz, degree(O))
    z.has_coord = false
    return z
  end

  function NfOrderElem(O::GenNfOrd, a::nf_elem)
    z = new()
    z.elem_in_nf = a
    z.elem_in_basis = Array(fmpz, degree(O))
    z.parent = O
    z.has_coord = false
    return z
  end

  function NfOrderElem(O::GenNfOrd, a::nf_elem, arr::Array{fmpz, 1})
    z = new()
    z.parent = O
    z.elem_in_nf = a
    z.has_coord = true
    z.elem_in_basis = arr
    return z
  end

  function NfOrderElem(O::GenNfOrd, arr::Array{fmpz, 1})
    z = new()
    z.elem_in_nf = dot(basis_nf(O), arr)
    z.has_coord = true
    z.elem_in_basis = arr
    z.parent = O
    return z
  end

  function NfOrderElem{T <: Integer}(O::GenNfOrd, arr::Array{T, 1})
    return NfOrderElem(O, map(ZZ, arr))
  end
end

################################################################################
#
#  NfOrder
#
################################################################################

const NfOrderSetID = ObjectIdDict()

type NfOrderSet
  nf::AnticNumberField

  function NfOrderSet(a::AnticNumberField)
  try
    return NfOrderSetID[a]::NfOrder
  end
    NfOrderSetID[a] = new(a)
    return NfOrderSetID[a]
  end
end

#const NfOrderID = Dict{Tuple{AnticNumberField, FakeFmpqMat}, GenNfOrd}()
const NfOrderID = ObjectIdDict()

type NfOrder <: GenNfOrd
  nf::AnticNumberField
  basis_nf::Array{nf_elem, 1}      # Basis as number field elements
  basis_ord::Array{NfOrderElem, 1} # Basis as order elements
  basis_mat::FakeFmpqMat           # Basis matrix with respect
                                   # to number field basis
  basis_mat_inv::FakeFmpqMat       # Inverse of basis matrix
  index::fmpz                      # ??
  disc::fmpz                       # Discriminant
  disc_fac                         # ??
  isequationorder::Bool            # Flag for being equation order
  parent::NfOrderSet               # Parent object
  signature::Tuple{Int, Int}       # Signature of the associated number field
                                   # (-1, 0) means 'not set'
  torsion_units::Tuple{Array{NfOrderElem, 1}, NfOrderElem}

  function NfOrder()
    z = new()
    # Populate with 'default' values
    z.signature = (-1,0)      
    z.isequationorder = false
    return z
  end

  function NfOrder(K::AnticNumberField)
    A = FakeFmpqMat(one(MatrixSpace(FlintZZ, degree(K), degree(K))))
    if haskey(NfOrderID, (K,A))
      return NfOrderID[(K,A)]::NfOrder
    else
      z = NfOrder()
      z.parent = NfOrderSet(K)
      z.nf = K
      z.basis_mat = A
      z.basis_nf = basis(K)
      z.basis_ord = Array(NfOrderElem, degree(K))
      z.basis_ord[1] = z(K(1), false)
      for i in 2:degree(K)
        z.basis_ord[i] = z(gen(K)^(i-1), false)
      end
      NfOrderID[(K, A)] = z
      return z::NfOrder
    end
  end

  # Construct the order with basis matrix x
  function NfOrder(K::AnticNumberField, x::FakeFmpqMat)
    if haskey(NfOrderID, (K,x))
      return NfOrderID[(K,x)]::NfOrder
    else
      z = NfOrder()
      z.parent = NfOrderSet(K)
      z.nf = K
      z.basis_mat = x
      B = Array(NfOrderElem, degree(K))
      BB = Array(nf_elem, degree(K))
      for i in 1:degree(K)
        t = elem_from_mat_row(K, x.num, i, x.den)
        BB[i] = t
        B[i] = z(t, false) 
      end
      z.basis_ord = B
      z.basis_nf = BB
      z.parent = NfOrderSet(z.nf)
      NfOrderID[(K,x)] = z
      return z::NfOrder
    end
  end

  # Construct the order with basis a
  function NfOrder(a::Array{nf_elem, 1})
    K = parent(a[1])
    A = FakeFmpqMat(basis_mat(K,a))
    if haskey(NfOrderID, (K,A))
      return NfOrderID[(K,A)]::NfOrder
    else
      z = NfOrder()
      z.parent = NfOrderSet(K)
      z.nf = K
      z.basis_nf = a
      z.basis_mat = A
      z.basis_ord = Array(NfOrderElem, degree(K))
      for i in 1:degree(K)
        z.basis_ord[i] = z(a[i], false)
      end
      NfOrderID[(K,A)] = z
      return z::NfOrder
    end
  end
end

################################################################################
#
#  GenNfOrdIdl/NfOrderIdealSet/NfOrderIdeal
#
################################################################################

abstract GenNfOrdIdl

NfOrderIdealSetID = ObjectIdDict()

type NfOrderIdealSet
  order::NfOrder
  
  function NfOrderIdealSet(a::NfOrder)
    try
      return NfOrderIdealSetID[a]
    catch
      NfOrderIdealSetID[a] = new(a)
      return NfOrderIdealSetID[a]
    end
  end
end

type NfOrderIdeal <: GenNfOrdIdl
  basis::Array{NfOrderElem, 1}
  basis_mat::fmpz_mat
  basis_mat_inv::FakeFmpqMat
  parent::NfOrderIdealSet

  function NfOrderIdeal(O::NfOrder, a::fmpz)
    z = new()
    z.parent = NfOrderIdealSet(O)
    z.basis_mat = MatrixSpace(ZZ, degree(O), degree(O))(a)
    return z
  end

  function NfOrderIdeal(O::NfOrder, a::fmpz_mat)
    z = new()
    z.parent = NfOrderIdealSet(O)
    z.basis_mat = a
    return z
  end
end

################################################################################
#
#  NfOrderFracIdealSet/NfOrderFracIdeal
#
################################################################################

NfOrderFracIdealSetID = ObjectIdDict()

type NfOrderFracIdealSet
  order::NfOrder
  
  function NfOrderFracIdealSet(a::NfOrder)
    try
      return NfOrderFracIdealSetID[a]
    catch
      NfOrderFracIdealSetID[a] = new(a)
      return NfOrderFracIdealSetID[a]
    end
  end
end

type NfOrderFracIdeal
  basis::Array{NfOrderElem, 1}
  basis_mat::FakeFmpqMat
  basis_mat_inv::FakeFmpqMat
  parent::NfOrderFracIdealSet
  
  function NfOrderFracIdeal(O::NfOrder, a::FakeFmpqMat)
    z = new()
    z.basis_mat = a
    z.parent = NfOrderFracIdealSet(O)
    return z
  end
end

################################################################################
#
#  NfMaximalOrderSet/NfMaximalOrder
#
################################################################################

const NfMaximalOrderID = Dict{Tuple{AnticNumberField, FakeFmpqMat}, GenNfOrd}()

const NfMaximalOrderSetID = ObjectIdDict()

type NfMaximalOrderSet
  nf::AnticNumberField

  function NfMaximalOrderSet(a::AnticNumberField)
  try
    return NfMaximalOrderSetID[a]::NfMaximalOrderSet
  end
    NfMaximalOrderSetID[a] = new(a)
    return NfMaximalOrderSetID[a]
  end
end

type NfMaximalOrder <: GenNfOrd
  nf::AnticNumberField
  basis_nf::Array{nf_elem, 1}      # Array of number field elements
  basis_ord::Array{NfOrderElem, 1} # Array of order elements
  basis_mat::FakeFmpqMat           # basis matrix of order wrt basis of K
  basis_mat_inv::FakeFmpqMat       # inverse of basis matrix
  index::fmpz                      # the determinant of basis_mat_inv
  disc::fmpz                       # discriminant
  parent::NfMaximalOrderSet        # parent object
  signature::Tuple{Int, Int}       # signature of the parent object
                                   # (-1, 0) means 'not set'
  conjugate_data::acb_root_ctx
  minkowski_mat::Tuple{arb_mat, Int}        # Minkowski matrix
  torsion_units::Tuple{Array{NfOrderElem, 1}, NfOrderElem}

  function NfMaximalOrder(a::AnticNumberField)
    r = new(a)
    r.parent = NfMaximalOrderSet(a)
    r.signature = (-1,0)
    return r
  end

  function NfMaximalOrder(K::AnticNumberField, x::FakeFmpqMat)
    if haskey(NfMaximalOrderID, (K,x))
      return NfMaximalOrderID[(K,x)]::NfMaximalOrder
    end
    z = NfMaximalOrder(K)
    n = degree(K)
    B_K = basis(K)
    d = Array(nf_elem, n)
    for i in 1:n
      d[i] = elem_from_mat_row(K, x.num, i, x.den)
    end
    z.basis_nf = d
    z.basis_mat = x
    z.basis_mat_inv = inv(x)
    B = Array(NfOrderElem, n)
    for i in 1:n
      v = fill(zero(ZZ), n)
      v[i] = ZZ(1)
      B[i] = z(d[i], v)
    end

    z.basis_ord = B
    NfMaximalOrderID[(K,x)] = z
    return z
  end

  function NfMaximalOrder(b::Array{nf_elem, 1})
    K = parent(b[1])
    n = degree(K)
    A = FakeFmpqMat(basis_mat(K,b))

    if haskey(NfMaximalOrderID, (K,A))
      return NfMaximalOrderID[(K,A)]::NfMaximalOrder
    end

    z = NfMaximalOrder(K)
    z.basis_nf = b
    z.basis_mat = A
    z.basis_mat_inv = inv(A)

    B = Array(NfOrderElem, n)

    for i in 1:n
      v = fill(zero(ZZ), n)
      v[i] = ZZ(1)
      B[i] = z(b[i], v)
    end

    z.basis_ord = B

    NfMaximalOrderID[(K,A)] = z
    return z
  end
end

################################################################################
#
#  NfMaximalOrderIdealSet/NfMaximalOrderIdeal
#
################################################################################

const NfMaximalOrderIdealSetID = ObjectIdDict()

type NfMaximalOrderIdealSet <: Ring
  order::NfMaximalOrder
  function NfMaximalOrderIdealSet(O::NfMaximalOrder)
    if haskey(NfMaximalOrderIdealSetID, O)
      return NfMaximalOrderIdealSetID[O]::NfMaximalOrderIdealSet
    else
      r = new(O)
      NfMaximalOrderIdealSetID[O] = r
      return r
    end
  end
end

@doc """
  NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz_mat) -> NfMaximalOrderIdeal

    Creates the ideal of O with basis matrix a.
    No sanity checks. No data is copied, a should not be used anymore.

  NfMaximalOrderIdeal(a::fmpz, b::NfOrderElem) -> NfMaximalOrderIdeal

    Creates the ideal (a,b) of the order of b.
    No sanity checks. Note data is copied, a and b should not be used anymore.
  
  NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz, b::nf_elem) -> NfMaximalOrderIdeal

    Creates the ideal (a,b) of O.
    No sanity checks. No data is copied, a and b should be used anymore.
  
  NfMaximalOrderIdeal(x::NfOrderElem) -> NfMaximalOrderIdeal

    Creates the principal ideal (x) of the order of O.
    No sanity checks. No data is copied, x should not be used anymore.

""" ->
type NfMaximalOrderIdeal <: GenNfOrdIdl
  basis::Array{NfOrderElem, 1}
  basis_mat::fmpz_mat
  basis_mat_inv::FakeFmpqMat
  gen_one::fmpz
  gen_two::NfOrderElem
  gens_short::Bool
  gens_normal::fmpz
  gens_weakly_normal::Bool # true if Norm(A) = gcd(Norm, Norm)
                           # weaker than normality - at least potentialy
  norm::fmpz
  minimum::fmpz
  is_prime::Int            # 0: don't know
                           # 1 known to be prime
                           # 2 known to be not prime
  is_principal::Int        # as above
  princ_gen::NfOrderElem
  splitting_type::Tuple{Int, Int}
                           #
  anti_uniformizer::NfOrderElem
                           # If A is unramified, prime with minimum p,
                           # this element is in pA^-1
                           # Used for the residue map

  valuation::Function      # a function returning "the" valuation -
                           # mind that the ideal is not prime

  parent::NfMaximalOrderIdealSet
  
  function NfMaximalOrderIdeal(O::NfMaximalOrder)
    # populate the bits types (Bool, Int) with default values
    r = new()
    r.parent = NfMaximalOrderIdealSet(O)
    r.gens_short = false
    r.gens_weakly_normal = false
    r.is_prime = 0
    r.is_principal = 0
    r.splitting_type = (0,0)
    return r
  end

  function NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz_mat)
    # create ideal of O with basis_matrix a
    # Note that the constructor 'destroys' a, a should not be used anymore
    r = NfMaximalOrderIdeal(O)
    r.basis_mat = a
    return r
  end

  function NfMaximalOrderIdeal(a::fmpz, b::NfOrderElem)
    # create ideal (a,b) of order(b)
    r = NfMaximalOrderIdeal(parent(b))
    r.gen_one = a
    r.gen_two = b
    return r
  end
 
  function NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz, b::nf_elem)
    # create ideal (a,b) of O
    r = NfMaximalOrderIdeal(a, O(b, false))
    return r
  end

  function NfMaximalOrderIdeal(x::NfOrderElem)
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    O = parent(x)
    b = x.elem_in_nf

    bi = inv(b)

    C = NfMaximalOrderIdeal(O)
    C.gen_one = den(bi, O)
    C.minimum = C.gen_one
    C.gen_two = x
    C.norm = abs(num(norm(b)))
    @hassert :NfMaximalOrder 1 gcd(C.gen_one^degree(O),
                    ZZ(norm(C.gen_two))) == C.norm
    C.princ_gen = C.gen_two

    if C.gen_one == 1
      C.gens_normal = 2*C.gen_one
    else
      C.gens_normal = C.gen_one
    end
    C.gens_weakly_normal = 1
    return C
  end
end

################################################################################
#
#  NfMaximalOrderFracIdealSet/NfMaximalOrderFracIdeal
#
################################################################################

const NfMaximalOrderFracIdealSetID = Dict{NfMaximalOrder, Ring}()

type NfMaximalOrderFracIdealSet <: Ring
   order::NfMaximalOrder
   function NfMaximalOrderFracIdealSet(O::NfMaximalOrder)
     try
       return NfMaximalOrderFracIdealSetID[O]::NfMaximalOrderFracIdealSet
     catch
       r = new()
       r.order = O
       NfMaximalOrderFracIdealSetID[O] = r
       return r
     end
   end
end

type NfMaximalOrderFracIdeal
  num::NfMaximalOrderIdeal
  den::fmpz
  basis_mat::FakeFmpqMat
  parent::NfMaximalOrderFracIdealSet

  function NfMaximalOrderFracIdeal(x::NfMaximalOrderIdeal, y::fmpz)
    z = new()
    z.parent = NfMaximalOrderFracIdealSet(order(x))
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

type UnitGrpCtx{T <: Union{nf_elem, FactoredElem{nf_elem}}}
  order::GenNfOrd
  rank::Int
  full_rank::Bool
  units::Array{T, 1}
  regulator::arb
  tentative_regulator::arb
  regulator_precision::Int
  torsion_units::Array{NfOrderElem, 1}
  torsion_units_order::Int
  torsion_units_gen::NfOrderElem
  conj_log_cache::Dict{Int, Dict{nf_elem, arb}}

  function UnitGrpCtx(O::GenNfOrd)
    z = new()
    z.order = O
    z.rank = -1
    z.full_rank = false
    z.regulator_precision = -1
    z.torsion_units_order = -1
    z.units = Array{T, 1}()
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
  lp::Array{Tuple{Int,NfMaximalOrderIdeal}, 1}
  doit::Function
  
  function FactorBaseSingleP(p::fmpz, lp::Array{Tuple{Int, NfMaximalOrderIdeal}, 1})
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
        g = Fpx(Zx(Qx(a)))
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
      if isone(d) return int_doit(a, v); end
      return naive_doit(a, v); 
    end  
    return FB
  end
end  

type NfFactorBase
  fb::Dict{fmpz, FactorBaseSingleP}
  size::Int
  fb_int::FactorBase{fmpz}
  ideals::Array{NfMaximalOrderIdeal, 1}
  rw::Array{Int, 1}
  mx::Int

  function NfFactorBase()
    r = new(Dict{fmpz, Array{Tuple{Int, NfMaximalOrderIdeal}, 1}}())
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

  val_base::fmpz_mat      # a basis for the possible infinite ranodmization 
                          # vectors: conditions are
                          #  - sum over all = 0
                          #  - indices correspoding to complex pairs are
                          #    identical
                          # done via lll + nullspace
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
    return r
  end  
end

################################################################################
#
#  IdealRelationCtx
#
################################################################################

type IdealRelationsCtx{Tx, TU, TC}
  A::NfMaximalOrderIdeal
  v::Array{Int, 1}  # the infinite valuation will be exp(v[i])
  E::enum_ctx{Tx, TU, TC}
  c::fmpz           # the last length
  cnt::Int
  bad::Int
  restart::Int
  M::fmpz_mat
  vl::Int
  rr::Range{Int}

  function IdealRelationsCtx(clg::ClassGrpCtx, A::NfMaximalOrderIdeal;
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

include("Map/MapType.jl")

################################################################################
#
#  Abelian groups
#
################################################################################

const AbGrpID = Dict{Array{fmpz, 1}, Nemo.Set}()

type AbGrp <: Nemo.Set
  diagonal::Array{fmpz, 1}
  order::fmpz
  inf_num::Int
  fin_num::Int
  
  function AbGrp(a::Array{fmpz, 1})
    sort!(a)
    println(a, " ",hash(a))
    if haskey(AbGrpID, a)
      return AbGrpID[a]::AbGrp
    else
      z = new()
      z.diagonal = a
      z.inf_num = findfirst(x -> x != 0, a) - 1
      z.fin_num = length(a) - z.inf_num
      AbGrpID[a] = z
      return z
    end
  end
  
  function AbGrp(a::Array{Int, 1})
    return AbGrp(map(fmpz, a))
  end
end

type AbGrpElem
  parent::AbGrp
  coord::Array{fmpz, 1}

  function AbGrpElem(A::AbGrp, a::Array{fmpz, 1})
    z = new()
    z.parent = A
    z.coord = a
    return z
  end
end


################################################################################
#
#  NoElements
#
################################################################################

type NoElements <: Exception end
