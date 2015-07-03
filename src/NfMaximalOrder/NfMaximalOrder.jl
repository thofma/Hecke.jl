export NfMaximalOrder, MaximalOrder


################################################################################
#
#  Types and memory management
#
################################################################################

NfMaximalOrderID = Dict{Tuple{NfNumberField, FakeFmpqMat}, GenNfOrd}()

NfMaximalOrderSetID = ObjectIdDict()

type NfMaximalOrderSet
  nf::NfNumberField

  function NfMaximalOrderSet(a::NfNumberField)
  try
    return NfMaximalOrderSetID[a]
  end
    NfMaximalOrderSetID[a] = new(a)
    return NfMaximalOrderSetID[a]
  end
end

type NfMaximalOrder <: GenNfOrd
  nf::NfNumberField
  basis_nf::Array{nf_elem, 1}   # Array of number field elements
  basis_ord                     # Array of order elements
  basis_mat::FakeFmpqMat        # basis matrix of order wrt basis of K
  basis_mat_inv::FakeFmpqMat    # inverse of basis matrix
  index::fmpz                   # the determinant of basis_mat_inv
  disc::fmpz                    # discriminant
  disc_fac                      # factorized discriminant or prime factors?
  parent::NfMaximalOrderSet     # parent object
  signature::Tuple{Int, Int}    # signature of the parent object

  function NfMaximalOrder(a::NfNumberField)
    r = new(a)
    r.parent = NfMaximalOrderSet(a)
    r.signature = (-1,0)
    return r
  end
end

################################################################################
#
#  Constructors
#
################################################################################

function NfMaximalOrder(K::NfNumberField, x::FakeFmpqMat)
  if haskey(NfMaximalOrderID, (K,x))
    return NfMaximalOrderID[(K,x)]
  end
  z = NfMaximalOrder(K)
  n = degree(K)
  B_K = basis(K)
  d = Array(nf_elem, n)
  for i in 1:n
    d[i] = divexact(element_from_mat_row(K, x.num, i), x.den)
  end
  z.basis_nf = d
  z.basis_mat = x
  z.basis_mat_inv = inv(x)
  B = Array(NfMaximalOrderElem, n)
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
    return NfMaximalOrderID[(K,A)]
  end

  z = NfMaximalOrder(K)
  z.basis_nf = b
  z.basis_mat = A
  z.basis_mat_inv = inv(A)

  B = Array(NfMaximalOrderElem, n)

  for i in 1:n
    v = fill(zero(ZZ), n)
    v[i] = ZZ(1)
    B[i] = z(b[i], v)
  end

  z.basis_ord = B

  NfMaximalOrderID[(K,A)] = z
  return z
end

function NfMaximalOrder(O::PariMaximalOrder)
  K = O.pari_nf.nf
  n = degree(K)
  #z = NfMaximalOrder(K)
  b = basis(O)
  d = Array(nf_elem, n)
  Qx = K.pol.parent
  B = Array(NfMaximalOrderElem, n)

  for i in 1:n
    d[i] = K(Qx(b[i]))
  end
  return NfMaximalOrder(d)
end

################################################################################
#
#  Field access
#
################################################################################

function basis_ord(O::NfMaximalOrder)
  if isdefined(O, :basis_ord)
    return O.basis_ord
  end
  b = O.basis_nf
  B = Array(NfMaximalOrderElem, length(b))
  for i in 1:length(b)
    v = fill(ZZ(0), length(b))
    v[i] = ZZ(1)
    B[i] = O(b[i], v; check = false)
  end
  O.basis_ord = B
  return B
end

function basis_mat_inv(O::NfMaximalOrder)
  if isdefined(O, :basis_mat_inv)
    return O.basis_mat_inv
  else
    O.basis_mat_inv = inv(basis_mat(O))
    return O.basis_mat_inv
  end
end

function basis_mat(O::NfMaximalOrder)
  return O.basis_mat
end

function basis(O::NfMaximalOrder)
  return basis_ord(O)
end

function basis(O::NfMaximalOrder, K::NfNumberField)
  nf(O) != K && error()
  return basis_nf(O)
end

function basis_nf(O::NfMaximalOrder)
  return O.basis_nf
end

function index(O::NfMaximalOrder)
  if isdefined(O, :index)
    return O.index
  else
    O.index = divexact(basis_mat(O).den^degree(O), determinant(basis_mat(O).num))
    return O.index
  end
end

function discriminant(O::NfMaximalOrder)
  if isdefined(O, :disc)
    return O.disc
  end

  A = MatrixSpace(ZZ, degree(O), degree(O))()
  B = basis(O)
  for i in 1:degree(O)
    for j in 1:degree(O)
      A[i,j] = ZZ(trace(B[i]*B[j]))
    end
  end
  O.disc = determinant(A)
  return O.disc
end
nf(O::NfMaximalOrder) = O.nf

rank(x::NfMaximalOrder) = degree(nf(x))

degree(x::NfMaximalOrder) = degree(nf(x))

################################################################################
#
#  Containment
#
################################################################################

# Migrated to GenNfOrd.jl under new name _check_elem_in_order

#function _check_elem_in_maximal_order(x::nf_elem, O::NfMaximalOrder)
#  d = denominator(x)
#  b = d*x 
#  M = MatrixSpace(ZZ, 1, rank(O))()
#  element_to_mat_row!(M,1,b)
#  t = FakeFmpqMat(M,d)
#  z = t*basis_mat_inv(O)
#  v = Array(fmpz, degree(O))
#  for i in 1:degree(O)
#    v[i] = z.num[1,i]
#  end
#  return (z.den == 1, v)  
#end

#function in(a::nf_elem, O::NfMaximalOrder)
#  (x,y) = _check_elem_in_maximal_order(a,O)
#  return x
#end

################################################################################
#
#  Denominator
#
################################################################################

# Migrated to GenNfOrd.jl

#@doc """
#  denominator(a::nf_elem, O::NfMaximalOrder) -> fmpz
#
#  Compute the smalles positive integer k such that k*a in O.
#""" ->
#function denominator(a::nf_elem, O::NfMaximalOrder)
#  d = denominator(a)
#  b = d*a 
#  M = MatrixSpace(ZZ, 1, rank(O))()
#  element_to_mat_row!(M,1,b)
#  t = FakeFmpqMat(M,d)
#  z = t*basis_mat_inv(O)
#  return z.den
#end
#
################################################################################
#
#  Constructors for users
#
################################################################################

@doc """
  MaximalOrder(K::NfNumberField) -> NfMaximalOrder

  Compute the maximal order of K.
""" ->
function MaximalOrder(K::NfNumberField)
  O = EquationOrder(K)
  @vprint :NfMaximalOrder 1 "Computing the maximal order ...\n"
  O = _MaximalOrder(O)
  @vprint :NfMaximalOrder 1 "... done\n"
  return NfMaximalOrder(K, basis_mat(O))
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, O::NfMaximalOrder)
  print(io, "Maximal order of $(nf(O)) \nwith basis $(basis_nf(O))")
end

function PariMaximalOrder(O::NfMaximalOrder)
  return PariMaximalOrder(PariNumberField(nf(O)))
end


