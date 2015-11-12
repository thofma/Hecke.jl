export NfMaximalOrder

export MaximalOrder, conjugate_data

################################################################################
#
#  Types and memory management
#
################################################################################


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
  B = Array(NfOrderElem, length(b))
  for i in 1:length(b)
    v = fill(ZZ(0), length(b))
    v[i] = ZZ(1)
    B[i] = O(b[i], v; check = false)
  end
  O.basis_ord = B
  return B
end

function conjugate_data(O::NfMaximalOrder)
  if isdefined(O, :conjugate_data)
    return O.conjugate_data
  else
    # acb_root_ctx will find the roots of the polynomial
    # precision will be chosen so that roots can be separated
    # starting precision is 64
    O.conjugate_data = acb_root_ctx(nf(O).pol)
    return O.conjugate_data
  end
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

function basis(O::NfMaximalOrder, K::AnticNumberField)
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

"""
    MaximalOrder(K::AnticNumberField) -> NfMaximalOrder

Compute the maximal order of ``K`` using Dedekind's criterion and the classical
Round two algorithm.

Here is an example:
```jl
Qx, x = QQ["x"]
K, a = NumberField(x^3 + 2, "a")
O = MaximalOrder(K)
```
"""
function MaximalOrder(K::AnticNumberField)
  O = EquationOrder(K)
  @vprint :NfMaximalOrder 1 "Computing the maximal order ...\n"
  O = _MaximalOrder(O)
  @vprint :NfMaximalOrder 1 "... done\n"
  return NfMaximalOrder(K, basis_mat(O))
end

function MaximalOrder(K::AnticNumberField, primes::Array{fmpz, 1})
  O = EquationOrder(K)
  @vprint :NfMaximalOrder 1 "Computing the maximal order ...\n"
  O = _MaximalOrder(O, primes)
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

