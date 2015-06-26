################################################################################
#
#  GenNfOrd.jl : Generic orders in number fields
#
################################################################################

# So far, this is only a common supertype for NfOrder and NfMaximalOrder

abstract GenNfOrd 

abstract GenNfOrdIdeal

abstract GenNfOrdElem

################################################################################
#
#  Compute the p-radical
#
################################################################################

function pradical(O::GenNfOrd, p::fmpz)
  j = clog(fmpz(degree(O)),p)
  R = ResidueRing(ZZ,p)
  A = MatrixSpace(R, degree(O), degree(O))()
  for i in 1:degree(O)
    t = powermod(basis(O)[i], p^j, p)
    ar = elem_in_basis(t)
    for k in 1:degree(O)
      A[i,k] = ar[k]
    end
  end
  X = kernel(A)
  Mat = MatrixSpace(ZZ, 1, degree(O))
  MMat = MatrixSpace(R, 1, degree(O))
  if length(X) != 0
    m = lift(MMat(X[1]))
    for x in 2:length(X)
      m = vcat(m,lift(MMat(X[x])))
    end
    m = vcat(m,MatrixSpace(ZZ, degree(O), degree(O))(p))
  else
    m = MatrixSpace(ZZ, degree(O), degree(O))(p)
  end
  r = sub(_hnf(m, :lowerleft), rows(m) - degree(O) + 1:rows(m), 1:degree(O))
  return ideal(O,r)
end

function pradical(O::GenNfOrd, p::Integer)
  return pradical(O, fmpz(p))
end

################################################################################
#
#  Signature
#
################################################################################

function signature(x::GenNfOrd)
  if x.signature[1] != -1
    return x.signature
  else
    x.signature = signature(nf(x).pol)
    return x.signature
  end
end

################################################################################
#
#  Number field element containment
#
################################################################################

# Check if a is contained in O
# In this case, also return the coefficient vector v
function _check_elem_in_order(a::nf_elem, O::GenNfOrd)
  d = denominator(a)
  b = d*a 
  M = MatrixSpace(ZZ, 1, degree(O))()
  element_to_mat_row!(M,1,b)
  t = FakeFmpqMat(M,d)
  x = t*basis_mat_inv(O)
  v = Array(fmpz, degree(O))
  for i in 1:degree(O)
    v[i] = x.num[1,i]
  end
  return (x.den == 1, v) 
end  

function in(a::nf_elem, O::GenNfOrd)
  (x,y) = _check_elem_in_maximal_order(a,O)
  return x
end

################################################################################
#
#  Denominator in an order
#
################################################################################

@doc """
  denominator(a::nf_elem, O::GenNfOrd) -> fmpz

  Compute the smalles positive integer k such that k*a in O.
""" ->
function denominator(a::nf_elem, O::GenNfOrd)
  d = denominator(a)
  b = d*a 
  M = MatrixSpace(ZZ, 1, degree(O))()
  element_to_mat_row!(M,1,b)
  t = FakeFmpqMat(M,d)
  z = t*basis_mat_inv(O)
  return z.den
end

################################################################################
#
#  Discriminant
#
################################################################################

function discriminant(O::GenNfOrd)
  if isdefined(O, :disc)
    return O.disc
  end
  A = MatrixSpace(ZZ, degree(O), degree(O))()
  B = basis_nf(O)
  for i in 1:degree(O)
    for j in 1:degree(O)
      A[i,j] = FlintZZ(trace(B[i]*B[j]))
    end
  end
  O.disc = determinant(A)
  return O.disc
end
