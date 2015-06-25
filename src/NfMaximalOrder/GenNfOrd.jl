#################################################################################
#
#  ComOrd.jl : Commutative orders (over principal ideal domains)
#
#################################################################################

# So far, this is only a common type for NfOrder and NfMaximalOrder

abstract GenNfOrd 

abstract GenNfOrdIdeal

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
  return ideal(O,sub(_hnf(m, :lowerleft), rows(m) - degree(O) + 1:rows(m), 1:degree(O)))
end

function pradical(O::GenNfOrd, p::Integer)
  return pradical(O, fmpz(p))
end

