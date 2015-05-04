################################################################################
#
#  NfOrderRoundTwo.jl : Primitive implementation of Round 2
#
################################################################################

# TODO:
# - 
export pradical, pmaximal_overorder, MaximalOrder

function pradical(O::NfOrder, p::fmpz)
  j = clog(ZZ(degree(O)),p)
  R = ResidueRing(ZZ,p) # hashing doesn't work
  A = MatrixSpace(R, degree(O), degree(O))()
  for i in 1:degree(O)
    t = powermod(basis(O)[i], p^j, p)
    #print("basis elemt", i, "to the power", p^j, "modulo ", p)
    #println(t)
    ar = elem_in_basis(t)
    for j in 1:degree(O)
      A[i,j] = ar[j]
    end
  end
  #println(A)
  X = kernel(A)
  Mat = MatrixSpace(ZZ, 1, degree(O))
  MMat = MatrixSpace(R, 1, degree(O))
  if length(X) != 0
    #println(parent(X[1][1]) == base_ring(MMat))
    m = lift(MMat(X[1]))
    for x in 2:length(X)
      m = vcat(m,lift(MMat(X[x])))
    end
    m = vcat(m,MatrixSpace(ZZ, degree(O), degree(O))(p))
  else
    m = MatrixSpace(ZZ, degree(O), degree(O))(p)
  end
  #println(m)
  return ideal(O,sub(hnf(m), 1:degree(O), 1:degree(O)))
end

function pmaximal_overorder(O::NfOrder, p::fmpz)
  d = discriminant(O)
  OO = NfOrder(colon_ideal(pradical(O,p)))
  dd = discriminant(OO)
  while d != dd
    d = dd
    OO = NfOrder(colon_ideal(pradical(OO,p)))
    dd = discriminant(OO)
  end
  OO.basis_mat.num = hnf(OO.basis_mat.num)
  return OO
end

function MaximalOrder(O::NfOrder)
  fac = factor(abs(discriminant(O)))
  for i in 1:fac.len
    (p,j) = fac[i]
    if j == 1
      continue
    end
    O += pmaximal_overorder(O, ZZ(p))
  end
  return O
end
