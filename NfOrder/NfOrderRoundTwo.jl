export pradical

function pradical(O::NfOrder, p::fmpz)
  j = clog(ZZ(degree(O)),p)
  R = ResidueRing(ZZ,p) # hashing doesn't work
  A = MatrixSpace(R, degree(O), degree(O))()
  for i in 1:degree(O)
    t = powermod(basis(O)[i], p^j, p)
    print("basis elemt", i, "to the power", p^j, "modulo ", p)
    println(t)
    ar = elem_in_basis(t)
    for j in 1:degree(O)
      A[i,j] = ar[j]
    end
  end
  println(A)
  X = kernel(A)
  Mat = MatrixSpace(ZZ, 1, degree(O))
  MMat = MatrixSpace(R, 1, degree(O))
  if length(X) != 0
    println(parent(X[1][1]) == base_ring(MMat))
    m = lift(MMat(X[1]))
    for x in 2:length(X)
      m = vcat(m,lift(MMat(X[x])))
    end
    m = vcat(m,MatrixSpace(ZZ, degree(O), degree(O))(p))
  else
    m = MatrixSpace(ZZ, degree(O), degree(O))(p)
  end
  println(m)
  return ideal(O,sub(hnf(m), 1:degree(O), 1:degree(O)))
end


