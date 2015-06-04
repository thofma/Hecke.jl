################################################################################
#
#  NfOrderRoundTwo.jl : Primitive implementation of Round 2
#
################################################################################

export pradical, pmaximal_overorder, MaximalOrder

################################################################################
#
#  Compute the p-radical of an order
#
################################################################################

function pradical(O::NfOrder, p::fmpz)
  j = clog(ZZ(degree(O)),p)
  R = ResidueRing(ZZ,p)
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

function pradical(O::NfOrder, p::Integer)
  return pradical(O, ZZ(p))
end

################################################################################
#
#  Compute an overorder, which is larger at p (if possible)
#
################################################################################

function _poverorder(O::NfOrder, p::fmpz)
  OO = NfOrder(colon_ideal(pradical(O,p)))
  #OO.basis_mat = hnf(OO.basis_mat)
  return OO
end

function _poverorder(O::NfOrder, p::Integer)
  return _poverorder(O, ZZ(p))
end

function poverorder(O::NfOrder, p::fmpz)
  if isequationorder(O)
    return dedekind_poverorder(O, p)
  else
    return _poverorder(O, p)
  end
end

function poverorder(O::NfOrder, p::Integer)
  return poverorder(O::NfOrder, ZZ(p))
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

function pmaximal_overorder(O::NfOrder, p::fmpz)
  if rem(discriminant(O), p) != 0
    return O
  end

  d = discriminant(O)
  OO = poverorder(O, p)
  dd = discriminant(OO)
  while d != dd
    d = dd
    OO = poverorder(OO, p)
    dd = discriminant(OO)
  end
  return OO
end

function pmaximal_overorder(O::NfOrder, p::Integer)
  return pmaximal_overorder(O, ZZ(p))
end

function _MaximalOrder(O::NfOrder)
  OO = deepcopy(O)
  @vtime :NfOrder fac = factor(Nemo.abs(discriminant(O)))
  for i in 1:fac.len
    (p,j) = fac[i]
    if j == 1
      continue
    end
    @vprint :NfOrder 1 "Computing p-maximal overorder for $p ..."
    #println("Computing maximal ",p," overorder")
    OO += pmaximal_overorder(O, p)
    @vprint :NfOrder 1 "done\n"
  end
  return OO
end
