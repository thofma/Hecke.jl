################################################################################
#
#  NfOrderRoundTwo.jl : Primitive implementation of Round 2
#
################################################################################

export pradical, pmaximal_overorder, MaximalOrder

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
  @vprint :NfOrder 1 "computing p-maximal overorder for $p ... \n"
  if rem(discriminant(O), p) != 0
    return O
  end

  d = discriminant(O)
  @vprint :NfOrder 1 "extending the order at $p for the first time ... \n"
  OO = poverorder(O, p)
  dd = discriminant(OO)
  i = 1
  while d != dd
    i += 1
    @vprint :NfOrder 1 "extending the order at $p for the $(i)th time ... \n"
    d = dd
    OO = poverorder(OO, p)
    dd = discriminant(OO)
  end
  return OO
end

function pmaximal_overorder(O::NfOrder, p::Integer)
  return pmaximal_overorder(O, ZZ(p))
end

function _MaximalOrder(O::NfOrder, primes::Array{fmpz, 1})
  OO = deepcopy(O)
  disc = abs(discriminant(O))
  for i in 1:length(primes)
    p = primes[i]
    (j, disc) = valuation(disc, p)
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

function _MaximalOrder(O::NfOrder)
  OO = deepcopy(O)
  @vtime :NfOrder fac = factor(Nemo.abs(discriminant(O)))
  for (p,j) in fac
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
