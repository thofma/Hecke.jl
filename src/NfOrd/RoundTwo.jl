################################################################################
#
#  NfOrdRoundTwo.jl : Primitive implementation of Round 2
#
################################################################################

export pradical, pmaximal_overorder, MaximalOrder

################################################################################
#
#  Compute an overorder, which is larger at p (if possible)
#
################################################################################

function _poverorder(O::NfOrd, p::fmpz)
  #OO = NfOrdGen(colon_ideal(pradical(O, p)))
  OO = ring_of_multipliers(pradical(O, p))
  #OO.basis_mat = hnf(OO.basis_mat)
  return OO
end

function _poverorder(O::NfOrd, p::Integer)
  return _poverorder(O, ZZ(p))
end

function poverorder(O::NfOrd, p::fmpz)
  if isequationorder(O)
    return dedekind_poverorder(O, p)
  else
    return _poverorder(O, p)
  end
end

function poverorder(O::NfOrd, p::Integer)
  return poverorder(O::NfOrd, ZZ(p))
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

function pmaximal_overorder(O::NfOrd, p::fmpz)
  @vprint :NfOrd 1 "computing p-maximal overorder for $p ... \n"
  if rem(discriminant(O), p) != 0
    return O
  end

  d = discriminant(O)
  @vprint :NfOrd 1 "extending the order at $p for the first time ... \n"
  OO = poverorder(O, p)
  dd = discriminant(OO)
  i = 1
  while d != dd
    i += 1
    @vprint :NfOrd 1 "extending the order at $p for the $(i)th time ... \n"
    d = dd
    OO = poverorder(OO, p)
    dd = discriminant(OO)
  end
  return OO
end

function pmaximal_overorder(O::NfOrd, p::Integer)
  return pmaximal_overorder(O, ZZ(p))
end

function _MaximalOrder(O::NfOrd, primes::Array{fmpz, 1})
  OO = deepcopy(O)
  disc = abs(discriminant(O))
  for i in 1:length(primes)
    p = primes[i]
    (j, disc) = valuation(disc, p)
    if j == 1
      continue
    end
    @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
    OO += pmaximal_overorder(O, p)
    @vprint :NfOrd 1 "done\n"
  end
  return OO
end

function _MaximalOrder(O::NfOrd)
  OO = deepcopy(O)
  @vtime :NfOrd fac = factor(Nemo.abs(discriminant(O)))
  for (p,j) in fac
    if j == 1
      continue
    end
    @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
    OO += pmaximal_overorder(O, p)
    @vprint :NfOrd 1 "done\n"
  end
  return OO
end
