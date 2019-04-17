

function MaximalOrder(K::NfAbsNS; discriminant::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[])
  try
    c = _get_maximal_order(K)::NfAbsOrd{NfAbsNS, NfAbsNSElem}
    return c
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
    O = maximal_order_from_components(K)
    O.ismaximal = 1
    _set_maximal_order(K, O)
    return O
  end
end



###############################################################################
#
#  Generic code for orders
#
###############################################################################

function new_maximal_order(O::NfAbsOrd{S, T}; index_divisors::Vector{fmpz} = fmpz[], disc::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[]) where {S, T}
  return maximal_order_round_four(O, index_divisors= index_divisors, disc = disc, ramified_primes = ramified_primes)
end

function maximal_order_round_four(O::NfAbsOrd; index_divisors::Vector{fmpz} = fmpz[], disc::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[])
  OO = O
  M = trace_matrix(O)
  l = divisors(M, discriminant(O))
  if !isempty(index_divisors)
    push!(l, index_divisors)
  end
  if !isempty(ramified_primes)
    push!(l, ramified_primes)
  end
  l = coprime_base(l)
  for s in l
    if disc != -1
      u = divexact(discriminant(OO), disc)
      if isone(gcd(u, s))
        continue
      end
    end
    @vtime :NfOrd fac = factor(s)
    for (p, j) in fac
      @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
      O1 = pmaximal_overorder(O, p)
      if valuation(discriminant(O1), p) < valuation(discriminant(OO),p)
        OO += O1
      end 
      @vprint :NfOrd 1 "done\n"
    end
  end
  OO.ismaximal = 1
  return OO
end

function maximal_order_from_components(L::NfAbsNS; disc::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[])
  BKs, lp = maximal_order_of_components(L)
  B = product_basis(BKs)
  OO = Order(L, B, check = false, cached = false, isbasis = true)
  if disc != -1 && discriminant(OO) == disc
    return OO
  end
  if !isempty(ramified_primes)
    append!(lp, ramified_primes)
  end
  lp = coprime_base(lp)
  for p in lp
    if isprime(p)
      OO = pmaximal_overorder(OO, p)
    else
      fac = factor(p)
      for (k, v) in fac
        OO = pmaximal_overorder(OO, k)
      end
    end
  end
  OO.ismaximal = 1
  return OO

end


function product_basis(l::Vector{Vector{T}}) where T <: Union{NfAbsOrdElem, nf_elem, NfAbsNSElem}
  nelems = 1
  for i = 1:length(l)
    nelems *= length(l[i])
  end
  B = Vector{T}(undef, nelems)
  ind = length(l[1])
  for i = 1:ind
    B[i] = l[1][i]
  end
  for jj = 2:length(l)
    new_deg = length(l[jj])
    for i = 2:new_deg
      for j = 1:ind
        B[(i-1)* ind + j] = B[j] * l[jj][i]
      end
    end
    ind *= new_deg
  end
  return B
end

function product_basis(l1::Vector{T}, l2::Vector{T}) where T <: Union{NfAbsOrdElem, nf_elem, NfAbsNSElem}
  B = Vector{T}(undef, length(l1)*length(l2))
  for i = 1:length(l1)
    B[i] = l1[i]
  end
  for i = 1:length(l2)
    for j = 1:length(l1)
      B[(i-1)* length(l1) + j] = B[j] * l2[i]
    end
  end
  return B
end

function maximal_order_of_components(L::NfAbsNS) where {S, T}
  Qx, x = PolynomialRing(FlintQQ, "x")
  fields = Vector{AnticNumberField}(undef, length(L.pol))
  for i = 1:length(L.pol)
    f = Qx(L.pol[i])
    K = NumberField(f, cached = false)[1];
    OK = maximal_order(K)
    fields[i] = K
  end
  mvpolring = parent(L.pol[1])
  gpols = gens(mvpolring)
  #Now, bring the maximal order of every component in L
  B = Vector{Vector{NfAbsNSElem}}(undef, length(fields))
  for i = 1:length(fields)
    OK = maximal_order(fields[i])
    BOK = OK.basis_nf
    BK = Vector{NfAbsNSElem}(undef, degree(OK))
    for j = 1:length(BK)
      polel = Qx(BOK[j])
      polm = evaluate(polel, gpols[i])
      BK[j] = L(polm)
    end
    B[i] = BK
  end
  lp = fmpz[]
  for i = 1:length(fields)
    for j = i+1:length(fields)
      push!(lp, gcd(discriminant(maximal_order(fields[i])), discriminant(maximal_order(fields[j]))))
    end
  end
  return B, lp
end  
