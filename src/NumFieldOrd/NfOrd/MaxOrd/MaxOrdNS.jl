function MaximalOrder(K::NfAbsNS; discriminant::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[])
  return get_attribute!(K, :maximal_order) do
    O = maximal_order_from_components(K)
    O.is_maximal = 1
    return O
  end::NfAbsOrd{NfAbsNS, NfAbsNSElem}
end



###############################################################################
#
#  Generic code for orders
#
###############################################################################

function new_maximal_order(O::NfAbsOrd{<:NumField{fmpq}, <:NumFieldElem{fmpq}}; index_divisors::Vector{fmpz} = fmpz[], disc::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[]) where {S, T}
  return maximal_order_round_four(O, index_divisors = index_divisors, disc = disc, ramified_primes = ramified_primes)
end

function maximal_order_round_four(O::NfAbsOrd{<:NumField{fmpq}, <:NumFieldElem{fmpq}}; index_divisors::Vector{fmpz} = fmpz[], disc::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[])
  return _maximal_order_round_four(O; index_divisors = index_divisors, disc = disc, ramified_primes = ramified_primes)
end

function _maximal_order_round_four(O::NfAbsOrd{<:NumField{fmpq}, <:NumFieldElem{fmpq}}; index_divisors::Vector{fmpz} = fmpz[], disc::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[])
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
  OO.is_maximal = 1
  return OO
end


function maximal_order_from_components(L::NfAbsNS; disc::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[])
  BKs, lp, disc_order = _maximal_order_of_components(L)
  B = _product_basis(BKs)
  OO = Order(L, B, check = false, cached = false, isbasis = true)
  OO.disc = disc_order
  if disc != -1 && discriminant(OO) == disc
    OO.is_maximal = 1
    return OO
  end
  if ngens(L) == 1
    OO.is_maximal = 1
    return OO
  end
  if !isempty(ramified_primes)
    append!(lp, ramified_primes)
  end
  lp = coprime_base(lp)
  for p in lp
    if is_prime(p)
      OO = pmaximal_overorder(OO, p)
    else
      fac = factor(p)
      for (k, v) in fac
        OO = pmaximal_overorder(OO, k)
      end
    end
  end
  OO.is_maximal = 1
  return OO
end

function _product_basis(l::Vector{Vector{NfAbsNSElem}})
  nelems = 1
  for i = 1:length(l)
    nelems *= length(l[i])
  end
  K = parent(l[1][1])
  B = typeof(l[1])(undef, nelems)
  ind = length(l[1])
  for i = 1:ind
    B[i] = l[1][i]
  end
  for jj = 2:length(l)
    new_deg = length(l[jj])
    for i = 2:new_deg
      for j = 1:ind
        B[(i-1)* ind + j] = K(B[j].data * l[jj][i].data, false)
      end
    end
    ind *= new_deg
  end
  return B
end

function product_basis(l::Vector{Vector{T}}) where T <: Union{NfAbsOrdElem, NfRelOrdElem, NumFieldElem}
  nelems = 1
  for i = 1:length(l)
    nelems *= length(l[i])
  end
  B = typeof(l[1])(undef, nelems)
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

function product_basis(l1::Vector{T}, l2::Vector{T}) where T <: Union{NfAbsOrdElem, NfRelOrdElem, NumFieldElem}
  B = Vector{typeof(l1[1])}(undef, length(l1)*length(l2))
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

function _maximal_order_of_components(L::NfAbsNS) where {S, T}
  Qx, x = PolynomialRing(FlintQQ, "x")
  fields = Vector{Tuple{AnticNumberField, NfAbsToNfAbsNS}}(undef, length(L.pol))
  for i = 1:length(L.pol)
    fields[i] = component(L, i)
  end
  #Now, bring the maximal order of every component in L
  B = Vector{Vector{NfAbsNSElem}}(undef, length(fields))
  d = fmpz(1)
  for i = 1:length(fields)
    OK = maximal_order(fields[i][1])
    d *= discriminant(OK)^(divexact(degree(L), degree(OK)))
    BOK = basis(OK, fields[i][1])
    BK = Vector{NfAbsNSElem}(undef, degree(OK))
    for j = 1:length(BK)
      BK[j] = fields[i][2](BOK[j])
    end
    B[i] = BK
  end
  lp = fmpz[]
  for i = 1:length(fields)
    for j = i+1:length(fields)
      push!(lp, gcd(discriminant(maximal_order(fields[i][1])), discriminant(maximal_order(fields[j][1]))))
    end
  end
  return B, lp, d
end

function pradical_trace1(O::NfAbsOrd{NfAbsNS, NfAbsNSElem}, p::Union{Int, fmpz})
  return pradical_trace(O, p)
end

function new_pradical_frobenius1(O::NfAbsOrd{NfAbsNS, NfAbsNSElem}, p::Int)
  R = GF(p, cached = false)
  d = degree(O)
  K = nf(O)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  Zx = PolynomialRing(FlintZZ, "x")[1]
  j = clog(fmpz(d), p)
  els_in_pradical = elem_type(O)[]
  M1 = zero_matrix(FlintZZ, 2*d, d)
  gens = elem_type(O)[O(p)]
  for i = 1:ngens(K)
    g = to_univariate(Globals.Qx, K.pol[i])
    sqf = factor_squarefree(Rx(g))
    p1 = one(Rx)
    for (x, v) in sqf
      if v > 1
        p1 = mul!(p1, p1, x)
      end
    end
    pol = lift(Zx, p1)
    elK = O(evaluate(pol, K[i]))
    push!(gens, elK)
    Mi = representation_matrix_mod(elK, fmpz(p))
    _copy_matrix_into_matrix(M1, 1, 1, Mi)
    hnf_modular_eldiv!(M1, fmpz(p), :lowerleft)
  end
  powers = Dict{Int, Vector{fmpz}}()
  B = basis(O, copy = false)
  it = 0
  while true
    if it == j
      I = ideal(O, M1, false, true)
      reverse!(gens)
      I.gens = gens
      I.minimum = fmpz(p)
      return I
    end
    it += 1
    indices = Int[]
    for i = 1:d
      if !isone(M1[i, i])
        push!(indices, i)
      end
    end
    nr = length(indices)
    A = zero_matrix(R, d, nr + d)
    ind = 0
    for i in 1:d
      if !(i in indices)
        continue
      end
      ind += 1
      if haskey(powers, i)
        ar = copy(powers[i])
        for k in 1:d
          A[k, ind] = ar[k]
        end
      else
        t = powermod(B[i], p, p)
        ar = coordinates(t, copy = true)
        powers[i] = copy(ar)
        if iszero(t)
          continue
        end
        for k in 1:d
          A[k, ind] = R(ar[k])
        end
      end
    end
    for s = 1:d
      for i = 1:s
        A[i, s+nr] = R(M1[s, i])
      end
    end
    X = right_kernel_basis(A)
    if isempty(X)
      I = ideal(O, M1, false, true)
      reverse!(gens)
      I.gens = gens
      I.minimum = fmpz(p)
      return I
    end
    #First, find the generators
    new_gens = Vector{elem_type(O)}()
    for i = 1:length(X)
      coords = zeros(FlintZZ, d)
      for j=1:nr
        coords[indices[j]] = lift(X[i][j])
      end
      if !iszero(coords)
        new_el = O(coords)
        push!(new_gens, new_el)
      end
    end
    if iszero(length(new_gens))
      I = ideal(O, M1, false, true)
      reverse!(gens)
      I.gens = gens
      I.minimum = fmpz(p)
      return I
    end
    #Then, construct the basis matrix of the ideal
    m1 = zero_matrix(FlintZZ, length(new_gens) + d, d)
    for i = 1:length(new_gens)
      el = coordinates(new_gens[i], copy = true)
      for j = 1:nr
        m1[i, indices[j]] = el[indices[j]]
      end
    end
    for i = 1:d
      for s = 1:i
        m1[i+length(new_gens), s] = M1[i, s]
      end
    end
    hnf_modular_eldiv!(m1, fmpz(p), :lowerleft)
    M1 = sub(m1, length(new_gens)+1:nrows(m1), 1:d)
    append!(gens, new_gens)
  end
end
