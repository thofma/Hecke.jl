
export maximal_order, poverorder, MaximalOrder, ring_of_integers

###############################################################################
#
#  Maximal Order interface
#
###############################################################################
@doc Markdown.doc"""
    MaximalOrder(O::NfAbsOrd; index_divisors::Vector{fmpz}, discriminant::fmpz, ramified_primes::Vector{fmpz}) -> NfAbsOrd

Returns the maximal order of the number field that contains $O$. Additional information can be supplied if they are already known, as the ramified primes,
the discriminant of the maximal order or a set of integers dividing the index of $O$ in the maximal order.
"""
function MaximalOrder(O::NfAbsOrd{S, T}; index_divisors::Vector{fmpz} = fmpz[], discriminant::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[]) where {S, T}
  K = nf(O)
  return get_attribute!(K, :maximal_order) do
    M = new_maximal_order(O, index_divisors = index_divisors, disc = discriminant, ramified_primes = ramified_primes)
    M.is_maximal = 1
    if M === O
      O.is_maximal = 1
      if isdefined(O, :lllO)
        O.lllO.is_maximal = 1
      end
    end
    return M
  end::NfAbsOrd{S, T}
end

@doc Markdown.doc"""
    MaximalOrder(K::NumField{fmpq}; discriminant::fmpz, ramified_primes::Vector{fmpz}) -> NfAbsOrd

Returns the maximal order of $K$. Additional information can be supplied if they are already known, as the ramified primes
or the discriminant of the maximal order.

# Example

```julia-repl
julia> Qx, x = FlintQQ["x"];
julia> K, a = NumberField(x^3 + 2, "a");
julia> O = MaximalOrder(K);
```
"""
function MaximalOrder(K::AnticNumberField; discriminant::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[])
  return get_attribute!(K, :maximal_order) do
    E = any_order(K)
    O = new_maximal_order(E, ramified_primes = ramified_primes)
    O.is_maximal = 1
    if E === O
      E.is_maximal == 1
      if isdefined(E, :lllO)
        E.lllO.is_maximal = 1
      end
    end
    return O
  end::NfAbsOrd{AnticNumberField, nf_elem}
end

@doc Markdown.doc"""
    ring_of_integers(K::AnticNumberField) -> NfAbsOrd

Returns the ring of integers of $K$.

See also `[`MaximalOrder`](@ref)`.
"""
function ring_of_integers(x::T; kw...) where T
  return maximal_order(x; kw...)
end


function maximal_order(f::T) where T <: Union{fmpz_poly, fmpq_poly}
  K = number_field(f, cached = false)[1]
  return maximal_order(K)
end

################################################################################
#
#  function to get an order which is maximal at some primes
#
################################################################################
@doc Markdown.doc"""
    pmaximal_overorder_at(O::NfOrd, primes::Vector{fmpz}) -> NfOrd

Given a set of prime numbers, this function returns an overorder of $O$ which
is maximal at those primes.
"""
function pmaximal_overorder_at(O::NfOrd, primes::Vector{fmpz})

  primes1 = setdiff(primes, O.primesofmaximality)
  if isempty(primes1)
    return O
  end
  OO = O

  if !is_defining_polynomial_nice(nf(O)) || !isinteger(gen_index(O))
    for i in 1:length(primes)
      p = primes[i]
      @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
      OO += pmaximal_overorder(OO, p)
      if !(p in OO.primesofmaximality)
        push!(OO.primesofmaximality, p)
      end
    end
    return OO
  end

  ind = index(O)
  K = nf(O)
  EO = EquationOrder(K)
  M = zero_matrix(FlintZZ, 2 * degree(O), degree(O))
  Zx = PolynomialRing(FlintZZ, "x", cached = false)[1]
  f = Zx(K.pol)
  for i in 1:length(primes1)
    p = primes1[i]
    @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
    if !divisible(ind, p) || is_regular_at(f, p)
      O1 = pmaximal_overorder(EO, p)
      if valuation(discriminant(O1), p) != valuation(discriminant(OO), p)
        OO = sum_as_Z_modules(OO, O1, M)
      end
    else
      #Instead of starting the computation with O, I create the maximal suborder of O of p-power index
      O1 = pmaximal_overorder(O, p)
      if discriminant(O1) != discriminant(O)
        OO = sum_as_Z_modules(OO, O1, M)
      end
    end
    if !(p in OO.primesofmaximality)
      push!(OO.primesofmaximality, p)
    end
    @vprint :NfOrd 1 "done\n"
  end
  @assert isdefined(OO, :disc)
  return OO
end

################################################################################
#
#  Buchmann Lenstra heuristic
#
################################################################################

#  Buchmann-Lenstra for simple absolute number fields.
function new_maximal_order(O::NfOrd; index_divisors::Vector{fmpz} = fmpz[], disc::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[])

  K = nf(O)
  if degree(K) == 1
    O.is_maximal = 1
    return O
  end

  if is_defining_polynomial_nice(K) && !contains_equation_order(O)
    #The order does not contain the equation order. We add them
    O = O + EquationOrder(K)
  end

  if is_defining_polynomial_nice(K) && (is_equation_order(O) || contains_equation_order(O))
    Zx, x = PolynomialRing(FlintZZ, "x", cached = false)
    f1 = Zx(K.pol)
    ds = gcd(rres(f1, derivative(f1)), discriminant(O))
    l = prefactorization(f1, ds)
  else
    ds = discriminant(O)
    #First, factorization of the discriminant given by the snf of the trace matrix
    M = trace_matrix(O)
    @vtime :NfOrd 1 l = divisors(M, ds)
  end

  @vprint :NfOrd 1 "Computing some factors of the discriminant\n"


  #No, factors of the discriminant appearing in the
  if !isempty(index_divisors)
    append!(l, index_divisors)
  end
  if !isempty(ramified_primes)
    append!(l, ramified_primes)
  end
  if disc != -1
    push!(l, disc)
  end
  l = coprime_base(l)
  @vprint :NfOrd 1 "Factors of the discriminant: $l\n "
  l1 = fmpz[]
  OO = O
  @vprint :NfOrd 1 "Trial division of the discriminant\n "
  auxmat = zero_matrix(FlintZZ, 2*degree(K), degree(K))
  first = true
  for d in l
    if disc != -1
      u = divexact(discriminant(OO), disc)
      if isone(gcd(u, d))
        continue
      end
    end
    fac = factor_trial_range(d)[1]
    rem = d
    for (p,v) in fac
      rem = divexact(rem, p^v)
    end
    pps = collect(keys(fac))
    @vprint :NfOrd 1 "Computing the maximal order at $(pps)\n "
    O1 = pmaximal_overorder_at(O, pps)
    if discriminant(O1) != discriminant(O)
      if first
        OO = O1
        first = false
      else
        @vtime :NfOrd 3 OO = sum_as_Z_modules(OO, O1, auxmat)
      end
    end
    rem = abs(rem)
    if !isone(rem)
      if disc != -1
        u = divexact(discriminant(OO), disc)
        if isone(gcd(u, rem))
          continue
        end
      end
      push!(l1, rem)
    end
  end
  if isempty(l1) || discriminant(OO) == disc
    OO.is_maximal = 1
    return OO
  end
  for i=1:length(l1)
    a, b = is_power(l1[i])
    if a>1
      if is_prime(b)
        O1 = pmaximal_overorder(O, b)
        OO = sum_as_Z_modules(OO, O1, auxmat)
        l1[i] = 0
      else
        l1[i]=b
      end
    end
  end
  ll1 = fmpz[x for x in l1 if !iszero(x)]
  if isempty(ll1)
    OO.is_maximal = 1
    return OO
  end
  O1, Q = _TameOverorderBL(OO, ll1)
  if !isempty(Q) && discriminant(O1) != disc
    @vprint :NfOrd 1 "I have to factor $Q\n "
    for el in Q
      d = factor(el).fac
      O2 = pmaximal_overorder_at(O, collect(keys(d)))
      O1 = sum_as_Z_modules(O1, O2, auxmat)
    end
  end
  O1.is_maximal = 1
  return O1

end

function _TameOverorderBL(O::NfOrd, lp::Vector{fmpz})

  K = nf(O)
  OO = O
  M = coprime_base(lp)
  Q = fmpz[]
  while !isempty(M)
    @vprint :NfOrd 1 "List of factors: $M\n"
    q = pop!(M)
    if is_coprime(q, discriminant(OO))
      continue
    end
    _, q = is_power(q)
    if is_prime(q)
      OO1 = pmaximal_overorder(O, q)
      if valuation(discriminant(OO1), q) < valuation(discriminant(OO), q)
        OO = sum_as_Z_modules(OO, OO1)
      end
    else
      if is_defining_polynomial_nice(nf(O)) && is_coprime(index(OO), q)
        q1, OOq = dedekind_test_composite(EquationOrder(K), q)
        if !isone(q1)
          push!(M, q1)
          push!(M, divexact(q, q1))
          M = coprime_base(M)
          continue
        end
        OO = sum_as_Z_modules(OO, OOq)
      end
      q = gcd(q, discriminant(OO))
      if isone(q)
        continue
      end
      OO, q1 = _cycleBL(OO, q)
      q1, q2 = ppio(q, q1)
      if q1 == q
        push!(Q, q)
      elseif !isone(q1)
        push!(M, q1)
        push!(M, q2)
        M = coprime_base(M)
      end
    end
  end
  if isempty(Q)
    OO.is_maximal = 1
  end
  return OO, Q
end

function _radical_by_poly(O::NfOrd, q::fmpz)
  d = degree(O)
  K = nf(O)
  R = ResidueRing(FlintZZ, q, cached=false)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  f = Rx(K.pol)
  f1 = derivative(f)
  fd, p1 = _gcd_with_failure(f, f1)
  if !isone(fd)
    return fd, ideal(O, q)
  end
  if isone(p1)
    return fmpz(1), ideal(O, q)
  end
  #p1 generates the same ideal as the derivative of f
  #to approximate its radical, we divide by the gcd with its derivative.
  fd, p2 = _gcd_with_failure(p1, derivative(p1))
  if !isone(fd)
    return fd, ideal(O, q)
  end
  Zx = PolynomialRing(FlintZZ, "x")[1]
  qq, rr = divrem(p1, p2)
  @assert iszero(rr)
  gen2 = O(K(lift(Zx, qq)))
  M1 = representation_matrix_mod(gen2, q)
  hnf_modular_eldiv!(M1, q, :lowerleft)
  for i = 1:d
    if !isone(M1[i, i])
      if M1[i, i] != q && !isone(gcd(M1[i, i], q))
        return M1[i, i], ideal(O, q)
      end
    end
  end
  I1 = ideal(O, q, gen2)
  I1.basis_matrix = M1
  I1.gens = NfOrdElem[O(q), gen2]
  return fmpz(1), I1
end

function _radical_by_trace(O::NfOrd, q::fmpz)
  d = degree(O)
  K = nf(O)
  R = ResidueRing(FlintZZ, q, cached=false)
  k, B = kernel(trace_matrix(O), R)
  M2 = zero_matrix(FlintZZ, d, d)
  for i = 1:k
    for j = 1:d
      na = lift(B[j, i])
      if q != na && !iszero(na) && !isone(gcd(na, q))
        return na, ideal(O, q)
      end
      M2[i, j] = na
    end
  end
  gens = elem_type(O)[O(q)]
  for i=1:k
    push!(gens, elem_from_mat_row(O, M2, i))
  end
  hnf_modular_eldiv!(M2, q, :lowerleft)
  for i = 1:d
    if M2[i, i] != q && !isone(gcd(M2[i, i], q))
      return M2[i, i], ideal(O, q)
    end
  end
  I = ideal(O, M2, false, true)
  I.minimum = q
  I.gens = gens
  return fmpz(1), I
end

function _qradical(O::NfOrd, q::fmpz)
  K = nf(O)
  @vprint :NfOrd 1 "\nradical computation\n "
  if is_defining_polynomial_nice(K) && isone(gcd(index(O), q))
    return _radical_by_poly(O, q)
  else
    return _radical_by_trace(O, q)
  end
end

function _cycleBL(O::NfOrd, q::fmpz)

  q1, I = _qradical(O, q)
  if !isone(q1)
    return O, q1
  elseif isdefined(I, :princ_gens) && q == I.princ_gens
    return O, fmpz(1)
  elseif I == ideal(O, q)
    return O, fmpz(1)
  end
  @vprint :NfOrd 1 "ring of multipliers\n"
  O1 = ring_of_multipliers(I)
  @vprint :NfOrd 1 "ring of multipliers computed\n"
  while discriminant(O1) != discriminant(O)
    if isone(gcd(discriminant(O1), q))
      return O1, fmpz(1)
    end
    O = O1
    q1, I = _qradical(O, q)
    if !isone(q1)
      return O, q1
    elseif isdefined(I, :princ_gens) && q == I.princ_gens
      return O, fmpz(1)
    end
    @vprint :NfOrd 1 "ring of multipliers\n"
    O1 = ring_of_multipliers(I)
  end
  @vprint :NfOrd 1 "The ring of multipliers was the ring itself\n"
  # (I:I)=OO. Now, we want to prove tameness (or get a factor of q)
  # We have to test that (OO:a)/B is a free Z/qZ module.
  #TODO: Check, I am doing something stupid here
  inva = colon(ideal(O, 1), I, true)
  M1 = basis_mat_inv(inva)
  @assert isone(M1.den)
  G1 = divisors(M1.num, q)
  for i = 1:length(G1)
    q1 = gcd(q, G1[i])
    if q1 != q && !isone(q1)
      @vprint :NfOrd 1 "Found the factor $q1"
      return O, q1
    end
  end
  @vprint :NfOrd 1 "(OO:I)/OO is free\n"
  res = _cycleBL2(O, q, I)
  return res

end

function _cycleBL2(O::NfOrd, q::fmpz, I::NfOrdIdl)

  h = 2
  ideals = Vector{NfOrdIdl}(undef, 3)
  ideals[1] = I
  ideals[2] = I*I
  ideals[3] = ideals[2] * I
  while true
    if h > degree(O)
      error("Not found!")
    end
    I1 = (ideals[1] + ideal(O, q))*(ideals[3] + ideal(O, q))
    I2 = (ideals[2] + ideal(O, q))^2
    if I1 != I2
      M2 = basis_matrix(I2, copy = false)*basis_mat_inv(I1, copy = false)
      @assert isone(M2.den)
      G2 = divisors(M2.num, q)
      for i = 1:length(G2)
        q1 = gcd(q, G2[i])
        if q1 != q && !isone(q1)
          return O, q1
        end
      end
      break
    else
      h += 1
      ideals[1] = ideals[2]
      ideals[2] = ideals[3]
      ideals[3] = ideals[2]*I
    end
  end
  f, r = is_power(q, h)
  if f
    return O, r
  else
    return O, q
  end
end



function TameOverorderBL(O::NfOrd, lp::Vector{fmpz}=fmpz[])

  # First, we hope that we can get a factorization of the discriminant by computing
  # the structure of the group OO^*/OO
  OO=O
  list = append!(elementary_divisors(trace_matrix(OO)), primes_up_to(degree(O)))
  l=coprime_base(list)
  #Some trivial things, maybe useless
  for i=1:length(l)
    a,b=is_power(l[i])
    if a>1
      l[i]=b
    end
    if is_prime(l[i])
      @vprint :NfOrd 1 "pmaximal order at $(l[i])\n"
      OO1=pmaximal_overorder(O, l[i])
      if valuation(discriminant(OO1), l[i])<valuation(discriminant(OO), l[i])
        OO+=OO1
      end
      l[i]=0
    end
  end
  push!(l, discriminant(OO))
  append!(l,lp)
  filter!(x-> !iszero(x), l)
  for i=1:length(l)
    l[i]=abs(l[i])
  end
  M=coprime_base(l)
  Q=fmpz[]
  while !isempty(M)
    @vprint :NfOrd 1 M
    q = M[1]
    if is_prime(q)
      OO1=pmaximal_overorder(O, q)
      if valuation(discriminant(OO1), q)< valuation(discriminant(OO), q)
        OO+=OO1
      end
      filter!(x-> x!=q, M)
      continue
    end
    OO, q1 = _cycleBL(OO,q)
    if isone(q1)
      filter!(x->x!=q, M)
    elseif q1 == q
      push!(Q, q)
      filter!(x-> x != q, M)
    else
      push!(M, q1)
      push!(M, divexact(q,q1))
      M = coprime_base(M)
    end
  end
  if isempty(Q)
    OO.is_maximal=1
  end
  return OO, Q

end

################################################################################
#
#  p-overorder
#
################################################################################

function _poverorder(O::NfAbsOrd, p::fmpz)
  @vtime :NfOrd 3 I = pradical1(O, p)
  if isdefined(I, :princ_gen) && I.princ_gen == p
    return O
  end
  @vtime :NfOrd 3 R = ring_of_multipliers(I)
  return R
end

@doc Markdown.doc"""
    poverorder(O::NfOrd, p::fmpz) -> NfOrd
    poverorder(O::NfOrd, p::Integer) -> NfOrd

This function tries to find an order that is locally larger than $\mathcal O$
at the prime $p$: If $p$ divides the index $[ \mathcal O_K : \mathcal O]$,
this function will return an order $R$ such that
$v_p([ \mathcal O_K : R]) < v_p([ \mathcal O_K : \mathcal O])$. Otherwise
$\mathcal O$ is returned.
"""
function poverorder(O::NfAbsOrd, p::fmpz)
  if p in O.primesofmaximality
    return O
  end
  if is_equation_order(O) && is_defining_polynomial_nice(nf(O)) && is_simple(nf(O))
    #return dedekind_poverorder(O, p)
    return polygons_overorder(O, p)
  else
    return _poverorder(O, p)
  end
end

function poverorder(O::NfAbsOrd, p::Integer)
  return poverorder(O, fmpz(p))
end

################################################################################
#
#  p-maximal overorder
#
################################################################################

@doc Markdown.doc"""
    pmaximal_overorder(O::NfOrd, p::fmpz) -> NfOrd
    pmaximal_overorder(O::NfOrd, p::Integer) -> NfOrd

This function finds a $p$-maximal order $R$ containing $\mathcal O$. That is,
the index $[ \mathcal O_K : R]$ is not divisible by $p$.
"""
function pmaximal_overorder(O::NfAbsOrd, p::fmpz)
  @vprint :NfOrd 1 "computing p-maximal overorder for $p ... \n"
  if p in O.primesofmaximality
    return O
  end
  d = discriminant(O)
  if !iszero(rem(d, p^2))
    push!(O.primesofmaximality, p)
    return O
  end
  @vprint :NfOrd 1 "extending the order at $p for the first time ... \n"
  i = 1
  OO = poverorder(O, p)
  dd = discriminant(OO)
  while d != dd
    if !iszero(rem(dd, p^2))
      break
    end
    i += 1
    @vprint :NfOrd 1 "extending the order at $p for the $(i)th time ... \n"
    d = dd
    OO = poverorder(OO, p)
    dd = discriminant(OO)
  end
  push!(OO.primesofmaximality, p)
  return OO
end

function pmaximal_overorder(O::NfAbsOrd, p::Integer)
  return pmaximal_overorder(O, fmpz(p))
end

################################################################################
#
#  Ring of multipliers
#
################################################################################
@doc Markdown.doc"""
    ring_of_multipliers(I::NfAbsOrdIdl) -> NfAbsOrd

Computes the order $(I : I)$, which is the set of all $x \in K$
with $xI \subseteq I$.
"""
function ring_of_multipliers(a::NfAbsOrdIdl)
  O = order(a)
  n = degree(O)
  bmatinv = basis_mat_inv(a, copy = false)
  if isdefined(a, :gens) && length(a.gens) < n
    B = vcat(elem_type(O)[O(minimum(a))], a.gens)
  else
    B = basis(a, copy = false)
  end
  @assert length(B) > 0
  id_gen = zero_matrix(FlintZZ, 2*n, n)
  m = zero_matrix(FlintZZ, n*length(B), n)
  ind = 1
  modu = minimum(a, copy = false)*bmatinv.den
  for i = 1:length(B)
    if i != 1
      c = matrix(FlintZZ, 1, n, coordinates(B[i]))
      reduce_mod_hnf_ll!(c, id_gen)
      if iszero(c)
        continue
      end
    end
    M = representation_matrix_mod(B[i], modu)
    _copy_matrix_into_matrix(id_gen, 1, 1, M)
    hnf_modular_eldiv!(id_gen, minimum(a, copy = false), :lowerleft)
    mod!(M, minimum(a, copy = false)*bmatinv.den)
    mul!(M, M, bmatinv.num)
    transpose!(M, M)
    _copy_matrix_into_matrix(m, n*(ind-1)+1, 1, M)
    if view(id_gen, n+1:2*n, 1:n) == basis_matrix(a, copy = false)
      m = view(m, 1:n*ind, 1:n)
      break
    end
    ind += 1
  end
  if !isone(bmatinv.den)
    divexact!(m, m, bmatinv.den)
  end
  hnf_modular_eldiv!(m, minimum(a, copy = false))
  mhnf = view(m, 1:n, 1:n)
  s = prod_diagonal(mhnf)
  if isone(s)
    return O
  end
  # mhnf is upper right HNF
  transpose!(mhnf, mhnf)
  b = FakeFmpqMat(pseudo_inv(mhnf))
  mul!(b, b, basis_matrix(O, copy = false))
  @hassert :NfOrd 1 defines_order(nf(O), b)[1]
  O1 = NfAbsOrd(nf(O), b)
  if isdefined(O, :disc)
    O1.disc = divexact(O.disc, s^2)
  end
  if isdefined(O, :index)
    O1.index = s*O.index
    O1.gen_index = fmpq(O1.index)
  end
  if isdefined(O, :basis_mat_inv)
    O1.basis_mat_inv = O.basis_mat_inv * mhnf
  end
  O1.primesofmaximality = fmpz[ppp for ppp in O.primesofmaximality]
  return O1
end

################################################################################
#
#  radical for maximal order
#
################################################################################

@doc Markdown.doc"""
    factor_shape_refined(f::gfp_poly)

Given a polynomial $f$ over a finite field, it returns an array having one
entry for every irreducible factor giving its degree and its multiplicity.
"""
function factor_shape_refined(x::gfp_poly) where {T <: RingElem}
  res = Tuple{Int, Int}[]
  square_fac = factor_squarefree(x)
  for (f, i) in square_fac
    discdeg = factor_distinct_deg(f)
    for (j, g) in discdeg
      num = divexact(degree(g), j)
      for l = 1:num
        push!(res, (j, i))
      end
    end
  end
  return res
end

function new_pradical_frobenius1(O::NfOrd, p::Int)
  R = GF(p, cached = false)
  d = degree(O)
  K = nf(O)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  res = factor_shape_refined(Rx(K.pol))
  md = 1
  for i = 1:length(res)
    md = max(md, res[i][2])
  end
  j = clog(fmpz(md), p)
  sqf = factor_squarefree(Rx(K.pol))
  p1 = one(Rx)
  for (x, v) in sqf
    if v > 1
      p1 = mul!(p1, p1, x)
    end
  end
  gen2 = O(lift(K, p1))
  M1 = representation_matrix_mod(gen2, fmpz(p))
  hnf_modular_eldiv!(M1, fmpz(p), :lowerleft)
  powers = Dict{Int, Vector{fmpz}}()
  gens = NfOrdElem[O(p), gen2]
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
    new_gens = Vector{NfOrdElem}()
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

function pradical_frobenius1(O::NfOrd, p::Int)
  R = GF(p, cached = false)
  d = degree(O)
  K = nf(O)
  Rx = PolynomialRing(R, "x", cached = false)[1]
  res = factor_shape_refined(Rx(K.pol))
  md = 1
  for i = 1:length(res)
    md = max(md, res[i][2])
  end
  j = clog(fmpz(md), p)
  sqf = factor_squarefree(Rx(K.pol))
  p1 = one(Rx)
  for (x, v) in sqf
    if v > 1
      p1 = mul!(p1, p1, x)
    end
  end
  gen2 = O(lift(K, p1))
  M1 = representation_matrix_mod(gen2, fmpz(p))
  hnf_modular_eldiv!(M1, fmpz(p), :lowerleft)
  nr = 0
  indices = Int[]
  for i = 1:d
    if !isone(M1[i, i])
      push!(indices, i)
      nr += 1
    end
  end
  A = zero_matrix(R, d, nr + d)
  B = basis(O, copy = false)
  ind = 0
  for i in 1:d
    if !(i in indices)
      continue
    end
    t = powermod(B[i], p^j, p)
    ind += 1
    if iszero(t)
      continue
    end
    ar = coordinates(t, copy = false)
    for k in 1:d
      A[k, ind] = ar[k]
    end
  end
  for s = 1:d
    for i = 1:s
      A[i, s+nr] = R(M1[s, i])
    end
  end
  X = right_kernel_basis(A)
  gens = elem_type(O)[O(p), gen2]
  if isempty(X)
    I = ideal(O, p, gen2)
    I.gens = gens
    return I
  end
  #First, find the generators
  for i = 1:length(X)
    coords = zeros(FlintZZ, d)
    for j=1:nr
      coords[indices[j]] = lift(X[i][j])
    end
    if !iszero(coords)
      push!(gens, O(coords))
    end
  end
  #Then, construct the basis matrix of the ideal
  m1 = zero_matrix(FlintZZ, length(gens) - 2 + d, d)
  for i = 3:length(gens)
    el = coordinates(gens[i], copy = false)
    for j = 1:nr
      m1[i-2, indices[j]] = el[indices[j]]
    end
  end
  for i = 1:d
    for s = 1:i
      m1[i+length(gens)-2, s] = M1[i, s]
    end
  end
  hnf_modular_eldiv!(m1, fmpz(p), :lowerleft)
  m1 = view(m1, length(gens) - 1:nrows(m1), 1:d)
  I = NfAbsOrdIdl(O, m1)
  I.minimum = p
  I.gens = gens
  return I
end

function pradical_trace1(O::NfOrd, p::IntegerUnion)
  if isone(gcd(discriminant(O), p))
    return ideal(O, p)
  end
  d = degree(O)
  M = trace_matrix(O)
  K = nf(O)
  F = GF(p, cached = false)
  Fx = PolynomialRing(F, "x", cached = false)[1]
  sqf = factor_squarefree(Fx(K.pol))
  p1 = one(Fx)
  for (x, v) in sqf
    if v > 1
      p1 = mul!(p1, p1, x)
    end
  end
  gen2 = O(lift(K, p1))
  M1 = representation_matrix_mod(gen2, fmpz(p))
  hnf_modular_eldiv!(M1, fmpz(p), :lowerleft)
  I1 = ideal(O, p, gen2)
  I1.basis_matrix = M1
  k, B = kernel(M, F)
  if iszero(k)
    return ideal(O, p)
  end

  gens = NfOrdElem[O(p), gen2]
  for i = 1:k
    coords = Vector{fmpz}(undef, d)
    for j = 1:d
      coords[j] = lift(B[j, i])
    end
    c = matrix(FlintZZ, 1, d, coords)
    reduce_mod_hnf_ll!(c, M1)
    if !iszero(c)
      push!(gens, O(coords))
    end
  end
  M2 = zero_matrix(FlintZZ, length(gens) -2 + d, d)
  for i = 3:length(gens)
    c = coordinates(gens[i], copy = false)
    for j = 1:d
      M2[i-2, j] = c[j]
    end
  end
  for i = 1:d
    for j = 1:i
      M2[i+length(gens)-2, j] = M1[i, j]
    end
  end
  hnf_modular_eldiv!(M2, fmpz(p), :lowerleft)
  M2 = view(M2, nrows(M2)-d+1:nrows(M2), 1:d)
  I = ideal(O, M2, false, true)
  I.minimum = p
  I.gens = gens
  return I
end


function pradical1(O::NfAbsOrd, p::IntegerUnion)
  if p isa fmpz && fits(Int, p)
    return pradical1(O, Int(p))
  end
  d = degree(O)

  if !is_defining_polynomial_nice(nf(O)) || !contains_equation_order(O)
    return pradical(O, p)
  end

  #Trace method if the prime is large enough
  if p > d
    return pradical_trace1(O, p)
  else
    res1 = new_pradical_frobenius1(O, Int(p))
    @hassert :NfOrd 1 !is_simple(nf(O)) || res1 == pradical_frobenius1(O, p)
    return res1
  end
end

################################################################################
#
#  Prefactorization of the discriminant
#
################################################################################

function prefactorization(f::fmpz_poly, d::fmpz, f1::fmpz_poly = derivative(f))
  if isone(d)
    return fmpz[]
  end
  factors = fmpz[d]
  final_factors = fmpz[]
  while !isempty(factors)
    d1 = pop!(factors)
    d1 = is_power(d1)[2]
    if isone(d1) || iszero(d1)
      continue
    end

    R = ResidueRing(FlintZZ, d1, cached = false)
    Rx = PolynomialRing(R, "x", cached = false)[1]
    ff = Rx(f)
    ff1 = Rx(f1)
    fd = _gcd_with_failure(ff, ff1)[1]
    fdl = gcd(fd, d1)
    if !isone(fd) && d1 != fdl
      d2, d3 = ppio(d1, fdl)
      push!(factors, fdl)
      if !isone(d2) && d1 != d2
        push!(factors, d2)
      end
      if !isone(d3)
        push!(factors, d3)
      end
    else
      push!(final_factors, d1)
    end
    if length(factors) > 2
      factors = coprime_base(factors)
    end
  end
  cb = coprime_base(final_factors)
  return cb
end

function _squarefree_decomposition(f::fmpz_mod_poly)
  D = Dict{Int, fmpz_mod_poly}()
  fail, d = Hecke._gcd_with_failure(f, derivative(f))
  if !isone(fail)
    return fail, D
  end
  g = divexact(f, d)
  f1 = deepcopy(f)
  j = 1
  m = modulus(base_ring(f))
  while !isone(f1)
    f1 = divexact(f1, g)
    fail, h = Hecke._gcd_with_failure(f1, g)
    @show fail
    @show fail = gcd(fail, m)
    if !isone(fail)
      return fail, D
    end
    t = divexact(g, h)
    if !isone(t)
      D[j] = t
    end
    g = h
    j += 1
  end
  return fail, D
end


function _gcd_with_failure(a::fmpz_mod_poly, b::fmpz_mod_poly)
  f = fmpz()
  G = parent(a)()
  ccall((:fmpz_mod_poly_gcd_euclidean_f, libflint), Nothing,
        (Ref{fmpz}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_poly}, Ref{fmpz_mod_ctx_struct}), f, G, a, b, a.parent.base_ring.ninv)
  return f, G
end
