
export maximal_order, pmaximal_order,poverorder, MaximalOrder, ring_of_integers


###############################################################################
#
#  Maximal Order interface
#
###############################################################################
@doc Markdown.doc"""
    maximal_order(O::NfAbsOrd; index_divisors::Vector{fmpz}, discriminant::fmpz, ramified_primes::Vector{fmpz}) -> NfAbsOrd

> Returns the maximal order of the number field that contains $O$. Additional information can be supplied if they are already known, as the ramified primes,
> the discriminant of the maximal order or a set of integers dividing the index of $O$ in the maximal order.
"""
function MaximalOrder(O::NfAbsOrd{S, T}; index_divisors::Vector{fmpz} = fmpz[], discriminant::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[]) where {S, T}
  K = nf(O)
  try
    # First check if the number field knows its maximal order
    M = _get_maximal_order(K)::typeof(O)
    return M
  catch e
    if !isa(e, AccessorNotSetError) 
      rethrow(e)
    end
    M = new_maximal_order(O, index_divisors = index_divisors, disc = discriminant, ramified_primes = ramified_primes)
    M.ismaximal = 1
    _set_maximal_order(K, M)
    return M
  end
end

@doc Markdown.doc"""
    maximal_order(K::Union{AnticNumberField, NfAbsNS}; discriminant::fmpz, ramified_primes::Vector{fmpz}) -> NfAbsOrd

> Returns the maximal order of $K$. Additional information can be supplied if they are already known, as the ramified primes
> or the discriminant of the maximal order.  

# Example

```julia-repl
julia> Qx, xx = FlintQQ["x"];
julia> K, a = NumberField(x^3 + 2, "a");
julia> O = MaximalOrder(K);
```
"""
function MaximalOrder(K::T; discriminant::fmpz = fmpz(-1), ramified_primes::Vector{fmpz} = fmpz[]) where T <: Union{AnticNumberField, NfAbsNS}
  try
    c = _get_maximal_order(K)::NfAbsOrd{T, elem_type(T)}
    return c
  catch e
    if !isa(e, AccessorNotSetError)
      rethrow(e)
    end
    #O = MaximalOrder(K)::NfOrd
    O = new_maximal_order(any_order(K))
    O.ismaximal = 1
    _set_maximal_order(K, O)
    return O
  end
end

@doc Markdown.doc"""
***
    ring_of_integers(K::AnticNumberField) -> NfAbsOrd

> This function returns the ring of integers of $K$.
"""
function ring_of_integers(x::T; kw...) where T
  return maximal_order(x; kw...)
end


function maximal_order(f::T) where T <: Union{fmpz_poly, fmpq_poly}
  K = number_field(f, cached = false)[1]
  return maximal_order(K)
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
  OO = deepcopy(O)
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

################################################################################
#
#  function to get an order which is maximal at some primes
#
################################################################################
@doc Markdown.doc"""
***
    pmaximal_overorder_at(O::NfOrd, primes::Array{fmpz, 1}) - > NfOrd

> Given a set of prime numbers, this function returns an overorder of $O$ which
> is maximal at those primes.
"""
function pmaximal_overorder_at(O::NfOrd, primes::Array{fmpz, 1})
  if length(primes) == 0
    return O
  end

  OO = O

  if !isdefining_polynomial_nice(nf(O)) || !isinteger(gen_index(O))
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
  EO = EquationOrder(nf(O))
  for i in 1:length(primes)
    p = primes[i]
    @vprint :NfOrd 1 "Computing p-maximal overorder for $p ..."
    if divisible(ind, p)
      OO = pmaximal_overorder(OO, p)
    else
      O1 = pmaximal_overorder(EO, p)
      if divisible(index(O1), p)
        OO += O1
      end
    end
    if !(p in OO.primesofmaximality)
      push!(OO.primesofmaximality, p)
    end
    @vprint :NfOrd 1 "done\n"
  end
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
    O.ismaximal = 1
    return O  
  end

  if isdefining_polynomial_nice(K) && (isequation_order(O) || isinteger(gen_index(O)))
    Zx, x = PolynomialRing(FlintZZ, "x", cached = false)
    f1 = Zx(K.pol)
    ds = rres(f1, derivative(f1))
  else
    ds = discriminant(O)
  end

  #First, factorization of the discriminant given by the snf of the trace matrix
  M = trace_matrix(O)
  l = divisors(M, ds)
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
    @vprint :NfOrd 1 "Computing the maximal order at $(collect(keys(fac)))\n "
    O1 = pmaximal_overorder_at(O, collect(keys(fac)))
    OO += O1
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
    OO.ismaximal = 1
    return OO
  end
  for i=1:length(l1)
    a, b = ispower(l1[i])
    if a>1
      l1[i]=b
    end
  end
  O1, Q = _TameOverorderBL(OO, l1)
  if !isempty(Q) && discriminant(O1) != disc
    @vprint :NfOrd 1 "I have to factor $Q\n "
    for el in Q
      d = factor(el).fac
      O1 += pmaximal_overorder_at(O1, collect(keys(d)))
    end
  end
  O1.ismaximal = 1
  return O1
  
end

function _TameOverorderBL(O::NfOrd, lp::Array{fmpz,1})
  
  OO = O
  M = coprime_base(lp)
  Q = fmpz[]
  while !isempty(M)
    @vprint :NfOrd 1 M
    q = pop!(M)
    if isprime(q)
      OO1 = pmaximal_overorder(O, q)
      if valuation(discriminant(OO1), q) < valuation(discriminant(OO), q)
        OO += OO1
      end
    else
      OO, q1 = _cycleBL(OO, q)
      if q1 == q
        push!(Q, q)
      elseif !isone(q1)
        push!(M, q1)
        push!(M, divexact(q, q1))
        M = coprime_base(M)
      end
    end
  end
  if isempty(Q)
    OO.ismaximal = 1
  end
  return OO, Q

end


function _qradical(O::NfOrd, q::fmpz)
  
  d = degree(O)
  R = ResidueRing(FlintZZ, q, cached=false)
  #First, we compute the q-radical as the kernel of the trace matrix mod q.
  #By theory, this is free if q is prime; if I get a non free module, I have found a factor of q.
  @vprint :NfOrd 1 "radical computation\n "
  rk, M = kernel(trace_matrix(O), R, side = :left)
  if iszero(rk)
    @vprint :NfOrd 1 "The radical is equal to the ideal generated by q"
    return fmpz(1), ideal(O, q)
  end
  M = howell_form(M)     
  for i = 1:nrows(M)
    if iszero_row(M, i)
      break
    end
    j = i
    while iszero(M[i,j])
      j += 1
    end
    if !isone(M[i,j])
      @vprint :NfOrd 1 "Split: $(M[i,j])"
      return lift(M[i,j]), NfOrdIdl()
    end
  end
  # Now, we have the radical.
  # We want to compute the ring of multipliers.
  # So we need to lift the matrix.
  @vprint :NfOrd 1 "Computing hnf of basis matrix \n "
  MatIdeal = zero_matrix(FlintZZ, d, d)
  for i=1:nrows(M)
    for j=1:degree(O)
      MatIdeal[i, j] = M[i,j].data
    end
  end
  gens = NfOrdElem[O(q)]
  for i=1:nrows(M)
    if !iszero_row(MatIdeal, i)
      push!(gens, elem_from_mat_row(O, MatIdeal, i))
    end       
  end
  M2 = _hnf_modular_eldiv(MatIdeal, fmpz(q),  :lowerleft)
  I = NfOrdIdl(O, M2)
  I.gens = gens
  return fmpz(1), I
end

function _cycleBL(O::NfOrd, q::fmpz)
  
  q1, I = _qradical(O, q)
  if !isone(q1)
    return O, q1
  elseif isdefined(I, :princ_gens) && q == I.princ_gens
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
  @vprint :NfOrd 1 "couldn't enlarge\n"
  # (I:I)=OO. Now, we want to prove tameness (or get a factor of q)
  # We have to test that (OO:a)/B is a free Z/qZ module.
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
  @vprint :NfOrd 1 "...is free\n"
  return _cycleBL2(O, q, I)

end

function _cycleBL2(O::NfOrd, q::fmpz, I::NfOrdIdl)

  h = 2
  ideals = Array{NfOrdIdl,1}(undef, 3)
  ideals[1] = I
  ideals[2] = I*I
  ideals[3] = ideals[2] * I
  while true
    if h > degree(O)
      error("Not found!")
    end
    I1 = (ideals[1] + ideal(O, q))*(ideals[3] + ideal(O, q))
    I2 = (ideals[2] + ideal(O, q))^2
    M2 = basis_mat(I2, copy = false)*basis_mat_inv(I1, copy = false)
    @assert isone(M2.den)
    G2 = divisors(M2.num, q)
    if isempty(G2)
      h += 1
      ideals[1] = ideals[2]
      ideals[2] = ideals[3]
      ideals[3] = ideals[2]*I
      continue
    end
    for i = 1:length(G2)
      q1 = gcd(q, G2[i])
      if q1 != q && !isone(q1)
        return O, q1
      end
    end
    break
  end
  f, r = ispower(q, h)
  if f
    return O, r
  else
    return O, q
  end
end



function TameOverorderBL(O::NfOrd, lp::Array{fmpz,1}=fmpz[])
    
  # First, we hope that we can get a factorization of the discriminant by computing 
  # the structure of the group OO^*/OO
  OO=O
  list = append!(elementary_divisors(trace_matrix(OO)), primes_up_to(degree(O)))
  l=coprime_base(list)
  #Some trivial things, maybe useless
  for i=1:length(l)
    a,b=ispower(l[i])
    if a>1
      l[i]=b
    end
    if isprime(l[i])
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
    q=M[1]
    if isprime(q)
      OO1=pmaximal_overorder(O, q)
      if valuation(discriminant(OO1), q)<valuation(discriminant(OO), q)
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
    OO.ismaximal=1
  end
  return OO, Q

end

################################################################################
#
#  p-overorder
#
################################################################################

function _poverorder(O::NfAbsOrd, p::fmpz)
  @vtime :NfOrd 3 I = pradical(O, p)
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
  if isequation_order(O) && issimple(nf(O))
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
the index $[ \mathcal O_K : R]$ is not dividible by $p$.
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
***
    ring_of_multipliers(I::NfAbsOrdIdl) -> NfOrd

> Computes the order $(I : I)$, which is the set of all $x \in K$
> with $xI \subseteq I$.
"""
function ring_of_multipliers(a::NfAbsOrdIdl)
  O = order(a) 
  n = degree(O)
  if isdefined(a, :gens) && length(a.gens) < n
    B = a.gens
  else
    B = basis(a, copy = false)
  end
  @assert length(B) > 0
  bmatinv = basis_mat_inv(a, copy = false)
  m = zero_matrix(FlintZZ, n*length(B), n)
  for i = 1:length(B)
    M = representation_matrix(B[i])
    mul!(M, M, bmatinv.num)
    if bmatinv.den == 1
      for j=1:n
        for k=1:n
          m[j+(i-1)*n,k] = M[k,j]
        end
      end
    else
      for j=1:n
        for k=1:n
          m[j+(i-1)*n,k] = divexact(M[k,j], bmatinv.den)
        end
      end
    end
  end
  mhnf = hnf_modular_eldiv!(m, minimum(a))
  s = prod(mhnf[i,i] for i = 1:n)
  if isone(s)
    return O
  end
  # mhnf is upper right HNF
  # mhnftrans = transpose(view(mhnf, 1:n, 1:n))
  for i = 1:n
    for j = i+1:n
      mhnf[j, i] = mhnf[i, j]
      mhnf[i, j] = 0
    end
  end
  mhnftrans = view(mhnf, 1:n, 1:n)
  b = FakeFmpqMat(pseudo_inv(mhnftrans))
  mul!(b, b, basis_mat(O, copy = false))
  @hassert :NfOrd 1 defines_order(nf(O), b)[1]
  O1 = NfAbsOrd(nf(O), b)
  if isdefined(O, :disc)
    O1.disc = divexact(O.disc, s^2)
  end
  if isdefined(O, :index)
    O1.index = s*O.index
  end
  if isdefined(O, :basis_mat_inv)
    O1.basis_mat_inv = O.basis_mat_inv * mhnftrans
  end
  return O1
end

################################################################################
#
#  p-radical
#
################################################################################


function pradical_trace(O::NfAbsOrd, p::Union{Integer, fmpz})
  d = degree(O)
  M = trace_matrix(O)
  F = GF(p, cached = false)
  M1 = change_base_ring(M, F)
  k, B = nullspace(M1)
  if k == 0
    return ideal(O, p)
  end
  M2 = zero_matrix(FlintZZ, d, d)
  for i = 1:ncols(B)
    for j = 1:d
      M2[i, j] = FlintZZ(B[j, i].data)
    end
  end
  gens = elem_type(O)[O(p)]
  for i=1:ncols(B)
    if !iszero_row(M2,i)
      push!(gens, elem_from_mat_row(O, M2, i))
    end
  end
  M2 = _hnf_modular_eldiv(M2, fmpz(p), :lowerleft)
  I = ideal(O, M2)
  I.minimum = p
  I.gens = gens
  return I
end

function pradical_frobenius(O::NfAbsOrd, p::Union{Integer, fmpz})
  
  d = degree(O)
  j = clog(fmpz(d), p)
  @assert p^(j-1) < d
  @assert d <= p^j

  R = GF(p, cached = false)
  A = zero_matrix(R, degree(O), degree(O))
  B = basis(O, copy = false)
  for i in 1:d
    t = powermod(B[i], p^j, p)
    ar = elem_in_basis(t)
    for k in 1:d
      A[k, i] = ar[k]
    end
  end
  X = right_kernel_basis(A)
  gens = elem_type(O)[O(p)]
  if length(X)==0
    I = ideal(O, p)
    I.gens = gens
    return I
  end
  #First, find the generators
  for i = 1:length(X)
    coords = Array{fmpz,1}(undef, d)
    for j=1:d
      coords[j] = lift(X[i][j])
    end
    push!(gens, O(coords))
  end
  #Then, construct the basis matrix of the ideal
  m = zero_matrix(FlintZZ, d, d)
  for i = 1:length(X)
    for j = 1:d
      m[i, j] = lift(X[i][j])
    end
  end
  mm = _hnf_modular_eldiv(m, fmpz(p), :lowerleft)
  I = NfAbsOrdIdl(O, mm)
  I.minimum = p
  I.gens = gens
  return I

end

@doc Markdown.doc"""
    pradical(O::NfOrd, p::{fmpz|Integer}) -> NfAbsOrdIdl

> Given a prime number $p$, this function returns the $p$-radical
> $\sqrt{p\mathcal O}$ of $\mathcal O$, which is
> just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
> \in p\mathcal O \}$. It is not checked that $p$ is prime.
"""
function pradical(O::NfAbsOrd, p::Union{Integer, fmpz})
  if p isa fmpz
    if nbits(p) < 64
      return pradical(O, Int(p))
    end
  end
  d = degree(O)
  
  #Trace method if the prime is large enough
  if p > d
    return pradical_trace(O, p)
  else
    return pradical_frobenius(O, p)
  end
end


