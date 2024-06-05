abstract type Hensel end

mutable struct HenselCtxQadic <: Hensel
  f::PolyRingElem{QadicFieldElem}
  lf::Vector{PolyRingElem{QadicFieldElem}}
  la::Vector{PolyRingElem{QadicFieldElem}}
  p::QadicFieldElem
  n::Int
  #TODO: lift over subfields first iff poly is defined over subfield
  #TODO: use flint if QadicFieldElem = PadicFieldElem!!
  function HenselCtxQadic(f::PolyRingElem{QadicFieldElem}, lfp::Vector{FqPolyRingElem})
    @assert sum(map(degree, lfp)) == degree(f)
    Q = base_ring(f)
    Qx = parent(f)
    K, mK = residue_field(Q)
    i = 1
    la = Vector{PolyRingElem{QadicFieldElem}}()
    n = length(lfp)
    while i < length(lfp)
      f1 = lfp[i]
      f2 = lfp[i+1]
      g, a, b = gcdx(f1, f2)
      @assert isone(g)
      push!(la, setprecision(map_coefficients(x->preimage(mK, x), a, cached = false, parent = Qx), 1))
      push!(la, setprecision(map_coefficients(x->preimage(mK, x), b, cached = false, parent = Qx), 1))
      push!(lfp, f1*f2)
      i += 2
    end
    return new(f, map(x->setprecision(map_coefficients(y->preimage(mK, y), x, parent = Qx), 1), lfp), la, uniformizer(Q), n)
  end

  function HenselCtxQadic(f::PolyRingElem{QadicFieldElem})
    Q = base_ring(f)
    K, mK = residue_field(Q)
    fp = map_coefficients(mK, f, cached = false)
    lfp = collect(keys(factor(fp).fac))
    return HenselCtxQadic(f, lfp)
  end
end

function Base.show(io::IO, C::HenselCtxQadic)
  println(io, "Lifting tree for $(C.f), with $(C.n) factors, currently up precision $(valuation(C.p))")
end

function lift(C::HenselCtxQadic, mx::Int = minimum(precision, coefficients(C.f)))
  p = C.p
  Q = parent(p)
  N = valuation(p)
#  @show map(precision, coefficients(C.f)), N, precision(parent(p))
  #have: N need mx
  if length(C.lf) == 1
    C.lf[1] = C.f
    return
  end
  ch = [mx]
  while ch[end] > N
    push!(ch, div(ch[end]+1, 2))
  end
  @vprintln :PolyFactor 1 "using lifting chain $ch"
  for k=length(ch)-1:-1:1
    N2 = ch[k]
    setprecision!(Q, N2+1)
    p = Q(prime(Q))^ch[k+1]
    i = length(C.lf)
    j = i-1
    p = setprecision(p, N2)
    while j > 0
      if i==length(C.lf)
        f = setprecision(C.f, N2)
      else
        f = setprecision(C.lf[i], N2)
      end

      #formulae and names from the Flint doc
      h = C.lf[j]
      g = C.lf[j-1]
      b = C.la[j]
      a = C.la[j-1]
      h = setprecision(h, N2)
      g = setprecision(g, N2)
      a = setprecision(a, N2)
      b = setprecision(b, N2)

      fgh = (f-g*h)*inv(p)
      G = rem(fgh*b, g)*p+g
      H = rem(fgh*a, h)*p+h
      t = (1-a*G-b*H)*inv(p)
      B = rem(t*b, g)*p+b
      A = rem(t*a, h)*p+a
      if i < length(C.lf)
        C.lf[i] = G*H
      end
      C.lf[j-1] = G
      C.lf[j] = H
      C.la[j-1] = A
      C.la[j] = B
      i -= 1
      j -= 2
    end
  end
  C.p = Q(prime(Q))^ch[1]
end

function factor(C::HenselCtxQadic)
  return C.lf[1:C.n]
end

function precision(C::HenselCtxQadic)
  return valuation(C.p)
end

# interface to use Bill's Z/p^k lifting code. same algo as above, but
# tighter implementation
mutable struct HenselCtxPadic <: Hensel
  X::HenselCtx
  f::PolyRingElem{PadicFieldElem}
  function HenselCtxPadic(f::PolyRingElem{PadicFieldElem})
    r = new()
    r.f = f
    Zx = polynomial_ring(FlintZZ, cached = false)[1]
    ff = Zx()
    for i=0:degree(f)
      setcoeff!(ff, i, lift(ZZ, coeff(f, i)))
    end
    r.X = HenselCtx(ff, prime(base_ring(f)))
    start_lift(r.X, 1)
    return r
  end
end

function lift(C::HenselCtxPadic, mx::Int)
  for i=0:degree(C.f)
    setcoeff!(C.X.f, i, lift(ZZ, coeff(C.f, i)))
  end
  continue_lift(C.X, mx)
end

function factor(C::HenselCtxPadic)
  res =  typeof(C.f)[]
  Zx = polynomial_ring(FlintZZ, cached = false)[1]
  h = Zx()
  Qp = base_ring(C.f)
  for i = 1:C.X.LF._num #from factor_to_dict
    #cannot use factor_to_dict as the order will be random (hashing!)
    #TODO: there is the option to return list rather than dict.
    g = parent(C.f)()
    ccall((:fmpz_poly_set, libflint), Nothing, (Ref{ZZPolyRingElem}, Ref{fmpz_poly_raw}), h, C.X.LF.poly+(i-1)*sizeof(fmpz_poly_raw))
    for j=0:degree(h)
      setcoeff!(g, j, Qp(coeff(h, j)))
    end
    push!(res, g)
  end
  return res
end

function precision(C::HenselCtxPadic)
  return Int(C.X.N)
end

function precision(H::HenselCtx)
  return Int(H.N)
end

function prime(H::HenselCtx)
  return Int(H.p)
end

function div_preinv(a::ZZRingElem, b::ZZRingElem, bi::fmpz_preinvn_struct)
  q = ZZRingElem()
  r = ZZRingElem()
  fdiv_qr_with_preinvn!(q, r, a, b, bi)
  return q
end

@doc raw"""
    round(::ZZRingElem, a::ZZRingElem, b::ZZRingElem, bi::ZZRingElem) -> ZZRingElem

Computes `round(a//b)` using the pre-inverse of `2b`.
"""
function Base.round(::Type{ZZRingElem}, a::ZZRingElem, b::ZZRingElem, bi::fmpz_preinvn_struct)
  s = sign(a)
  as = abs(a)
  #TODO: mul! and friends to make memory friendly
  r = s*div_preinv(2*as+b, 2*b, bi)
  @hassert :PolyFactor 1 abs(r - a//b) <= 1//2
#  @assert r == round(ZZRingElem, a//b)
  return r
end

#TODO: think about computing pM[1][1,:]//pM[2] as a "float" approximation
#      to save on multiplications
function reco(a::ZZRingElem, M, pM::Tuple{ZZMatrix, ZZRingElem, fmpz_preinvn_struct}, O)
  m = map(x -> round(ZZRingElem, a*x, pM[2], pM[3]), pM[1][1, :])*M
  return a - O(m)
end

function reco(a::ZZRingElem, M, pM::Tuple{ZZMatrix, ZZRingElem}, O)
  m = map(x -> round(ZZRingElem, a*x, pM[2]), pM[1][1, :])*M
  return a - O(m)
end

function reco(a::AbsNumFieldOrderElem, M, pM)
  m = matrix(FlintZZ, 1, degree(parent(a)), coordinates(a))
  m = m - map(x -> round(ZZRingElem, x, pM[2]), m*pM[1])*M
  return parent(a)(m)
end

function is_prime_nice(O::AbsSimpleNumFieldOrder, p::Int)
  f = is_prime_nice(nf(O), p)
  f || return f
  if discriminant(O) %p == 0
    return false
  end
  return true
end

function is_prime_nice(K::AbsSimpleNumField, p::Int)
  d = lcm(map(denominator, coefficients(K.pol)))
  if d % p == 0
    return false
  end
  F = Native.GF(p)
  f = map_coefficients(F, d*K.pol, cached = false)
  if degree(f) < degree(K)
    return false
  end
  if iszero(discriminant(f))
    return false
  end
  return true
end

@doc raw"""
    factor_new(f::PolyRingElem{AbsSimpleNumFieldElem}) -> Vector{PolyRingElem{AbsSimpleNumFieldElem}}

Direct factorisation over a number field, using either Zassenhaus' approach
with the potentially exponential recombination or a van Hoeij like approach using LLL.
The decision is based on the number of local factors.
"""
function factor_new(f::PolyRingElem{AbsSimpleNumFieldElem})
  k = base_ring(f)
  local zk::AbsSimpleNumFieldOrder
  if is_maximal_order_known(k)
    zk = maximal_order(k)
    if isdefined(zk, :lllO)
      zk = zk.lllO::AbsSimpleNumFieldOrder
    end
  else
    zk = any_order(k)
  end
  zk = lll(zk) # always a good option!
  p = degree(f)
  forig = f
  f *= lcm(map(denominator, coefficients(f)))
  np = 0
  bp = 1*zk
  br = 0
  s = Set{Int}()
  while true
    @vprintln :PolyFactor 3 "Trying with $p"
    p = next_prime(p)
    if !is_prime_nice(zk, p)
      continue
    end
    P = prime_decomposition(zk, p, 1)
    if length(P) == 0
      continue
    end
    F, mF1 = ResidueFieldSmallDegree1(zk::AbsSimpleNumFieldOrder, P[1][1])
    mF = extend(mF1, k)
    fp = map_coefficients(mF, f, cached = false)
    if degree(fp) < degree(f) || iszero(constant_coefficient(fp)) || iszero(constant_coefficient(fp))
      continue
    end
    if !is_squarefree(fp)
      continue
    end
    lf = factor_shape(fp)
    ns = degree_set(lf)
    if length(s) == 0
      s = ns
    else
      s = Base.intersect(s, ns)
    end
    @vprintln :PolyFactor 3 "$s"

    if length(s) == 1
      return typeof(f)[forig]
    end

    if br == 0 || br > sum(values(lf))
      br = sum(values(lf))
      bp = P[1][1]
    end
    np += 1
    if np > 2 && br > 10
      break
    end
    if np > min(100, 2*degree(f))
      break
    end
  end
  @vprintln :PolyFactor 1 "possible degrees: $s"
  if br < 5 #TODO calibrate, the 5 is random...
    return zassenhaus(f, bp, degset = s)
  else
    return van_hoeij(f, bp)
  end
end

function degree_set(fa::Dict{Int, Int})
  T = Vector{Int}(undef, sum(values(fa)))
  ind = 0
  for (k, v) in fa
    for j = 1:v
      T[j+ind] = k
    end
    ind += v
  end
  M = MSet(T)
  return Set(sum(s) for s = subsets(M) if length(s) > 0)
end

@doc raw"""
    zassenhaus(f::PolyRingElem{AbsSimpleNumFieldElem}, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; degset::Set{Int} = Set{Int}(collect(1:degree(f)))) -> Vector{PolyRingElem{AbsSimpleNumFieldElem}}

Zassenhaus' factoring algorithm over an absolute simple field. Given a prime ideal $P$ which
has to be an unramified non-index divisor, a factorisation of $f$ in the $P$-adic completion
is computed. In the last step, all combinations of the local factors are tried to find the
correct factorisation.
$f$ needs to be square-free and square-free modulo $P$ as well.
"""
function zassenhaus(f::PolyRingElem{AbsSimpleNumFieldElem}, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; degset::Set{Int} = Set{Int}(collect(1:degree(f))))
  @vprintln :PolyFactor 1 "Using (relative) Zassenhaus"

  K = base_ring(parent(f))
  C, mC = completion_easy(K, P)

  b = landau_mignotte_bound(f)*upper_bound(ZZRingElem, sqrt(t2(leading_coefficient(f))))
  den = K(1)
  if !is_maximal_known_and_maximal(order(P))
    if !is_defining_polynomial_nice(K)
      den = K(discriminant(order(P))*det(basis_matrix(FakeFmpqMat, order(P), copy = false)))
    else
      den = derivative(K.pol)(gen(K))
    end
    b *= upper_bound(ZZRingElem, sqrt(t2(den)))
  end

  #TODO: write and use
  # - T_2 -> prec for reco
  # - reco
  # - a reco context? Share with Galois? Problem in Oscar/ Hecke?
  # - reco fail with size?
  # - norm change const to reco ctx? Store den in there as well?
  c1, c2 = norm_change_const(order(P))
  N = ceil(Int, degree(K)/2/log(norm(P))*(log2(c1*c2) + 2*nbits(b)))
  @vprintln :PolyFactor 1 "using a precision of $N"

  setprecision!(C, N)

  vH = vanHoeijCtx()
  if degree(P) == 1
    vH.H = HenselCtxPadic(map_coefficients(x->coeff(mC(x), 0), f, cached = false))
  else
    vH.H = HenselCtxQadic(map_coefficients(mC, f, cached = false))
  end
  vH.C = C
  vH.P = P

  @vtime :PolyFactor 1 grow_prec!(vH, N)

  H = vH.H

  M = vH.Ml
  pM = vH.pMr

  lf = factor(H)
  zk = order(P)

  if degree(P) == 1
    S = Set(map(x -> map_coefficients(y -> lift(ZZ, y), x, parent = parent(f)), lf))
  else
    S = Set(map(x -> map_coefficients(y -> preimage(mC, y), x, parent = parent(f)), lf))
  end
  #TODO: test reco result for being small, do early abort
  #TODO: test selected coefficients first without computing the product
  #TODO: once a factor is found (need to enumerate by size!!!), remove stuff...
  #    : if f is the norm of a poly over a larger field, then every
  #      combination has to respect he prime splitting in the extension
  #      the norm(poly) is the prod of the local norm(poly)s
  #TODO: add/use degree sets and search restrictions. Users might want restricted degrees
  #TODO: add a call to jump from van Hoeij to Zassenhaus once a partitioning
  #      is there.
  used = empty(S)
  res = typeof(f)[]
  for d = 1:length(S)
    for s = subsets(S, d)
      if length(Base.intersect(used, s)) > 0
#        println("re-using data")
        continue
      end
      #TODO: test constant term first, possibly also trace + size
      g = prod(s)
      g = map_coefficients(x -> K(reco(zk(leading_coefficient(f)*x*den), M, pM)), g, parent = parent(f))*(1//leading_coefficient(f)//den)
      if iszero(rem(f, g))
        push!(res, g)
        used = union(used, s)
        if length(used) == length(S)
          return res
        end
      else
  #      println("reco failed")
      end
    end
  end
  error("no factor found - should not happen")
  return res
end

###############################################

#given the local factorisation in H, find the cld, the Coefficients of the Logarithmic
#Derivative: a factor g of f is mapped to g'*f/g
#Only the coefficients 0:up_to and from:degree(f)-1 are computed
function cld_data(H::Hensel, up_to::Int, from::Int, mC, Mi, sc::AbsSimpleNumFieldElem)
  lf = factor(H)
  a = preimage(mC, zero(codomain(mC)))
  k = parent(a)
  N = degree(H.f)
  @assert 0<= up_to <= N  #up_tp: modulo x^up_tp
  @assert 0<= from <= N   #from : div by x^from
#  @assert up_to <= from

  M = zero_matrix(FlintZZ, length(lf), (1+up_to + N - from) * degree(k))
  #last_lf[] = (lf, H.f, up_to)

  lf = [divexact_low(mullow(derivative(x), H.f, up_to+1), x, up_to+1) for x = lf]
#  lf = [divexact(derivative(x)*H.f, x) for x = lf]
#  @show llf .- lf

  NN = zero_matrix(FlintZZ, 1, degree(k))
  d = FlintZZ()

  for i=0:up_to
    for j=1:length(lf)
      c = sc * preimage(mC, coeff(lf[j], i)) # should be an AbsSimpleNumFieldElem
      elem_to_mat_row!(NN, 1, d, c)
      mul!(NN, NN, Mi) #base_change, Mi should be the inv-lll-basis-mat wrt field
      @assert isone(d)
      for h=1:degree(k)
        M[j, i*degree(k) + h] = NN[1, h]
      end
    end
  end
  lf = factor(H)
  lf = [divhigh(mulhigh(derivative(x), H.f, from), x, from) for x = lf]
  for i=from:N-1
    for j=1:length(lf)
      c = sc * preimage(mC, coeff(lf[j], i)) # should be an AbsSimpleNumFieldElem
      elem_to_mat_row!(NN, 1, d, c)
      mul!(NN, NN, Mi) #base_change, Mi should be the inv-lll-basis-mat wrt field
      @assert isone(d)
      for h=1:degree(k)
        M[j, (i-from+up_to)*degree(k) + h] = NN[1, h]
      end
    end
  end
  return M
end

mutable struct vanHoeijCtx
  H::Hensel
  pr::Int
  Ml::ZZMatrix
  pMr::Tuple{ZZMatrix, ZZRingElem, fmpz_preinvn_struct}
  pM::Tuple{ZZMatrix, ZZRingElem}
  C::Union{QadicField, PadicField}
  P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}
  function vanHoeijCtx()
    return new()
  end
end

#increase the precision of the local data, i.e lift the factorisation and
#the LLL_basis of the ideal
function grow_prec!(vH::vanHoeijCtx, pr::Int)
  lift(vH.H, pr)

  @vtime :PolyFactor 2 X1 = vH.P^pr
  @vtime :PolyFactor 2 X2 = basis_matrix(X1)
  @vtime :PolyFactor 2 vH.Ml = lll(X2)
  @vtime :PolyFactor 2 pMr = pseudo_inv(vH.Ml)
  F = FakeFmpqMat(pMr)
  #M * basis_matrix(zk) is the basis wrt to the field
  #(M*B)^-1 = B^-1 * M^-1, so I need basis_mat_inv(zk) * pM
  vH.pMr = (F.num, F.den, fmpz_preinvn_struct(2*F.den))
  F = basis_mat_inv(FakeFmpqMat, order(vH.P)) * F
  vH.pM = (F.num, F.den)
end

function lll_with_removal_knapsack(x::ZZMatrix, b::ZZRingElem, ctx::LLLContext = LLLContext(0.99, 0.51))
   z = deepcopy(x)
   d = Int(ccall((:fmpz_lll_wrapper_with_removal_knapsack, libflint), Cint,
    (Ref{ZZMatrix}, Ptr{nothing}, Ref{ZZRingElem}, Ref{LLLContext}), z, C_NULL, b, ctx))
   return d, z
end

function gradual_feed_lll(M::ZZMatrix, sm::ZZRingElem, B::ZZMatrix, d::ZZRingElem, bnd::ZZRingElem)
  b = maximum(nbits, B)
  sc = max(0, b-55)

  while false && sc > 0
    BB = tdivpow2(B, sc)
    dd = tdivpow2(d, sc)
    MM = [M BB; zero_matrix(FlintZZ, ncols(B), ncols(M)) dd*identity_matrix(FlintZZ, ncols(B))]
    @show maximum(nbits, MM)
    @time MM, T = lll_with_transform(MM, LLLContext(0.75, 0.51))
    @time l, _ = lll_with_removal(MM, bnd, LLLContext(0.75, 0.51))
    @show l
    M = T[1:nrows(M), 1:nrows(M)]*M
    B = T[1:nrows(M), 1:nrows(M)]*B
    mod_sym!(B, d)
    @show maximum(nbits, B)
    @show sc = max(0, sc-55)
  end
  M = [M B; zero_matrix(FlintZZ, ncols(B), ncols(M)) d*identity_matrix(FlintZZ, ncols(B))]
  return lll_with_removal(M, bnd)
end


@doc raw"""
    van_hoeij(f::PolyRingElem{AbsSimpleNumFieldElem}, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; prec_scale = 20) -> Vector{PolyRingElem{AbsSimpleNumFieldElem}}

A van Hoeij-like factorisation over an absolute simple number field, using the factorisation in the
$P$-adic completion where $P$ has to be an unramified non-index divisor and the square-free $f$ has
to be square-free mod $P$ as well.

Approach is taken from Hart, Novacin, van Hoeij in ISSAC.
"""
function van_hoeij(f::PolyRingElem{AbsSimpleNumFieldElem}, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}; prec_scale = 1)
  @vprintln :PolyFactor 1 "Using (relative) van Hoeij"
  @vprintln :PolyFactor 2 "with p = $P"
  @assert all(x->denominator(x) == 1, coefficients(f))

  K = base_ring(parent(f))
  C, mC = completion_easy(K, P)

  zk = order(P)
  if is_maximal_known_and_maximal(zk)
    den = K(1)
  elseif is_defining_polynomial_nice(K)
    den = derivative(K.pol)(gen(K))
  else
    den = K(discriminant(order(P))) * det(basis_matrix(FakeFmpqMat, order(P), copy= false))
  end

  _, mK = residue_field(order(P), P)
  mK = extend(mK, K)
  r = length(factor(map_coefficients(mK, f, cached = false)))
  N = degree(f)
  @vprintln :PolyFactor 1  "Having $r local factors for degree $N"

  setprecision!(C, 5)

  vH = vanHoeijCtx()
  if degree(P) == 1
    vH.H = HenselCtxPadic(map_coefficients(x->coeff(mC(x), 0), f, cached = false))
  else
    vH.H = HenselCtxQadic(map_coefficients(mC, f, cached = false))
  end
  vH.C = C
  vH.P = P

  up_to = min(5, ceil(Int, N/20))
  up_to_start = up_to
  from = N-up_to  #use 5 coeffs on either end
  up_to = min(up_to, N)
  from = min(from, N)
  from = max(up_to, from)
  b = cld_bound(f, vcat(0:up_to-1, from:N-1)) .* upper_bound(ZZRingElem, sqrt(t2(den*leading_coefficient(f))))
  b .*= b
  #Fieker/ Friedrichs is using T_2! while cld_bound is estimating sqrt(T_2)
  #TODO: think about changing cld_bound...
  #actually: for a polynomial with complex coefficients, cld_bound gives upper bounds on the
  #abs. value of the cld coefficients, not related to T_2 at all...
  #=
    cld_bound: for an ZZPolyRingElem, give size bounds for the abs value of coefficients of the cld
    - the bounds are monotonous in the abs value of the coeffs (I think they are using abs value of coeff)
    - the math works for real coeffs as well
    - thus create an ZZPolyRingElem with pos. coeffs. containing upper bounds of the conjugates of the
      coeffs. DOne via T_2: sqrt(n*T_2(alpha) is an upper bounds for all conjugates
    - Fieker/ Friedrichs compares T_2 vs 2-norm (squared) of coeffs
    - leading coeff as well as den are algebraic
      CHECK: den*lead*cld in Z[alpha] (or in the order used)
  =#

  # from Fieker/Friedrichs, still wrong here
  # needs to be larger than anticipated...
  c1, c2 = norm_change_const(order(P))
  b = Int[ceil(Int, degree(K)/2/log(norm(P))*(log2(c1*c2) + 2*nbits(x)+ degree(K)*r+prec_scale)) for x = b]
  #CHECK: 1st block is FF-bound on prec to recover cld's
  #       2nd block is for additional bits for rounding?
  bb = landau_mignotte_bound(f)*upper_bound(ZZRingElem, sqrt(t2(den*leading_coefficient(f))))
  #CHECK: landau... is a bound on the (abs value) of the coeffs of the factors,
  #       need everywhere sqrt(n*T_2)? to get conjugate bounds
  kk = ceil(Int, degree(K)/2/log(norm(P))*(log2(c1*c2) + 2*nbits(bb)))
  @vprintln :PolyFactor 2 "using CLD precision bounds $b"

  used = []
  really_used = []
  M = identity_matrix(FlintZZ, r)*ZZRingElem(2)^prec_scale

  while true #the main loop
    #find some prec
    #to start with, I want at least half of the CLDs to be useful
    if length(b) == degree(f)
      i = maximum(b) + 100
    else
      i= sort(b)[div(length(b)+1, 2)]
    end
    i = max(i, kk) #this seems to suggest, that prec is large enough to find factors! So the fail-2 works
    @vprintln :PolyFactor 1 "setting prec to $i, and lifting the info ..."
    setprecision!(codomain(mC), i)
    if degree(P) == 1
      vH.H.f = map_coefficients(x->coeff(mC(x), 0), f, cached = false)
    else
      vH.H.f = map_coefficients(mC, f, cached = false)
    end
    @vtime :PolyFactor 1 grow_prec!(vH, i)


    av_bits = sum(nbits, vH.Ml)/degree(K)^2 #Ml: lll basis of P^i?
    @vprintln :PolyFactor 1 "obtaining CLDs..."

    #prune: in Swinnerton-Dyer: either top or bottom are too large.
    while from < N && b[N - from + up_to] > i
      from += 1
    end
    while up_to > 0 && b[up_to] > i
      up_to -= 1
    end
    b = b[vcat(1:up_to, length(b)-(N-from-1):length(b))]
    have = vcat(0:up_to-1, from:N-2)  #N-1 is always 1

    if degree(P) == 1
      mD = MapFromFunc(K, base_ring(vH.H.f), x->coeff(mC(x),0), y->K(lift(ZZ, y)))
      @vtime :PolyFactor 1 C = cld_data(vH.H, up_to, from, mD, vH.pM[1], den*leading_coefficient(f))
    else
      @vtime :PolyFactor 1 C = cld_data(vH.H, up_to, from, mC, vH.pM[1], den*leading_coefficient(f))
    end

    # In the end, p-adic precision needs to be large enough to
    # cover some CLDs. If you want the factors, it also has to
    # cover those. The norm change constants also come in ...
    # and the degree of P...

    # starting precision:
    # - large enough to recover factors (maybe)
    # - large enough to recover some CLD (definitely)
    # - + eps to give algo a chance.
    # Then take 10% of the CLD, small enough for the current precision
    # possibly figure out which CLD's are available at all

    # we want
    # I |  C/p^n
    # 0 |   I
    # true factors, in this lattice, are small (the lower I is the rounding)
    # the left part is to keep track of operations
    # by cld_bound, we know the expected upper size of the rounded legal entries
    # so we scale it by the bound. If all would be exact, the true factors would be zero...
    # WHY???Zero??? small I see, but not zero..., smaller than 1 I can see.
    # 1st make integral:
    # I | C
    # 0 | p^n
    # scale:
    # I | C/lambda
    # 0 | p^n/lambda  lambda depends on the column
    # now, to limit damages re-write the rationals with den | 2^k (rounding)
    # I | D/2^k
    #   | X/2^k
    #make integral
    # 2^k | D
    #  0  | X   where X is still diagonal
    # is all goes like planned: lll with reduction will magically work...
    # needs (I think): fix a in Z_k, P and ideal. Then write a wrt. a LLL basis of P^k
    #  a = sum a^k_i alpha^k_i, a^k_i in Q, then for k -> infty, a^k_i -> 0
    #  (ineffective: write coeffs with Cramer's rule via determinants. The
    #  numerator has n-1 LLL-basis vectors and one small vector (a), thus the
    #  determinant is s.th. ^(n-1) and the coeff then ()^(n-1)/()^n should go to zero
    # lambda should be chosen, so that the true factors become < 1 by it
    # for the gradual feeding, we can also add the individual coefficients (of the nf_elems) individually


    # - apply transformations already done (by checking the left part of the matrix)
    # - scale, round
    # - call lll_with_removel
    # until done (whatever that means)
    # if unlucky: re-do Hensel and start over again, hopefully retaining some info
    # can happen if the CLD coeffs are too large for the current Hensel level

    while length(have) > length(used)
      local m
      m_empty = true
      for i=1:length(have)
        if have[i] in used
          continue
        end
        if m_empty || b[i] < m[1]
          m_empty = false
          m = (b[i], i)
        end
      end
      n = have[m[2]]
      @assert !(n in used)
      push!(used, n)

      i = findfirst(x->x == n, have) #new data will be in block i of C
      @vprintln :PolyFactor 2 "trying to use coeff $n which is $i"
      if b[i] > precision(codomain(mC))
        @vprintln :PolyFactor 2 "not enough precision for CLD $i, $b, $(precision(codomain(mC))), skipping"

#        error()
        continue
      end
      sz = floor(Int, degree(K)*av_bits/log(norm(P)) - b[i])

      B = sub(C, 1:r, (i-1)*degree(K)+1:i*degree(K))
#      @show i, maximum(nbits, B)

      T = sub(M, 1:nrows(M), 1:r)
      B = T*B   # T contains the prec_scale
      mod_sym!(B, vH.pM[2]*ZZRingElem(2)^prec_scale)

#      @show maximum(nbits, B), nbits(vH.pM[2]), b[i]
      if sz + prec_scale >= nbits(vH.pM[2]) || sz < 0
        println("Loss of precision for this col: ", sz, " ", nbits(vH.pM[2]))
        @show f, base_ring(f), P
        error()
        continue
      else
        sz = nbits(vH.pM[2]) - div(r, 1) - prec_scale
      end
      push!(really_used, n)
      Nemo.tdivpow2!(B, sz+prec_scale)
      d = tdivpow2(vH.pM[2], sz)

      bnd = r*ZZRingElem(2)^(2*prec_scale) + degree(K)*(ncols(M)-r)*div(r, 2)^2

      rt = time_ns()
      @vtime :PolyFactor 1 l, Mi = gradual_feed_lll(M, ZZRingElem(2)^prec_scale, B, d, bnd)
#      @vtime :PolyFactor 1 l, Mi = lll_with_removal(M, bnd)

      M = Mi
#      @show hnf(sub(M, 1:l, 1:r))
      if iszero(M[1:l, 1:r])
#        println(f)
#        println(base_ring(f))
        error("must never be zero")
      end
      @hassert :PolyFactor 1 !iszero(sub(M, 1:l, 1:r))
      M = sub(M, 1:l, 1:ncols(M))
      d = Dict{ZZMatrix, Vector{Int}}()
      for l=1:r
        k = M[:, l:l]
        if haskey(d, k)
          push!(d[k], l)
        else
          d[k] = [l]
        end
      end
      @vprintln :PolyFactor 1 "partitioning of local factors: $(values(d))"
      if length(keys(d)) <= nrows(M)
        @vprintln :PolyFactor 1  "BINGO: potentially $(length(keys(d))) factors"
        res = typeof(f)[]
        fail = []
        if length(keys(d)) == 1
          return [f]
        end
#        display(d)
        for v = values(d)
          #trivial test:
          if isone(den) && is_monic(f) #don't know what to do for non-monics
            a = prod(map(constant_coefficient, factor(vH.H)[v]))
            if degree(P) == 1
              A = K(reco(order(P)(lift(ZZ, a)), vH.Ml, vH.pMr))
            else
              A = K(reco(order(P)(preimage(mC, a)), vH.Ml, vH.pMr))
            end
            if denominator(divexact(constant_coefficient(f), A), order(P)) != 1
              @vprintln :PolyFactor 2 "Fail: const coeffs do not divide"
              push!(fail, v)
              if length(fail) > 1
                break
              end
              continue
            end
          end
          @vtime :PolyFactor 2 g = prod(factor(vH.H)[v])
          if degree(P) == 1
            @vtime :PolyFactor 2 G = parent(f)([K(reco(lift(ZZ, coeff(mC(den*leading_coefficient(f)), 0)*coeff(g, l)), vH.Ml, vH.pMr, order(P))) for l=0:degree(g)])
          else
            @vtime :PolyFactor 2 G = parent(f)([K(reco(order(P)(preimage(mC, mC(den*leading_coefficient(f))*coeff(g, l))), vH.Ml, vH.pMr)) for l=0:degree(g)])
          end
          G *= 1//(den*leading_coefficient(f))

          if !iszero(rem(f, G))
            @vprintln :PolyFactor 2 "Fail: poly does not divide"
            push!(fail, v)
            if length(fail) > 2
              break
            end
            continue
          end
          push!(res, G)
        end
        if length(fail) == 1
          @vprintln :PolyFactor 1 "only one reco failed, total success"
          push!(res, divexact(f, prod(res)))
          return res
        elseif false && length(fail) == 2 #ONLY legal if prec. is high enough
          #so that the individual factors would have worked....
          #f = x^12 + 4*x^10 + 11*x^8 + 4*x^6 - 41*x^4 - 8*x^2 + 37
          #over itself has 2 degree 4 factors that fail to combine
          #possibly related to the poly being really small.
          #need to investigate
          @vprintln :PolyFactor 1 "only two recos failed, total success"
          #only possibility is that the 2 need to combine...
          push!(res, divexact(f, prod(res)))
          return res
        end
        if length(res) < length(d)
          @vprintln :PolyFactor 1 "reco failed\n... here we go again ..."
        else
          return res
        end
      end
    end

    up_to = up_to_start = min(2*up_to_start, N)
    up_to = min(N, up_to)
    from = N-up_to
    from = min(from, N)
    from = max(up_to, from)

    have = vcat(0:up_to-1, from:N-2)  #N-1 is always 1
    if length(have) <= length(really_used)
      @show have, really_used, used
      @show f
      @show base_ring(f)
      #last_f[] = (f, P, vH)
      error("too bad")
    end
    used = deepcopy(really_used)

    b = cld_bound(f, vcat(0:up_to-1, from:N-1)) .* upper_bound(ZZRingElem, sqrt(t2(den*leading_coefficient(f))))
    b .*= b

    #TODO: see Fieker/Friedrichs comment above
    b = [ceil(Int, degree(K)/2/log(norm(P))*(log2(c1*c2) + 2*nbits(x)+ 2*prec_scale)) for x = b]
  end #the big while
end

#does not seem to be faster than the direct approach. (not modular)
#Magma is faster, which seems to suggest the direct resultant is
#even better (modular resultant)
# power series over finite fields are sub-par...or at least this usage
# fixed "most" of it...
#Update: f, K large enough, this wins. Need bounds...

function norm_mod(f::PolyRingElem{AbsSimpleNumFieldElem}, p::Int, Zx::ZZPolyRing = Globals.Zx)
  K = base_ring(f)
  k = Native.GF(p)
  s = 0
  while iszero(coeff(f, s))
    s += 1
  end
  if !iszero(s)
    f = shift_right(f, s)
  end
  me = modular_init(K, p)
  t = modular_proj(f, me)
  n = degree(f)*degree(K)
  v = Vector{fpFieldElem}(undef, n)
  first = true
  for i = 1:length(t)
    t1 = polynomial_to_power_sums(t[i]*inv(leading_coefficient(t[i])), n)
    for j = 1:length(t1)
      el = k(coeff(trace(t1[j]), 0))
      if first
        v[j] = el
      else
        v[j] += el
      end
    end
    first = false
  end
  nl = norm(leading_coefficient(f))
  pol = power_sums_to_polynomial(v)*numerator(nl)*invmod(denominator(nl), ZZRingElem(p))
  if !iszero(s)
    pol = shift_left(pol, s*degree(K))
  end
  return lift(Zx, pol)
end

function norm_mod(f::PolyRingElem{AbsSimpleNumFieldElem}, Zx::ZZPolyRing = Globals.Zx)
  #assumes, implicitly, the coeffs of f are algebraic integers.
  # equivalently: the norm is integral...
  p = p_start
  K = base_ring(f)

  g = Zx(0)
  d = ZZRingElem(1)

  stable = 0
  while true
    p = next_prime(p)
    tt = norm_mod(f, p, Zx)
    prev = g
    if isone(d)
      g = tt
      d = ZZRingElem(p)
    else
      g, d = induce_crt(g, d, tt, ZZRingElem(p), true)
    end
    if prev == g
      stable += 1
      if stable > 4
        return g
      end
    else
      stable = 0
    end
    if nbits(d) > 400000 #TODO: get a decent bound...
      error("too bad")
    end
  end
end

#=
  Daniel:
  let a_i be a linear recurrence sequence or better
    sum_1^infty a_i x^-i = -f/g is rational, deg f<deg g < n/2
    run rational reconstruction on h := sum_0^n a_i x^(n-i) and x^n
    finding bh = a mod x^n (h = a/b mod x^n)
    then b = g and f = div(a-bh, x^n)
    establishing the link between rat-recon and Berlekamp Massey

=#
