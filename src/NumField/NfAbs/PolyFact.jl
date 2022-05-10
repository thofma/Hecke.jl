abstract type Hensel end

mutable struct HenselCtxQadic <: Hensel
  f::PolyElem{qadic}
  lf::Vector{PolyElem{qadic}}
  la::Vector{PolyElem{qadic}}
  p::qadic
  n::Int
  #TODO: lift over subfields first iff poly is defined over subfield
  #TODO: use flint if qadic = padic!!
  function HenselCtxQadic(f::PolyElem{qadic}, lfp::Vector{fq_nmod_poly})
    @assert sum(map(degree, lfp)) == degree(f)
    Q = base_ring(f)
    Qx = parent(f)
    K, mK = ResidueField(Q)
    i = 1
    la = Vector{PolyElem{qadic}}()
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
    return new(f, map(x->setprecision(map_coefficients(y->preimage(mK, y), x, cached = false, parent = Qx), 1), lfp), la, uniformizer(Q), n)
  end

  function HenselCtxQadic(f::PolyElem{qadic})
    Q = base_ring(f)
    K, mK = ResidueField(Q)
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
  @vprint :PolyFactor 1 "using lifting chain $ch\n"
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
  f::PolyElem{padic}
  function HenselCtxPadic(f::PolyElem{padic})
    r = new()
    r.f = f
    Zx = PolynomialRing(FlintZZ, cached = false)[1]
    ff = Zx()
    for i=0:degree(f)
      setcoeff!(ff, i, lift(coeff(f, i)))
    end
    r.X = HenselCtx(ff, prime(base_ring(f)))
    start_lift(r.X, 1)
    return r
  end
end

function lift(C::HenselCtxPadic, mx::Int)
  for i=0:degree(C.f)
    setcoeff!(C.X.f, i, lift(coeff(C.f, i)))
  end
  continue_lift(C.X, mx)
end

function factor(C::HenselCtxPadic)
  res =  typeof(C.f)[]
  Zx = PolynomialRing(FlintZZ, cached = false)[1]
  h = Zx()
  Qp = base_ring(C.f)
  for i = 1:C.X.LF._num #from factor_to_dict
    #cannot use factor_to_dict as the order will be random (hashing!)
    g = parent(C.f)()
    ccall((:fmpz_poly_set, libflint), Nothing, (Ref{fmpz_poly}, Ref{fmpz_poly_raw}), h, C.X.LF.poly+(i-1)*sizeof(fmpz_poly_raw))
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

function div_preinv(a::fmpz, b::fmpz, bi::fmpz_preinvn_struct)
  q = fmpz()
  r = fmpz()
  fdiv_qr_with_preinvn!(q, r, a, b, bi)
  return q
end

@doc Markdown.doc"""
    round(::fmpz, a::fmpz, b::fmpz, bi::fmpz) -> fmpz

Computes `round(a//b)` using the pre-inverse of `2b`.
"""
function Base.round(::Type{fmpz}, a::fmpz, b::fmpz, bi::fmpz_preinvn_struct)
  s = sign(a)
  as = abs(a)
  r = s*div_preinv(2*as+b, 2*b, bi)
  @hassert :PolyFactor 1 abs(r - a//b) <= 1//2
#  @assert r == round(fmpz, a//b)
  return r
end

@doc Markdown.doc"""
    round(::fmpz, a::fmpz, b::fmpz) -> fmpz

Computes `round(a//b)`.
"""
function Base.round(::Type{fmpz}, a::fmpz, b::fmpz)
  s = sign(a)*sign(b)
  bs = abs(b)
  as = abs(a)
  r = s*div(2*as+bs, 2*bs)
#  @assert r == round(fmpz, a//b)
  return r
end

#TODO: think about computing pM[1][1,:]//pM[2] as a "float" approximation
#      to save on multiplications
function reco(a::fmpz, M, pM::Tuple{fmpz_mat, fmpz, fmpz_preinvn_struct}, O)
  m = map(x -> round(fmpz, a*x, pM[2], pM[3]), pM[1][1, :])*M
  return a - O(m)
end

function reco(a::fmpz, M, pM::Tuple{fmpz_mat, fmpz}, O)
  m = map(x -> round(fmpz, a*x, pM[2]), pM[1][1, :])*M
  return a - O(m)
end

function reco(a::NfAbsOrdElem, M, pM)
  m = matrix(FlintZZ, 1, degree(parent(a)), coordinates(a))
  m = m - map(x -> round(fmpz, x, pM[2]), m*pM[1])*M
  return parent(a)(m)
end

function is_prime_nice(O::NfOrd, p::Int)
  f = is_prime_nice(nf(O), p)
  f || return f
  if discriminant(O) %p == 0
    return false
  end
  return true
end

function is_prime_nice(K::AnticNumberField, p::Int)
  d = lcm(map(denominator, coefficients(K.pol)))
  if d % p == 0
    return false
  end
  F = GF(p)
  f = map_coefficients(F, d*K.pol)
  if degree(f) < degree(K)
    return false
  end
  if iszero(discriminant(f))
    return false
  end
  return true
end

@doc Markdown.doc"""
    factor_new(f::PolyElem{nf_elem}) -> Vector{PolyElem{nf_elem}}

Direct factorisation over a number field, using either Zassenhaus' approach
with the potentially exponential recombination or a van Hoeij like approach using LLL.
The decision is based on the number of local factors.
"""
function factor_new(f::PolyElem{nf_elem})
  k = base_ring(f)
  local zk::NfOrd
  if is_maximal_order_known(k)
    zk = maximal_order(k)
    if isdefined(zk, :lllO)
      zk = zk.lllO::NfOrd
    end
  else
    zk = any_order(k)
  end
  zk = lll(zk) # always a good option!
  p = degree(f)
  f *= lcm(map(denominator, coefficients(f)))
  np = 0
  bp = 1*zk
  br = 0
  s = Set{Int}()
  while true
    @vprint :PolyFactor 3 "Trying with $p\n "
    p = next_prime(p)
    if !is_prime_nice(zk, p)
      continue
    end
    P = prime_decomposition(zk, p, 1)
    if length(P) == 0
      continue
    end
    F, mF1 = ResidueFieldSmallDegree1(zk::NfOrd, P[1][1])
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
    @vprint :PolyFactor :3 "$s\n"

    if length(s) == 1
      return typeof(f)[f]
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
  @vprint :PolyFactor 1 "possible degrees: $s\n"
  if br < 5
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

@doc Markdown.doc"""
    zassenhaus(f::PolyElem{nf_elem}, P::NfOrdIdl; degset::Set{Int} = Set{Int}(collect(1:degree(f)))) -> Vector{PolyElem{nf_elem}}

Zassenhaus' factoring algorithm over an absolute simple field. Given a prime ideal $P$ which
has to be an unramified non-index divisor, a factorisation of $f$ in the $P$-adic completion
is computed. In the last step, all combinations of the local factors are tried to find the
correct factorisation.
$f$ needs to be square-free and square-free modulo $P$ as well.
"""
function zassenhaus(f::PolyElem{nf_elem}, P::NfOrdIdl; degset::Set{Int} = Set{Int}(collect(1:degree(f))))
  @vprint :PolyFactor 1 "Using (relative) Zassenhaus\n"

  K = base_ring(parent(f))
  C, mC = completion(K, P)

  b = landau_mignotte_bound(f)*upper_bound(fmpz, sqrt(t2(leading_coefficient(f))))
  den = K(1)
  if !is_maximal_known_and_maximal(order(P))
    if !is_defining_polynomial_nice(K)
      den = K(discriminant(order(P))*det(basis_matrix(order(P), copy = false)))
    else
      den = derivative(K.pol)(gen(K))
    end
    b *= upper_bound(fmpz, sqrt(t2(den)))
  end

  c1, c2 = norm_change_const(order(P))
  N = ceil(Int, degree(K)/2/log(norm(P))*(log2(c1*c2) + 2*nbits(b)))
  @vprint :PolyFactor 1 "using a precision of $N\n"

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
  av_bits = sum(nbits, vH.Ml)/degree(K)^2

  H = vH.H

  M = vH.Ml
  pM = vH.pMr

  lf = factor(H)
  zk = order(P)

  if degree(P) == 1
    S = Set(map(x -> map_coefficients(y -> lift(y), x, parent = parent(f)), lf))
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
Base.log2(a::fmpz) = log2(BigInt(a)) # stupid: there has to be faster way

global last_lf = Ref{Any}()
#given the local factorisation in H, find the cld, the Coefficients of the Logarithmic
#Derivative: a factor g of f is mapped to g'*f/g
#Only the coefficients 0:up_to and from:degree(f)-1 are computed
function cld_data(H::Hensel, up_to::Int, from::Int, mC, Mi, sc::nf_elem)
  lf = factor(H)
  a = preimage(mC, zero(codomain(mC)))
  k = parent(a)
  N = degree(H.f)
  @assert 0<= up_to <= N  #up_tp: modulo x^up_tp
  @assert 0<= from <= N   #from : div by x^from
#  @assert up_to <= from

  M = zero_matrix(FlintZZ, length(lf), (1+up_to + N - from) * degree(k))
  last_lf[] = (lf, H.f, up_to)

  lf = [divexact_low(mullow(derivative(x), H.f, up_to+1), x, up_to+1) for x = lf]
#  lf = [divexact(derivative(x)*H.f, x) for x = lf]
#  @show llf .- lf

  NN = zero_matrix(FlintZZ, 1, degree(k))
  d = FlintZZ()

  for i=0:up_to
    for j=1:length(lf)
      c = sc * preimage(mC, coeff(lf[j], i)) # should be an nf_elem
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
      c = sc * preimage(mC, coeff(lf[j], i)) # should be an nf_elem
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
  Ml::fmpz_mat
  pMr::Tuple{fmpz_mat, fmpz, fmpz_preinvn_struct}
  pM::Tuple{fmpz_mat, fmpz}
  C::Union{FlintQadicField, FlintPadicField}
  P::NfOrdIdl
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
  F = basis_mat_inv(order(vH.P)) * F
  vH.pM = (F.num, F.den)
end

global last_f = Ref{Any}()

function lll_with_removal_knapsack(x::fmpz_mat, b::fmpz, ctx::lll_ctx = lll_ctx(0.99, 0.51))
   z = deepcopy(x)
   d = Int(ccall((:fmpz_lll_wrapper_with_removal_knapsack, libflint), Cint,
    (Ref{fmpz_mat}, Ptr{nothing}, Ref{fmpz}, Ref{lll_ctx}), z, C_NULL, b, ctx))
   return d, z
end

function tdivpow2!(B::fmpz_mat, t::Int)
  ccall((:fmpz_mat_scalar_tdiv_q_2exp, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Cint), B, B, t)
end

function Nemo.tdivpow2(B::fmpz_mat, t::Int)
  C = similar(B)
  ccall((:fmpz_mat_scalar_tdiv_q_2exp, libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Cint), C, B, t)
  return C
end

function gradual_feed_lll(M::fmpz_mat, sm::fmpz, B::fmpz_mat, d::fmpz, bnd::fmpz)
  b = maximum(nbits, B)
  sc = max(0, b-55)

  while false && sc > 0
    BB = tdivpow2(B, sc)
    dd = tdivpow2(d, sc)
    MM = [M BB; zero_matrix(FlintZZ, ncols(B), ncols(M)) dd*identity_matrix(FlintZZ, ncols(B))]
    @show maximum(nbits, MM)
    @time MM, T = lll_with_transform(MM, lll_ctx(0.75, 0.51))
    @time l, _ = lll_with_removal(MM, bnd, lll_ctx(0.75, 0.51))
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


@doc Markdown.doc"""
    van_hoeij(f::PolyElem{nf_elem}, P::NfOrdIdl; prec_scale = 20) -> Vector{PolyElem{nf_elem}}

A van Hoeij-like factorisation over an absolute simple number field, using the factorisation in the
$P$-adic completion where $P$ has to be an unramified non-index divisor and the square-free $f$ has
to be square-free mod $P$ as well.

Approach is taken from Hart, Novacin, van Hoeij in ISSAC.
"""
function van_hoeij(f::PolyElem{nf_elem}, P::NfOrdIdl; prec_scale = 1)
  @vprint :PolyFactor 1 "Using (relative) van Hoeij\n"
  @vprint :PolyFactor 2 "with p = $P\n"
  @assert all(x->denominator(x) == 1, coefficients(f))

  K = base_ring(parent(f))
  C, mC = completion(K, P)

  zk = order(P)
  if is_maximal_known_and_maximal(zk)
    den = K(1)
  elseif is_defining_polynomial_nice(K)
    den = derivative(K.pol)(gen(K))
  else
    den = K(discriminant(order(P))) * det(basis_matrix(order(P), copy= false))
  end

  _, mK = ResidueField(order(P), P)
  mK = extend(mK, K)
  r = length(factor(map_coefficients(mK, f, cached = false)))
  N = degree(f)
  @vprint :PolyFactor 1  "Having $r local factors for degree $N \n"

  setprecision!(C, 5)

  vH = vanHoeijCtx()
  if degree(P) == 1
    vH.H = HenselCtxPadic(map_coefficients(x->coeff(mC(x), 0), f))
  else
    vH.H = HenselCtxQadic(map_coefficients(mC, f))
  end
  vH.C = C
  vH.P = P

  up_to = min(5, ceil(Int, N/20))
  up_to_start = up_to
  from = N-up_to  #use 5 coeffs on either end
  up_to = min(up_to, N)
  from = min(from, N)
  from = max(up_to, from)
  b = cld_bound(f, vcat(0:up_to-1, from:N-1)) .* upper_bound(fmpz, sqrt(t2(den*leading_coefficient(f))))

  # from Fieker/Friedrichs, still wrong here
  # needs to be larger than anticipated...
  c1, c2 = norm_change_const(order(P))
  b = Int[ceil(Int, degree(K)/2/log(norm(P))*(log2(c1*c2) + 2*nbits(x)+ degree(K)*r+prec_scale)) for x = b]
  bb = landau_mignotte_bound(f)*upper_bound(fmpz, sqrt(t2(den*leading_coefficient(f))))
  kk = ceil(Int, degree(K)/2/log(norm(P))*(log2(c1*c2) + 2*nbits(bb)))
  @vprint :PolyFactor 2 "using CLD precision bounds $b \n"

  used = []
  really_used = []
  M = identity_matrix(FlintZZ, r)*fmpz(2)^prec_scale

  while true #the main loop
    #find some prec
    #to start with, I want at least half of the CLDs to be useful
    if length(b) == degree(f)
      i = maximum(b) + 100
    else
      i= sort(b)[div(length(b)+1, 2)]
    end
    i = max(i, kk)
    @vprint :PolyFactor 1 "setting prec to $i, and lifting the info ...\n"
    setprecision!(codomain(mC), i)
    if degree(P) == 1
      vH.H.f = map_coefficients(x->coeff(mC(x), 0), f)
    else
      vH.H.f = map_coefficients(mC, f)
    end
    global last_vH = vH
    @vtime :PolyFactor 1 grow_prec!(vH, i)


    av_bits = sum(nbits, vH.Ml)/degree(K)^2
    @vprint :PolyFactor 1 "obtaining CLDs...\n"

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
      mD = MapFromFunc(x->coeff(mC(x),0), y->K(lift(y)), K, base_ring(vH.H.f))
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
    # if unlucky: re-do Hensel and start over again, hopefull retaining some info
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
      @vprint :PolyFactor 2 "trying to use coeff $n which is $i\n"
      if b[i] > precision(codomain(mC))
        @vprint :PolyFactor 2 "not enough precision for CLD $i, $b, $(precision(codomain(mC))), skipping\n"

#        error()
        continue
      end
      sz = floor(Int, degree(K)*av_bits/log(norm(P)) - b[i])

      B = sub(C, 1:r, (i-1)*degree(K)+1:i*degree(K))
#      @show i, maximum(nbits, B)

      T = sub(M, 1:nrows(M), 1:r)
      B = T*B   # T contains the prec_scale
      mod_sym!(B, vH.pM[2]*fmpz(2)^prec_scale)

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
      tdivpow2!(B, sz+prec_scale)
      d = tdivpow2(vH.pM[2], sz)

      bnd = r*fmpz(2)^(2*prec_scale) + degree(K)*(ncols(M)-r)*div(r, 2)^2

      rt = time_ns()
      @vtime :PolyFactor 1 l, Mi = gradual_feed_lll(M, fmpz(2)^prec_scale, B, d, bnd)
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
      d = Dict{fmpz_mat, Vector{Int}}()
      for l=1:r
        k = M[:, l]
        if haskey(d, k)
          push!(d[k], l)
        else
          d[k] = [l]
        end
      end
      @vprint :PolyFactor 1 "partitioning  of local factors: $(values(d))\n"
      if length(keys(d)) <= nrows(M)
        @vprint :PolyFactor 1  "BINGO: potentially $(length(keys(d))) factors\n"
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
              A = K(reco(order(P)(lift(a)), vH.Ml, vH.pMr))
            else
              A = K(reco(order(P)(preimage(mC, a)), vH.Ml, vH.pMr))
            end
            if denominator(divexact(constant_coefficient(f), A), order(P)) != 1
              @vprint :PolyFactor 2 "Fail: const coeffs do not divide\n"
              push!(fail, v)
              if length(fail) > 1
                break
              end
              continue
            end
          end
          @vtime :PolyFactor 2 g = prod(factor(vH.H)[v])
          if degree(P) == 1
            @vtime :PolyFactor 2 G = parent(f)([K(reco(lift(coeff(mC(den*leading_coefficient(f)), 0)*coeff(g, l)), vH.Ml, vH.pMr, order(P))) for l=0:degree(g)])
          else
            @vtime :PolyFactor 2 G = parent(f)([K(reco(order(P)(preimage(mC, mC(den*leading_coefficient(f))*coeff(g, l))), vH.Ml, vH.pMr)) for l=0:degree(g)])
          end
          G *= 1//(den*leading_coefficient(f))

          if !iszero(rem(f, G))
            @vprint :PolyFactor 2 "Fail: poly does not divide\n"
            push!(fail, v)
            if length(fail) > 1
              break
            end
            continue
          end
          push!(res, G)
        end
        if length(fail) == 1
          @vprint :PolyFactor 1 "only one reco failed, total success\n"
          push!(res, divexact(f, prod(res)))
          return res
        end
        if length(res) < length(d)
          @vprint :PolyFactor 1 "reco failed\n... here we go again ...\n"
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
      last_f[] = (f, P, vH)
      error("too bad")
    end
    used = deepcopy(really_used)

    b = cld_bound(f, vcat(0:up_to-1, from:N-1)) .* upper_bound(fmpz, sqrt(t2(den*leading_coefficient(f))))

    # from Fieker/Friedrichs, still wrong here
    # needs to be larger than anticipated...
    b = [ceil(Int, degree(K)/2/log(norm(P))*(log2(c1*c2) + 2*nbits(x)+ 2*prec_scale)) for x = b]
  end #the big while
end

function Base.map!(f, M::fmpz_mat)
  for i=1:nrows(M)
    for j=1:ncols(M)
      M[i,j] = f(M[i,j])
    end
  end
end

#does not seem to be faster than the direct approach. (not modular)
#Magma is faster, which seems to suggest the direct resultant is
#even better (modular resultant)
# power series over finite fields are sub-par...or at least this usage
# fixed "most" of it...
#Update: f, K large enough, this wins. Need bounds...

function norm_mod(f::PolyElem{nf_elem}, p::Int, Zx::FmpzPolyRing = Globals.Zx)
  K = base_ring(f)
  k = GF(p)
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
  v = Vector{gfp_elem}(undef, n)
  first = true
  for i = 1:length(t)
    t1 = polynomial_to_power_sums(t[i], n)
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
  pol = power_sums_to_polynomial(v)
  if !iszero(s)
    pol = shift_left(pol, s*degree(K))
  end
  return lift(Zx, pol)
end

global _debug = []

function norm_mod(f::PolyElem{nf_elem}, Zx::FmpzPolyRing = Globals.Zx)
  #assumes, implicitly, the coeffs of f are algebraic integers.
  # equivalently: the norm is integral...
  p = p_start
  K = base_ring(f)

  g = Zx(0)
  d = fmpz(1)

  stable = 0
  while true
    p = next_prime(p)
    tt = norm_mod(f, p, Zx)
    prev = g
    if isone(d)
      g = tt
      d = fmpz(p)
    else
      g, d = induce_crt(g, d, tt, fmpz(p), true)
    end
    if prev == g
      stable += 1
      if stable > 4
        return g
      end
    else
      stable = 0
    end
    if nbits(d) > 20000
      push!(_debug, f)
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
