module pAdicConj

#export conjugates_pAdic_log

#= XXX: qadics in flint: 
   defining polynomial needs to be conway (currently) as this is the only constructor
   code assumes always the def. poly is sparse and has small (<=p) coefficients
   (at least for performance)
   I don't know if this implies its pointless to use them?
   At least the general use in Hecke is not quite clear.
=#

using Hecke

function (O::Generic.PolyRing{padic})(f::fmpz_poly)
  g = O()
  R = base_ring(O)
  for i=0:length(f)
    Hecke.setcoeff!(g, i, R(coeff(f, i)))
  end
  return g
end

mutable struct pAdic_root_ctx  #TODO: parametrize to allow non-simples as well
  H::Hecke.HenselCtx
  prec::Int 
  Q#::Array{Generic.ResRing{fmpz_poly}, 1} #TODO: FlintQadicField (to be wrapped)
  pN::fmpz
  Qp::FlintPadicField
  Qpt
  cache::Dict{nf_elem, Array{Any, 1}}
  function pAdic_root_ctx(K::AnticNumberField, p::Int)
    d = Dict{Int, pAdic_root_ctx}()
    try 
      d = _get_nf_conjugate_data_pAdic(K)
      @show "usig old ctx"
    catch e
      #check proper type of e
      @show e
      _set_nf_conjugate_data_pAdic(K, d)
    end

    if haskey(d, p)
      return d[p]
    end

    r = new()
    @show "new r"
    zx, x = PolynomialRing(FlintZZ, cached = false)
    f = zx(K.pol * denominator(K.pol))
    r.H = Hecke.HenselCtx(f, fmpz(p))
    Hecke.start_lift(r.H, 10)
    r.prec = 10
    r.pN = fmpz(p)^10
    r.Qp = Hecke.FlintPadicField(p, 10)
    r.Qpt = PolynomialRing(r.Qp, cached = false)[1]

    d[p] = r
    s = Hecke.factor_to_dict(r.H.LF)
    r.Q = [ResidueRing(r.Qpt, r.Qpt(f)) for f = keys(s)]
    return r
  end
end

t = Hecke.create_accessors(AnticNumberField, Dict{Int, pAdic_root_ctx}, get_handle())
global _get_nf_conjugate_data_pAdic = t[1]
global _set_nf_conjugate_data_pAdic = t[2]

function assure_precision(r::pAdic_root_ctx, n::Int)
  if r.prec < n
    Hecke.continue_lift(r.H, n)
    r.prec = n
    s = Hecke.factor_to_dict(r.H.LF)
    #think: order may change as this is a dictionary
    p = r.Qp.p #see warning above
    r.pN = fmpz(p)^n
    r.Qp = Hecke.FlintPadicField(p, n)
    r.Qpt = PolynomialRing(r.Qp, cached = false)[1]
    s = Hecke.factor_to_dict(r.H.LF)
    r.Q = [ResidueRing(r.Qpt, r.Qpt(f)) for f = keys(s)]
  end
end

function Hecke.prime(R::PadicField, i::Int)
  p = fmpz()
  ccall((:padic_ctx_pow_ui, :libflint), Cvoid, (Ref{fmpz}, Int, Ref{PadicField}), p, i, R)
  return p
end

function frobenius_gen(R, e::Int = 1)
  Qpt = base_ring(R)
  Qp = base_ring(Qpt)
  f = R.modulus
  #Frob is a lift of x -> x^(p^e) this is a root of f...
  fs = derivative(f)
  i = gen(R)^prime(Qp, e)
  #@show methods(inv, (typeof(i), ))
  o = inv(fs(i))
  pr = 1
  #TODO: use a lifting chain and adjust the precision
  while pr < Qp.prec_max
    i = i-f(i)*o
    o *= (2-o*fs(i))
    parent(o) #julia bug: without this, it dies
    pr *= 2
  end
  return i
end

function frobenius(a, g = frobenius_gen(parent(a)))
  return a.data(g) # should be compose_mod
end

function conjugates_pAdic(a::nf_elem, p::Int, n::Int = 10; orbit::Bool = true)
  r = pAdic_root_ctx(parent(a), p)

  c = []
  assure_precision(r, n)
  Zx = PolynomialRing(FlintZZ, cached = false)[1]
  for C = r.Q
    b = Zx(a*denominator(a))
    x = C(r.Qpt(b)*inv(r.Qp(denominator(a))))
#    di = invmod(denominator(a), r.pN)
#    x *= di
    push!(c, x)
    if orbit
      g = frobenius_gen(parent(x))
      for i=2:degree(parent(x).modulus)
        push!(c, frobenius(c[end], g))
      end
    end
  end
  return c
end

#= log(x)' = 1/x
   1/(1-x) = sum_0 x^i
   log(1-x) = sum x^i/i
   =#
function _valuation(a)
  return minimum(valuation(coeff(a.data, i)) for i=0:degree(a.data))
end

#TODO/ ToThink
#  - if v_p(1-a) = l, then v_p((1-a)^p) = l+1, so
#    by raising to a power of p, the series converges faster
#    aparently, optimal is p^sqrt(prec)
#    if p >> 0, I don't think this is fast
#  - pari: 1/2 log((1+x)/(1-x)) = atanh(x), thus
#    1/2 log(x) = atanh((x-1)/(x+1))
#    atanh(x) = sum x^(2l+a)/(2l+a)
#    converges faster.
#  - evaluation via Brent-Kung rather than naive
#  - the sum is not long enough for small primes as the denominator
#    will have valuations
#  - needs to be optimized...
#  - maybe use Teichmueller lift instead of raising to the ?-1 st power:
#    a = tb for t the Teichmueller and b=1(pi)
#    in particular, t is torsion, hence log(t) = 1
#    There are non-trivial, fast(?) methods to compute t
#    The naive is t = a^((p^n)^prec) which is even worse...
function _log(a)
  Qpt = base_ring(parent(a))
  Qp = base_ring(Qpt)
  #log a = log(1-(1-a))
  @assert _valuation(a) == 0
  ex = prime(Qp, degree(modulus(parent(a)))) -1
  a = a^ex
  # .. this guarantees a equiv 1 mod p, hence the power series converges
  a = 1-a
  @assert all(x->valuation(coeff(a.data, x)) > 0, 0:degree(a.data))
  n = Qp.prec_max
  pa = a
  l = a
  i = 2
  z = ceil(Int, log(Int(prime(base_ring(a.data))), n))
  while any(j-> coeff(pa.data, j).v <= n, 0:degree(pa.data))
    pa *= a
    for j=0:degree(pa.data)
      c = coeff(pa.data, j)
      c.N = min(n+z, c.N)
    end
    l += pa*inv(Qp(i))
    i += 1
  end
  return l*inv(Qp(ex))
end

function _log2(a)
  Qpt = base_ring(parent(a))
  Qp = base_ring(Qpt)
  #log a = log(1-(1-a))
  @assert _valuation(a) == 0
  ex = prime(Qp, degree(modulus(parent(a)))) -1
  a = a^ex
  # .. this guarantees a equiv 1 mod p, hence the power series converges
  a = 1-a
  @assert all(x->valuation(coeff(a.data, x)) > 0, 0:degree(a.data))
  n = Qp.prec_max
  pa = a
  l = a
  for i=2:n
    pa *= a
    l += pa*inv(Qp(i))
  end
  return l*inv(Qp(ex))
end


#= XXX: this takes only one value for each completion and returns the coeff vec
#     is this enough or do I need to work in a splitting field??
  Yep: we should use log(u^(1)) ... log(u^(n)) for all conjugates, but
    log commutes with frob and thus any relation in the (say) 1st conjugate automatically
    implies one (via frob) for the second
    We are looking for the Qp-rank, NOT the q-adic one!
    This is so neat!
=#
function _conjugates_pAdic_log(a::nf_elem, p::Int, n::Int = 10; normalise::Bool = false)
  r = 1
  try
    s = _get_nf_conjugate_data_pAdic(parent(a))
    if haskey(s, p)
      r = s[p]
    end
    if !isdefined(r, :cache)
      @show "create cache 1"
      r.cache = Dict{nf_elem, Array{Any, 1}}()
    end

    if haskey(r.cache, a)
      la = r.cache[a]
      if precision(coeff(la[1].data, 0)) >= n
        @show "retrieve"
        return la
      end
      @show "bad"
    else
      @show "new elt"
    end
  catch t
    @show "errror 1", t
  end
  c = conjugates_pAdic(a, p, n, orbit = false)
  if normalise && any(x -> _valuation(x) != 0, c)
    lp = prime_decomposition(maximal_order(parent(a)), p)
    b = prod([p[1].gen_two^valuation(a, p[1]) for p = lp])
    a *= inv(elem_in_nf(b))
    c = conjugates_pAdic(a, p, n, orbit = false)
  end
  l = []
  for x = c
    y = _log(x)
    push!(l, y)
  end
  r = _get_nf_conjugate_data_pAdic(parent(a))[p]
  if !isdefined(r, :cache)
    @show "create cache 2"
    r.cache = Dict{nf_elem, Array{Any, 1}}()
  end
  r.cache[a] = l
  return l
end

function conjugates_pAdic_log(a::nf_elem, p::Int, n::Int = 10; normalise::Bool = false)
  d = _conjugates_pAdic_log(a, p, n, normalise = normalise)
  l = []
  for y = d
    for i=0:degree(modulus(parent(y)))-1
      push!(l, coeff(y.data, i))
    end
  end
  return matrix(parent(l[1]), 1, length(l), l) 
end
#TODO: caching padic logs in the number field?
#TODO: adjust the precision downwards

function conjugates_pAdic_log(a::FacElem{nf_elem, AnticNumberField}, p::Int, n::Int = 10)
  l = 1
  #if facelem is a (s) unit coprime to p, then one can/ could/should deal with
  #valuations differently: mult by suitable valuation elements - their
  #contribution must cancel
  #done
  for (k, v) = a.fac
    if l === 1
      l = v*conjugates_pAdic_log(k, p, n, normalise=true)
    else
      l += v*conjugates_pAdic_log(k, p, n, normalise=true)
    end
  end
  return l
end

#not working, no exp...
function conjugates_pAdic(a::FacElem{nf_elem, AnticNumberField}, p::Int, n::Int = 10)
  
  #if facelem is a (s) unit coprime to p, then one can/ could/should deal with
  #valuations differently: mult by suitable valuation elements - their
  #contribution must cancel
  #done
  l = _conjugates_pAdic_log(base_ring(a)(1), p, n, normalise = true)
  for (k, v) = a.fac
    iszero(v) && continue
    if l === 1
      l = v*_conjugates_pAdic_log(k, p, n, normalise=true)
    else
      l += v*_conjugates_pAdic_log(k, p, n, normalise=true)
    end
  end
  return [_exp(x) for x = l]
end


function conjugates_pAdic_log(a::NfOrdElem, p::Int, n::Int = 10)
  return conjugates_pAdic_log(a.elem_in_nf, p, 10)
end


#TODO: new name!
function getUnit(a::padic)
  u = fmpz()
  ccall((:fmpz_set, :libflint), Cvoid, (Ref{fmpz}, Ref{Int}), u, a.u)
  return u, a.v, a.N
end

function lift_reco(::FlintRationalField, a::padic; reco::Bool = false)
  if reco
    u, v, N = getUnit(a)
    R = parent(a)
    fl, c, d = rational_reconstruction(u, prime(R, N-v))
    !fl && return false
    if false && 2*max(nbits(c), nbits(d)) > nbits(prime(R, N-v)) -20 #arbitrary 
      @show "bad"
      return false
    end
    @assert fl
    x = FlintQQ(c, d)
    if v < 0
      return x//prime(R, -v)
    else
      return x*prime(R, v)
    end
  else
    return lift(FlintQQ, a)
  end
end

function Hecke.FlintZZ(x::Rational{Int})
  @assert denominator(x) == 1
  return fmpz(numerator(x))
end

import Base.*

function *(A::fmpz_mat, B::MatElem{padic})
  return matrix(base_ring(B), A) * B
end

#= kept for the comments

function mult_syzygies_units(a::Array{FacElem{nf_elem, AnticNumberField}, 1})
  p = next_prime(2^10) #experimentally, the runtime is dominated by
         # log which in case is dominated by the a^(p^n-1) in the 1st step
         # thus try p smaller..., ideally also try n smaller...
         # also, see comments at _log
  u = FacElem{nf_elem, AnticNumberField}[]
  la = [conjugates_pAdic_log(e, p, 300) for e = a] #can loose precision
    # needs to be traced
    # precision needs to be updated.  
  n = ncols(la[1])
  Qp = base_ring(la[1])
  lu = matrix(Qp, 0, n, [])
  for i=1:length(la)
    if iszero(la[i])
      println("torsino at $i\n")
      continue
    end
    lv = vcat(lu, la[i])
    k = Hecke.left_kernel(lv)
    @assert length(k) < 2
    if length(k) == 0
      println("new at $i")
      push!(u, a[i])
      lu = vcat(lu, la[i])
    else # length == 1 extend the module
      r = [lift_reco(FlintQQ, x, reco = true) for x = k[1]]
      #lift can fail if precision wrong.
      #or at least result is (can be) garbage
      #= bound on relation
        u has s independent units (independence is failproof p-adically)
        v is new and (probably, up to verification of the relation) dependent
        Then <u, v> = <e_1, .., e_s> where the e_'s are unknown.
        we have u = U(e_1, ..., e_n) for U in Z^(s x s)
                v = V(e_1, ..., e_n) vor V in Z^(1 x s)
        Over Q: v = x(u_1, ..., u_s) thus
            V(e_1, ..., e_s) = xU(e_1, ..., e_s)
        and, since the e_i are independent
            V = xU
        Cramer's rule
            x_i = det(U_1, ..., U_i-1, V, ... U_s) / det(U)
        and we need bounds for the determinants.
        As an example, det U
        det U = <e_1, ..., e_s> : <u_1, ..., u_s>
        and using universal lower bounds on the size of units (Dobrowski)
        and the successive minimal, we can get a lower bound on the 
        regulator of <e_i>. Hadramat gives an upper bound on reg(<u_i>)
        (regulator in the sence of lattice disciminant)

        Think: can we use the p-adic regulator to help???
               possibly increase precision until we either have
               indepence or a relation 
               ignore bounds?
      =#  
      d = reduce(lcm, map(denominator, r))
      gamma = [FlintZZ(x*d) for x = r] 
      #technically, this relations needs to be verified.
      #=
        we have a relation mod p^k, which means
          e = prod gamma[i]*u[i]
        has all logarithms == 0 mod p^k
        which should mean Norm(e) = product of the local norms
                                  = prod of exp(trace(components))
        For p large enough (larger than precision),
        val(exp(x)) = val(1-x) I think
        so
                                  >= p^(k* # primes) = p^l
        Now, either e is torsion (ie. logs identically 0) or
        not, but then arithmetic means:
        N(e) <= (T_2(e)^(1/2)/n)^n
        implies a non-trivial lower bound on the T_2:
        T_2(e) >= (np^(l/n))^2 =: B
        If T_2(e) < B, then e is torsion. B is MUCH larger than
        Dobrowski. Hence this can be evaluated with low precision.

        Not done.
      =#  
      @assert reduce(gcd, gamma) == 1 # should be a primitive relation
      _, U = hnf_with_trafo(matrix(FlintZZ, length(r), 1, gamma))
      U = inv(U)  
      U = sub(U, 1:nrows(U), 2:ncols(U))
      #new basis is the cols of U
      push!(u, a[i])
      u = Hecke._transform(u, U)
      lu = U'*lv
    end
  end
  return u
end

=#

function verify_gamma(a::Array{FacElem{nf_elem, AnticNumberField}, 1}, g::Array{fmpz, 1}, v::fmpz)
  #knowing that sum g[i] log(a[i]) == 0 mod v, prove that prod a[i]^g[i] is
  #torsion
  #= I claim N(1-a) > v^n for n the field degree:
   Let K be one of the p-adic fields involved, set b = a^g
   then log(K(b)) = 0 (v = p^l) by assumption
   so val(log(K(b))) >= l, but
   val(X) = 1/deg(K) val(norm(X)) for p-adics
   This is true for all completions involved, and sum degrees is n
 =#

  t = prod([a[i]^g[i] for i=1:length(a)])
  # t is either 1 or 1-t is large, norm(1-t) is div. by p^ln
  #in this case T2(1-t) is large, by the arguments above: T2>= (np^l)^2=:B
  # and, see the bottom, \|Log()\|_2^2 >= 1/4 arcosh((B-2)/2)^2
  B = ArbField(nbits(v)*2)(v)^2
  B = 1/2 *acosh((B-2)/2)^2
  p = Hecke.upper_bound(log(B)/log(parent(B)(2)), fmpz)
  b = conjugates_arb_log(t, -Int(p))
  global res = (B, b, t)
  @show (B > sum(x*x for x = b)) == istorsion_unit(t)[1]
  @assert (B > sum(x*x for x = b)) == istorsion_unit(t)[1]
  return B > sum(x*x for x = b)
end

function Base.setprecision(a::padic, N::Int)
  b = deepcopy(a)
  b.N = N
  @assert precision(b) == N
  return b
end

function mult_syzygies_units(A::Array{FacElem{nf_elem, AnticNumberField}, 1})
  p = next_prime(106) #experimentally, the runtime is dominated by
         # log which in case is dominated by the a^(p^n-1) in the 1st step
         # thus try p smaller..., ideally also try n smaller...
         # also, see comments at _log
  p = 10429       
  u = FacElem{nf_elem, AnticNumberField}[]
  prec = 10  #needs to match the 10 used in the creation of the 
             #ctx.
             #or prec needs to be honored and downwards corrected
  r1, r2 = signature(base_ring(parent(A[1])))
  r = r1+r2 -1
  n = degree(base_ring(parent(A[1])))
  la = conjugates_pAdic_log(A[1], p, prec)
  lu = zero_matrix(base_ring(la), 0, n)
  uu = []
  for a = A
    while true
      la = conjugates_pAdic_log(a, p, prec)
      if iszero(la)
        @assert verify_gamma([a], [fmpz(1)], fmpz(p)^prec)
        println("torsion found")
        break
      end
      lv = vcat(lu, la)
      #check_precision and change
      if false && any(x->precision(x) < prec, lv)
        println("loss of precision - not sure what to do")
        for i=1:rows(lv)
          for j = cols(lv) #seems to not do anything
            lv[i, j] = setprecision(lv[i, j], min_p)
            @assert precision(lv[i,j]) == min_p
          end
        end
      end
      k = Hecke.left_kernel(lv)
      @assert length(k) < 2
      if length(k) == 0
        println("new ")
        push!(u, a)
        lu = vcat(lu, la)
        @assert length(u) <= r
      else # length == 1 extend the module
        @show s = [lift_reco(FlintQQ, x, reco = true) for x = k[1]]
        if any(x -> x === false, s)
          prec *= 2
          @show "increase prec to ", prec
          lu = vcat([conjugates_pAdic_log(x, p, prec) for x = u])
          continue
        end
        d = reduce(lcm, map(denominator, s))
        gamma = [FlintZZ(x*d) for x = s] 
        @assert reduce(gcd, gamma) == 1 # should be a primitive relation
        if !verify_gamma(push!(copy(u), a), gamma, fmpz(p)^prec)
          prec *= 2
          @show "increase prec to ", prec
          lu = vcat([conjugates_pAdic_log(x, p, prec) for x = u])
          continue
        end
        @assert length(gamma) == length(u)+1
        gamma = vcat(gamma[1:length(u)], [0 for i=length(u)+1:r+length(uu)], [gamma[end]])
        push!(uu, (a, gamma))
      end
      break
    end
  end
  #=
    let u_1, .., u_n be units and
       <u_i | i> has rank s and 
        r_i in Z^n be such that
          prod u_i^r_i = 1  (OK, sum of the logs is zero)
          rank <r_i | i> = s as well
    so the r_i form a Q-basis for the relations.
    Essentially, the gamma of above are the r_i
    Let [H|0] = [r_i|i]*T be the hnf with trafo, so T in Gl(n, Z)
    Then
      <u_i|i> = <[u_i|i] T>
      [r_i|i] * [u_i|i]^t = 0 (by construction)
      [r_i|i] T inv(T) [u[i] | i] = 0
      [H | 0]   [v_i | i] = 0
      so, since H is triangular(!!) v_1, ... v_n-s = 0
      and <u_i |i> = <v_n-s+1, ..., v_n>
    
    for the case of n=s+1 this is mostly the "normal" construction.
    Note: as a side, the relations do not have to be primitive.
      If they are, (and n=s+1), then H = 1
  =#

  for i=1:length(uu)-1
    append!(uu[i][2], zeros(FlintZZ, length(uu[end][2])-length(uu[i][2])))
  end
  U = matrix(FlintZZ, length(uu), length(uu[end][2]), reduce(vcat, [x[2] for x = uu]))
  _, U = hnf_with_trafo(U')
  if false
    U = inv(U)
    V = sub(U, 1:rows(U), 1:cols(U)-length(u))
    U = sub(U, 1:rows(U), cols(U)-length(u)+1:cols(U))
    #U can be reduced modulo V...
    Z = zero_matrix(FlintZZ, cols(V), cols(U))
    I = identity_matrix(FlintZZ, cols(U)) * p^(2*prec)
    k = base_ring(A[1])
    A = [ Z V'; I U']
    l = lll(A)
    U = sub(l, cols(V)+1:rows(l), cols(U)+1:cols(l))
    U = lll(U)
  else
    U = lll(U')
  end
  return Hecke._transform(vcat(u, FacElem{nf_elem,AnticNumberField}[FacElem(k(1)) for i=length(u)+1:r], [x[1] for x = uu]), U')
end


function non_torsion_lower_bound(R::NfOrd, B::Int = 2*degree(R))
  L = Hecke.enum_ctx_from_ideal(1*R, zero_matrix(FlintZZ, 0, 0))
  n = degree(R)
  i = B
  while true
    #lat enum is wrong. Or maybe rounding funnily:
    # try on wildanger_field(13, 17) and observe the vectors found...
    # in particular 1 is not (reliably) found
    @show s = Hecke.enum_ctx_short_elements(L, i*L.d)
    #remove torsion
    if nrows(s) > 5
      M = minimum([t2(R(collect(sub(s, i:i, 1:n)))) for i=1:nrows(s)])
      j = n-2
      return (n-j)/4*acosh((M-j)/(n-j))^2
    end
    @show i += 1
  end
end

function unit_lower_bound(R::NfOrd, B::Int = 2*degree(R))
  L = Hecke.enum_ctx_from_ideal(1*R, zero_matrix(FlintZZ, 0, 0))
  n = degree(R)
  i = B
  while true
    s = Hecke.enum_ctx_short_elements(L, i*L.d)
    #remove torsion!!! now that \pm 1 is actually found
    e = [R(collect(sub(s, i:i, 1:n))) for i=1:nrows(s)]
    u = [x for x in e if isunit(x)]
    if nrows(s) > 5
      if length(u) == 0
        R = parent(t2(e[1]))
        @show M = R(i)
      else
        @show M = minimum([t2(x) for x = u])
      end
      j = n-2
      return (n-j)/4*acosh((M-j)/(n-j))^2, u
    end
    @show i += 1
  end
end


function regulator_lower_bound(R::NfOrd, B::Int = 2*degree(R))
  Ms, _ = unit_lower_bound(R, B)
  r1, r2 = signature(R)
  r = r1+r2-1
  n = degree(R) 
  return Ms^r * 2^r2 /n / Hecke.hermite_constant(r)
end

end
