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
  function pAdic_root_ctx(K::AnticNumberField, p::Int)
    d = Dict{Int, pAdic_root_ctx}()
    try 
      d = _get_nf_conjugate_data_pAdic(K)
    catch e
      #check proper type of e
    end

    if isdefined(d, p)
      return d[p]
    end

    r = new()
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
  assure_precision(r, n)
  c = []
  Zx = PolynomialRing(FlintZZ, cached = false)[1]
  for C = r.Q
    b = Zx(a*denominator(a))
    x = C(r.Qpt(b))
    di = invmod(denominator(a), r.pN)
    x *= di
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
  for i=2:n ## not far enough for small primes. Nor sure about the signs
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
function conjugates_pAdic_log(a::nf_elem, p::Int, n::Int = 10; normalise::Bool = false)
  c = conjugates_pAdic(a, p, n, orbit = false)
  l = []
  for x = c
    xx = 1
    if normalise  # works - but removes precision, thus is dangerous...
      v = _valuation(x)
      if v != 0
        xx = deepcopy(x)
        for i=0:degree(xx.data)
          setcoeff!(xx.data, i, coeff(xx.data, i)//prime(R, v))
        end
      else
        xx = x
      end
    else
      xx = x
    end
    y = _log(xx)
    for i=0:degree(modulus(parent(xx)))-1
      push!(l, coeff(y.data, i))
    end
  end
  return matrix(parent(l[1]), 1, length(l), l) 
end
#TODO: caching padic logs in the number field?
#TODO: adjust the precision downwards

function conjugates_pAdic_log(a::FacElem{nf_elem, AnticNumberField}, p::Int, n::Int = 10)
  l = 1
  for (k, v) = a.fac
    if l === 1
      l = v*conjugates_pAdic_log(k, p, n, normalise=true)
    else
      l += v*conjugates_pAdic_log(k, p, n, normalise=true)
    end
  end
  return l
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
    fl, c, d = rational_reconstruction(u, prime(R, N))
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

function mult_syzygies_units(a::Array{FacElem{nf_elem, AnticNumberField}, 1})
  p = next_prime(2^10) #experimentally, the runtime is dominated by
         # log which in case is dominated by the a^(p^n-1) in the 1st step
         # thus try p smaller..., ideally also try n smaller...
         # also, see comments at _log
  u = FacElem{nf_elem, AnticNumberField}[]
  la = [conjugates_pAdic_log(e, p, 30) for e = a] #can loose precision
    # needs to be traced
    # precision needs to be updated.  
  n = cols(la[1])
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
        Dombrowski. Hence this can be evaluated with low precision.

        Not done.
      =#  
      @assert reduce(gcd, gamma) == 1 # should be a primitive relation
      _, U = hnf_with_trafo(matrix(FlintZZ, length(r), 1, gamma))
      U = inv(U)  
      U = sub(U, 1:rows(U), 2:cols(U))
      #new basis is the cols of U
      push!(u, a[i])
      u = Hecke._transform(u, U)
      lu = U'*lv
    end
  end
  return u
end


function non_torsion_lower_bound(R::NfOrd, B::Int = 2*degree(R))
  L = Hecke.enum_ctx_from_ideal(1*R, zero_matrix(FlintZZ, 0, 0))
  n = degree(R)
  i = B
  while true
    #lat enum is wrong. Or maybe rounding funnily:
    # try on wildanger_field(13, 17) and observe the vectors found...
    @show s = Hecke.enum_ctx_short_elements(L, i*L.d)
    if rows(s) > 5
      M = minimum([t2(R(collect(sub(s, i:i, 1:n)))) for i=1:rows(s)])
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
    e = [R(collect(sub(s, i:i, 1:n))) for i=1:rows(s)]
    u = [x for x in e if isunit(x)]
    if rows(s) > 5
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
