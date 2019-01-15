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

function frobenius_gen(R, e::Int = 1)
  Qpt = base_ring(R)
  Qp = base_ring(Qpt)
  p = Qp.p #TODO: this is wrong and not legally accessible
           #this is an fmpz, for julia an Int
  f = R.modulus
  #Frob is a lift of x -> x^(p^e) this is a root of f...
  fs = derivative(f)
  i = gen(R)^(fmpz(p)^e)
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

function _log(a)
  Qpt = base_ring(parent(a))
  Qp = base_ring(Qpt)
  #log a = log(1-(1-a))
  @assert _valuation(a) == 0
  ex = fmpz(Qp.p)^degree(modulus(parent(a))) -1
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
function conjugates_pAdic_log(a::nf_elem, p::Int, n::Int = 10; normalise::Bool = false)
  c = conjugates_pAdic(a, p, n, orbit = false)
  l = []
  for x = c
    xx = 1
    if normalise  # does not seem to work< can't see why
                  # works - but removes precision, thus is dangerous...
      v = _valuation(x)
      if v != 0
        xx = deepcopy(x)
        for i=0:degree(xx.data)
          setcoeff!(xx.data, i, coeff(xx.data, i)//p^v)
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

#now we could combine with MultDep and finish everything
# enough is enough

end
