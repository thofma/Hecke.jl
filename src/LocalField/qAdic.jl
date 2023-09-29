add_verbosity_scope(:qAdic)
add_assertion_scope(:qAdic)

export defining_polynomial

@attributes FlintQadicField

function residue_field(Q::FlintQadicField)
  z = get_attribute(Q, :ResidueFieldMap)
  if z !== nothing
    return codomain(z), z
  end
  Fp = Native.GF(Int(prime(Q)))
  Fpt = polynomial_ring(Fp, cached = false)[1]
  g = defining_polynomial(Q) #no Conway if parameters are too large!
  f = Fpt([Fp(lift(coeff(g, i))) for i=0:degree(Q)])
  k = Native.finite_field(f, "o", cached = false)[1]
  pro = function(x::qadic)
    v = valuation(x)
    v < 0 && error("elt non integral")
    v > 0 && return k(0)
    z = k()
    for i=0:degree(Q)
      setcoeff!(z, i, UInt(lift(coeff(x, i))%prime(Q)))
    end
    return z
  end
  lif = function(x::fqPolyRepFieldElem)
    z = Q()
    for i=0:degree(Q)-1
      setcoeff!(z, i, coeff(x, i))
    end
    return z
  end
  mk = MapFromFunc(Q, k, pro, lif)
  set_attribute!(Q, :ResidueFieldMap => mk)
  return k, mk
end

function residue_field(Q::FlintPadicField)
  k = Native.GF(Int(prime(Q)))
  pro = function(x::padic)
    v = valuation(x)
    v < 0 && error("elt non integral")
    v > 0 && return k(0)
    z = k(lift(x))
    return z
  end
  lif = function(x::fpFieldElem)
    z = Q(lift(x))
    return z
  end
  return k, MapFromFunc(Q, k, pro, lif)
end

coefficient_field(Q::FlintQadicField) = coefficient_ring(Q)

function getUnit(a::padic)
  u = ZZRingElem()
  ccall((:fmpz_set, libflint), Cvoid, (Ref{ZZRingElem}, Ref{Int}), u, a.u)
  return u, a.v, a.N
end

function lift_reco(::QQField, a::padic; reco::Bool = false)
  if reco
    u, v, N = getUnit(a)
    R = parent(a)
    fl, c, d = rational_reconstruction(u, prime(R, N-v))
    !fl && return nothing

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


uniformizer(Q::FlintQadicField) = Q(prime(Q))

uniformizer(Q::FlintPadicField) = Q(prime(Q))

function defining_polynomial(Q::FlintQadicField, P::Ring = coefficient_ring(Q))
  Pt, t = polynomial_ring(P, cached = false)
  f = Pt()
  for i=0:Q.len-1
    j = unsafe_load(reinterpret(Ptr{Int}, Q.j), i+1)
    a = ZZRingElem()
    ccall((:fmpz_set, libflint), Nothing, (Ref{ZZRingElem}, Int64), a, Q.a+i*sizeof(Ptr))
    setcoeff!(f, j, P(a))
  end
  return f
end
