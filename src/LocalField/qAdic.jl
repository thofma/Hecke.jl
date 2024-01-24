add_verbosity_scope(:qAdic)
add_assertion_scope(:qAdic)

@attributes FlintQadicField

function residue_field(Q::FlintQadicField)
  z = get_attribute(Q, :ResidueFieldMap)
  if z !== nothing
    return codomain(z), z
  end
  Fp = GF(prime(Q))
  Fpt = polynomial_ring(Fp, cached = false)[1]
  g = defining_polynomial(Q) #no Conway if parameters are too large!
  f = Fpt([Fp(lift(coeff(g, i))) for i=0:degree(Q)])
  k, = Nemo._residue_field(f, "o")
  pro = function(x::qadic)
    v = valuation(x)
    v < 0 && error("elt non integral")
    v > 0 && return k(0)
    _z = Fpt()
    for i=0:degree(Q)
      setcoeff!(_z, i, Fp(lift(coeff(x, i))))
    end
    return k(_z)
  end
  lif = function(x::FqFieldElem)
    z = Q()
    for i=0:degree(Q)-1
      setcoeff!(z, i, lift(ZZ, coeff(x, i)))
    end
    return z
  end
  mk = MapFromFunc(Q, k, pro, lif)
  set_attribute!(Q, :ResidueFieldMap => mk)
  return k, mk
end

function residue_field(Q::FlintPadicField)
  k = GF(prime(Q))
  pro = function(x::padic)
    v = valuation(x)
    v < 0 && error("elt non integral")
    v > 0 && return k(0)
    z = k(lift(x))
    return z
  end
  lif = function(x::FqFieldElem)
    z = Q(lift(ZZ, x))
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
