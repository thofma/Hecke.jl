const FacElemQ = Union{FacElem{QQFieldElem, QQField}, FacElem{ZZRingElem, ZZRing}}

@doc raw"""
    evaluate(x::FacElem{QQFieldElem}) -> QQFieldElem
    evaluate(x::FacElem{ZZRingElem}) -> ZZRingElem

Expands or evaluates the factored element, i.e. actually computes the
the element.
Works by first obtaining a simplified version of the power product
into coprime base elements.
"""
function evaluate(x::FacElem{QQFieldElem})
  return evaluate_naive(simplify(x))
end

function evaluate(x::FacElem{ZZRingElem})
  return evaluate_naive(simplify(x))
end
@doc raw"""
    simplify(x::FacElem{QQFieldElem}) -> FacElem{QQFieldElem}
    simplify(x::FacElem{ZZRingElem}) -> FacElem{ZZRingElem}

Simplfies the factored element, i.e. arranges for the base to be coprime.
"""
function simplify(x::FacElem{QQFieldElem})
  y = deepcopy(x)
  simplify!(y)
  return y
end

function simplify(x::FacElem{ZZRingElem})
  y = deepcopy(x)
  simplify!(y)
  return y
end

function simplify!(x::FacElem{QQFieldElem})
  if length(x.fac) <= 1
    return nothing
  end
  cp = vcat([denominator(y) for (y, v) in x if !iszero(v)], [numerator(y) for (y, v) in x if !iszero(v)])
  ev = Dict{QQFieldElem, ZZRingElem}()
  if isempty(cp)
    ev[QQFieldElem(1)] = 0
    x.fac = ev
    return nothing
  end
  cp = coprime_base(cp)
  for p = cp
    if p == 1 || p == -1
      continue
    end
    v = ZZRingElem(0)
    for (b, vb) in x
      if !iszero(vb)
        v += valuation(b, abs(p))*vb
      end
    end
    if v != 0
      ev[QQFieldElem(abs(p))] = v
    end
  end
  f = b -> b < 0 && isodd(x.fac[b]) ? -1 : 1
  s = prod((f(v) for v in base(x)))
  if s == -1
    ev[QQFieldElem(-1)] = 1
  else
    if length(ev) == 0
      ev[QQFieldElem(1)] = 0
    end
  end
  x.fac = ev
  return nothing
end

function simplify!(x::FacElem{ZZRingElem})
  if length(x.fac) == 0
    x.fac[ZZRingElem(1)] = 0
    return
  end
  if length(x.fac) <= 1
    k,v = first(x.fac)
    if isone(k)
      x.fac[k] = 0
    elseif k == -1
      if isodd(v)
        x.fac[k] = 1
      else
        delete!(x.fac, k)
        x.fac[ZZRingElem(1)] = 0
      end
    end
    return
  end
  cp = coprime_base(collect(base(x)))
  ev = Dict{ZZRingElem, ZZRingElem}()
  for p = cp
    if p == 1 || p == -1
      continue
    end
    v = ZZRingElem(0)
    for (b, vb) in x
      v += valuation(b, abs(p))*vb
    end
    if v < 0
      throw(DomainError(v, "Negative valuation in simplify!"))
    end
    if v != 0
      ev[abs(p)] = v
    end
  end
  f = b -> b < 0 && isodd(x.fac[b]) ? -1 : 1
  s = prod(f(v) for v in base(x))
  if s == -1
    ev[-1] = 1
  else
    if length(ev) == 0
      ev[ZZRingElem(1)] = 0
    end
  end
  x.fac = ev
  nothing
end

@doc raw"""
    isone(x::FacElem{QQFieldElem}) -> Bool
    isone(x::FacElem{ZZRingElem}) -> Bool
Tests if $x$ represents $1$ without an evaluation.
"""
function isone(x::FacElem{QQFieldElem})
  y = simplify(x)
  return all(iszero, values(y.fac)) || all(isone, keys(y.fac))
end

function isone(x::FacElem{ZZRingElem})
  y = simplify(x)
  return all(iszero, values(y.fac)) || all(isone, keys(y.fac))
end

@doc raw"""
    factor_coprime(x::FacElem{ZZRingElem}) -> Fac{ZZRingElem}
Computed a partial factorisation of $x$, ie. writes $x$ as a product
of pariwise coprime integers.
"""
function factor_coprime(x::FacElem{ZZRingElem})
  x = deepcopy(x)
  simplify!(x)
  d = Dict(abs(p) => Int(v) for (p,v) = x.fac)
  if haskey(d, ZZRingElem(-1))
    delete!(d, ZZRingElem(-1))
    return Fac(ZZRingElem(-1), d)
  else
    return Fac(ZZRingElem(1), d)
  end
end


function abs(A::FacElemQ)
  B = empty(A.fac)
  for (k,v) = A.fac
    ak = abs(k)
    add_to_key!(B, ak, v)
  end
  if length(B) == 0
    return FacElem(Dict(one(base_ring(A)) => ZZRingElem(1)))
  end
  return FacElem(B)
end

function ==(A::T, B::T) where {T <: FacElemQ}
  C = A*B^-1
  simplify!(C)
  return isone(C)
end

function isone(A::FacElemQ)
  C = simplify(A)
  return all(iszero, values(C.fac)) || all(isone, keys(C.fac))
end