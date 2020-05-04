const FacElemQ = Union{FacElem{fmpq, FlintRationalField}, FacElem{fmpz, FlintIntegerRing}}

@doc Markdown.doc"""
    evaluate(x::FacElem{fmpq}) -> fmpq
    evaluate(x::FacElem{fmpz}) -> fmpz

Expands or evaluates the factored element, i.e. actually computes the
the element. 
Works by first obtaining a simplified version of the power product
into coprime base elements.
"""
function evaluate(x::FacElem{fmpq})
  return evaluate_naive(simplify(x))
end

function evaluate(x::FacElem{fmpz})
  return evaluate_naive(simplify(x))
end
@doc Markdown.doc"""
    simplify(x::FacElem{fmpq}) -> FacElem{fmpq}
    simplify(x::FacElem{fmpz}) -> FacElem{fmpz}

Simplfies the factored element, i.e. arranges for the base to be coprime.
"""
function simplify(x::FacElem{fmpq})
  y = deepcopy(x)
  simplify!(y)
  return y
end

function simplify(x::FacElem{fmpz})
  y = deepcopy(x)
  simplify!(y)
  return y
end

function simplify!(x::FacElem{fmpq})
  if length(x.fac) <= 1
    return nothing
  end
  cp = vcat([denominator(y) for (y, v) in x if !iszero(v)], [numerator(y) for (y, v) in x if !iszero(v)])
  ev = Dict{fmpq, fmpz}()
  if isempty(cp)
    ev[fmpq(1)] = 0
    x.fac = ev
    return nothing
  end
  cp = coprime_base(cp)
  for p = cp
    if p == 1 || p == -1
      continue
    end
    v = fmpz(0)
    for (b, vb) in x
      if !iszero(vb)
        v += valuation(b, abs(p))*vb
      end
    end
    if v != 0
      ev[fmpq(abs(p))] = v
    end
  end
  f = b -> b < 0 && isodd(x.fac[b]) ? -1 : 1
  s = prod((f(v) for v in base(x)))
  if s == -1
    ev[fmpq(-1)] = 1
  else
    if length(ev) == 0
      ev[fmpq(1)] = 0
    end
  end
  x.fac = ev
  return nothing
end

function simplify!(x::FacElem{fmpz})
  if length(x.fac) == 0
    x.fac[fmpz(1)] = 0
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
        x.fac[fmpz(1)] = 0
      end
    end
    return
  end
  cp = coprime_base(collect(base(x)))
  ev = Dict{fmpz, fmpz}()
  for p = cp
    if p == 1 || p == -1
      continue
    end
    v = fmpz(0)
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
      ev[fmpz(1)] = 0
    end
  end
  x.fac = ev
  nothing
end

@doc Markdown.doc"""
    isone(x::FacElem{fmpq}) -> Bool
    isone(x::FacElem{fmpz}) -> Bool
Tests if $x$ represents $1$ without an evaluation.
"""
function isone(x::FacElem{fmpq})
  y = simplify(x)
  return all(iszero, values(y.fac)) || all(isone, keys(y.fac))
end

function isone(x::FacElem{fmpz})
  y = simplify(x)
  return all(iszero, values(y.fac)) || all(isone, keys(y.fac))
end

@doc Markdown.doc"""
    factor_coprime(x::FacElem{fmpz}) -> Fac{fmpz}
Computed a partial factorisation of $x$, ie. writes $x$ as a product
of pariwise coprime integers.
"""
function factor_coprime(x::FacElem{fmpz})
  x = deepcopy(x)
  simplify!(x)
  d = Dict(abs(p) => Int(v) for (p,v) = x.fac)
  if haskey(d, fmpz(-1))
    delete!(d, fmpz(-1))
    return Fac(fmpz(-1), d)
  else
    return Fac(fmpz(1), d)
  end
end


function abs(A::FacElemQ)
  B = empty(A.fac)
  for (k,v) = A.fac
    ak = abs(k)
    add_to_key!(B, ak, v)
  end
  if length(B) == 0
    return FacElem(Dict(one(base_ring(A)) => fmpz(1)))
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