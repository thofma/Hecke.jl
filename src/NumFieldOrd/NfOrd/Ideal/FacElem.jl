function factored_norm(A::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  b = Dict{QQFieldElem, ZZRingElem}()
  for (p, k) = A.fac
    n = norm(p)
    add_to_key!(b, QQFieldElem(n), k)
    #if haskey(b, n)
    #  b[n] += k
    #else
    #  b[n] = k
    #end
  end
  bb = FacElem(FlintQQ, b)
  simplify!(bb)
  return bb
end

function norm(A::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  return evaluate(factored_norm(A))
end

function factored_norm(A::AbsSimpleNumFieldOrderFractionalIdeal)
  n = norm(A)
  return FacElem(Dict(QQFieldElem(numerator(n)) => 1, QQFieldElem(denominator(n)) => -1))
end

function factored_norm(A::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  b = Dict{QQFieldElem, ZZRingElem}()
  for (p, k) = A.fac
    if iszero(k)
      continue
    end
    n = norm(p)
    v = numerator(n)
    add_to_key!(b, QQFieldElem(v), k)
    #if haskey(b, v)
    #  b[v] += k
    #else
    #  b[v] = k
    #end
    v1 = denominator(n)
    add_to_key!(b, QQFieldElem(v1), -k)
    #if haskey(b, v)
    #  b[v] -= k
    #else
    #  b[v] = -k
    #end
  end
  bb = FacElem(FlintQQ, b)
  simplify!(bb)
  return bb
end

function norm(A::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  return evaluate(factored_norm(A))
end



@doc raw"""
    valuation(A::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
    valuation(A::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})

The valuation of $A$ at $P$.
"""
function valuation(A::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return sum(valuation(I, p)*v for (I, v) = A.fac if !iszero(v))
end

function valuation(A::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  return sum(valuation(I, p)*v for (I, v) = A.fac)
end

@doc raw"""
     ideal(O::AbsSimpleNumFieldOrder, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField)
The factored fractional ideal $a*O$.
"""
function ideal(O::AbsSimpleNumFieldOrder, a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
  de = Dict{AbsSimpleNumFieldOrderFractionalIdeal, ZZRingElem}()
  for (e, k) = a.fac
    if !iszero(k)
      I = ideal(O, e)
      add_to_key!(de, I, k)
    end
  end
  return FacElem(FractionalIdealSet(O), de)
end

function ==(A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, B::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  C = inv(B)*A
  return isone(C)
end
==(B::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) = A == B

function ==(A::AbsSimpleNumFieldOrderFractionalIdeal, B::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  C = A*inv(B)
  return isone(C)
end
==(B::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, A::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}) = A == B

function isone(A::AbsSimpleNumFieldOrderFractionalIdeal)
  B = simplify(A)
  return B.den == 1 && isone(B.num)
end

function ==(A::FacElem{AbsSimpleNumFieldOrderFractionalIdeal,AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, B::FacElem{AbsSimpleNumFieldOrderFractionalIdeal,AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  @assert check_parent(A, B) "Elements must have same parent"
  return isone(A*inv(B))
end
function ==(A::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, B::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  @assert check_parent(A, B) "Elements must have same parent"
  return isone(A*inv(B))
end
function ==(A::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, B::FacElem{AbsSimpleNumFieldOrderFractionalIdeal,AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  @assert order(base_ring(A)) === order(base_ring(B)) "Elements must be defined over the same order"
  return isone(A*inv(B))
end

==(A::FacElem{AbsSimpleNumFieldOrderFractionalIdeal,AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, B::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}) = B==A

==(A::AbsSimpleNumFieldOrderFractionalIdeal, B::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}) = isone(A*inv(B))

function *(A::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, B::FacElem{AbsSimpleNumFieldOrderFractionalIdeal,AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  @assert order(base_ring(A)) === order(base_ring(B)) "Elements must be defined over the same order"
  C = copy(B)
  for (i,k) = A.fac
    C *= FacElem(Dict(i//1 => k))
  end
  return C
end
*(A::FacElem{AbsSimpleNumFieldOrderFractionalIdeal,AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, B::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}) = B*A

function isone(A::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  if all(x -> iszero(x), values(A.fac))
    return true
  end
  simplify!(A)
  return length(A.fac) == 1 && (isone(first(keys(A.fac))) || iszero(first(values(A.fac))))
end

function isone(A::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  A = simplify(A)
  return length(A.fac) == 1 && (isone(first(keys(A.fac))) || iszero(first(values(A.fac))))
end

function factor(Q::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  if !all(is_prime, keys(Q.fac))
    S = factor_coprime(Q)
    fac = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
    for (p, e)=S
      lp = factor(p)
      for (q, v) in lp
        fac[q] = Int(v*e)
      end
    end
  else
    fac = Dict(p=>Int(e) for (p,e) = Q.fac)
  end
  return fac
end

function FacElem(Q::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, O::AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem})
  D = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem}()
  for (I, v) = Q.fac
    if iszero(v)
      continue
    end
    if isone(I.den)
      add_to_key!(D, I.num, v)
    else
      n,d = integral_split(I)
      add_to_key!(D, n, v)
      add_to_key!(D, d, -v)
    end
  end
  return FacElem(O, D)
end


@doc raw"""
    factor_coprime(Q::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}

A coprime factorisation of $Q$: each ideal in $Q$ is split using \code{integral_split} and then
a coprime basis is computed.
This does {\bf not} use any factorisation.
"""
function factor_coprime(Q::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  D = FacElem(Q, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}(order(base_ring(Q))))
  S = factor_coprime(D)
  return S
end

@doc raw"""
     factor(Q::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}
The factorisation of $Q$, by refining a coprime factorisation.
"""
function factor(Q::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  S = factor_coprime(Q)
  fac = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}()
  for (p, e) = S
    lp = factor(p)
    for (q, v) in lp
      fac[q] = Int(v*e)
    end
  end
  return fac
end

#TODO: expand the coprime stuff to automatically also get the exponents
@doc raw"""
    simplify(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> FacElem
    simplify(x::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> FacElem

Uses ```coprime_base``` to obtain a simplified version of $x$, ie.
in the simplified version all base ideals will be pariwise coprime
but not necessarily prime!.
"""
function simplify(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  z = copy(x)
  simplify!(z)
  return z
end


function factor_over_coprime_base(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, coprime_base::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  ev = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem}()
  if isempty(coprime_base)
    return ev
  end
  OK = order(coprime_base[1])
  for p in coprime_base
    if isone(p)
      continue
    end
    P = minimum(p)
    @vprint :CompactPresentation 3 "Computing valuation at an ideal lying over $P"
    assure_2_normal(p)
    v = ZZRingElem(0)
    for (b, e) in x
      if iszero(e)
        continue
      end
      if is_divisible_by(norm(b, copy = false), P)
        v += valuation(b, p)*e
      end
    end
    @vprint :CompactPresentation 3 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
    if !iszero(v)
      ev[p] = v
    end
  end
  return ev
end

function simplify!(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}; refine::Bool = false)
  if length(x.fac) <= 1
    return nothing
  elseif all(x -> iszero(x), values(x.fac))
    x.fac = Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ZZRingElem}()
    return nothing
  end
  base_x = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[y for (y, v) in x if !iszero(v)]
  cp = coprime_base(base_x, refine = refine)
  ev = factor_over_coprime_base(x, cp)
  x.fac = ev
  return nothing
end

function simplify(x::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  z = copy(x)
  simplify!(z)
  return z
end

function simplify!(x::FacElem{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderFractionalIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  de = factor_coprime(x)
  if length(de)==0
    de = Dict(ideal(order(base_ring(parent(x))), 1) => ZZRingElem(1))
  end
  x.fac = Dict((i//1, k) for (i,k) = de)
end

@doc raw"""
    factor_coprime(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}

Computed a partial factorisation of $x$, ie. writes $x$ as a product
of pariwise coprime integral ideals.
"""
function factor_coprime(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  z = copy(x)
  simplify!(z)
  return Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}(p=>Int(v) for (p,v) = z.fac)
end

function factor_coprime!(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}; refine::Bool = false)
  simplify!(x, refine = refine)
  return Dict{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}(p => Int(v) for (p,v) = x.fac)
end
