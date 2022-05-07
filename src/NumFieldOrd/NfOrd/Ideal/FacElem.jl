function factored_norm(A::FacElem{NfOrdIdl, NfOrdIdlSet})
  b = Dict{fmpq, fmpz}()
  for (p, k) = A.fac
    n = norm(p)
    add_to_key!(b, fmpq(n), k)
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

function norm(A::FacElem{NfOrdIdl, NfOrdIdlSet})
  return evaluate(factored_norm(A))
end

function factored_norm(A::NfOrdFracIdl)
  n = norm(A)
  return FacElem(Dict(fmpq(numerator(n)) => 1, fmpq(denominator(n)) => -1))
end

function factored_norm(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  b = Dict{fmpq, fmpz}()
  for (p, k) = A.fac
    if iszero(k)
      continue
    end
    n = norm(p)
    v = numerator(n)
    add_to_key!(b, fmpq(v), k)
    #if haskey(b, v)
    #  b[v] += k
    #else
    #  b[v] = k
    #end
    v1 = denominator(n)
    add_to_key!(b, fmpq(v1), -k)
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

function norm(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  return evaluate(factored_norm(A))
end



@doc Markdown.doc"""
    valuation(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}, p::NfOrdIdl)
    valuation(A::FacElem{NfOrdIdl, NfOrdIdlSet}, p::NfOrdIdl)

The valuation of $A$ at $P$.
"""
function valuation(A::FacElem{NfOrdIdl, NfOrdIdlSet}, p::NfOrdIdl)
  return sum(valuation(I, p)*v for (I, v) = A.fac if !iszero(v))
end

function valuation(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}, p::NfOrdIdl)
  return sum(valuation(I, p)*v for (I, v) = A.fac)
end

@doc Markdown.doc"""
     ideal(O::NfOrd, a::FacElem{nf_elem, AnticNumberField)
The factored fractional ideal $a*O$.
"""
function ideal(O::NfOrd, a::FacElem{nf_elem, AnticNumberField})
  de = Dict{NfOrdFracIdl, fmpz}()
  for (e, k) = a.fac
    if !iszero(k)
      I = ideal(O, e)
      add_to_key!(de, I, k)
    end
  end
  return FacElem(FractionalIdealSet(O), de)
end

function ==(A::NfOrdIdl, B::FacElem{NfOrdIdl, NfOrdIdlSet})
  C = inv(B)*A
  return isone(C)
end
==(B::FacElem{NfOrdIdl, NfOrdIdlSet}, A::NfOrdIdl) = A == B

function ==(A::NfOrdFracIdl, B::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  C = A*inv(B)
  return isone(C)
end
==(B::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}, A::NfOrdIdl) = A == B

function isone(A::NfOrdFracIdl)
  B = simplify(A)
  return B.den == 1 && isone(B.num)
end

function ==(A::FacElem{NfOrdFracIdl,NfOrdFracIdlSet}, B::FacElem{NfOrdFracIdl,NfOrdFracIdlSet})
  @assert check_parent(A, B) "Elements must have same parent"
  return isone(A*inv(B))
end
function ==(A::FacElem{NfOrdIdl,NfOrdIdlSet}, B::FacElem{NfOrdIdl,NfOrdIdlSet})
  @assert check_parent(A, B) "Elements must have same parent"
  return isone(A*inv(B))
end
function ==(A::FacElem{NfOrdIdl,NfOrdIdlSet}, B::FacElem{NfOrdFracIdl,NfOrdFracIdlSet})
  @assert order(base_ring(A)) === order(base_ring(B)) "Elements must be defined over the same order"
  return isone(A*inv(B))
end

==(A::FacElem{NfOrdFracIdl,NfOrdFracIdlSet}, B::FacElem{NfOrdIdl,NfOrdIdlSet}) = B==A

==(A::NfOrdFracIdl, B::FacElem{NfOrdIdl,NfOrdIdlSet}) = isone(A*inv(B))

function *(A::FacElem{NfOrdIdl,NfOrdIdlSet}, B::FacElem{NfOrdFracIdl,NfOrdFracIdlSet})
  @assert order(base_ring(A)) === order(base_ring(B)) "Elements must be defined over the same order"
  C = copy(B)
  for (i,k) = A.fac
    C *= FacElem(Dict(i//1 => k))
  end
  return C
end
*(A::FacElem{NfOrdFracIdl,NfOrdFracIdlSet}, B::FacElem{NfOrdIdl,NfOrdIdlSet}) = B*A

function isone(A::FacElem{NfOrdIdl, NfOrdIdlSet})
  if all(x -> iszero(x), values(A.fac))
    return true
  end
  simplify!(A)
  return length(A.fac) == 1 && (isone(first(keys(A.fac))) || iszero(first(values(A.fac))))
end

function isone(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  A = simplify(A)
  return length(A.fac) == 1 && (isone(first(keys(A.fac))) || iszero(first(values(A.fac))))
end

function factor(Q::FacElem{NfOrdIdl, NfOrdIdlSet})
  if !all(is_prime, keys(Q.fac))
    S = factor_coprime(Q)
    fac = Dict{NfOrdIdl, Int}()
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

function FacElem(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}, O::NfOrdIdlSet)
  D = Dict{NfOrdIdl, fmpz}()
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


@doc Markdown.doc"""
    factor_coprime(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> Dict{NfOrdIdl, Int}

A coprime factorisation of $Q$: each ideal in $Q$ is split using \code{integral_split} and then
a coprime basis is computed.
This does {\bf not} use any factorisation.
"""
function factor_coprime(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  D = FacElem(Q, NfOrdIdlSet(order(base_ring(Q))))
  S = factor_coprime(D)
  return S
end

@doc Markdown.doc"""
     factor(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> Dict{NfOrdIdl, Int}
The factorisation of $Q$, by refining a coprime factorisation.
"""
function factor(Q::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  S = factor_coprime(Q)
  fac = Dict{NfOrdIdl, Int}()
  for (p, e) = S
    lp = factor(p)
    for (q, v) in lp
      fac[q] = Int(v*e)
    end
  end
  return fac
end

#TODO: expand the coprime stuff to automatically also get the exponents
@doc Markdown.doc"""
    simplify(x::FacElem{NfOrdIdl, NfOrdIdlSet}) -> FacElem
    simplify(x::FacElem{NfOrdFracIdl, NfOrdFracIdlSet}) -> FacElem

Uses ```coprime_base``` to obtain a simplified version of $x$, ie.
in the simplified version all base ideals will be pariwise coprime
but not neccessarily prime!.
"""
function simplify(x::FacElem{NfOrdIdl, NfOrdIdlSet})
  z = copy(x)
  simplify!(z)
  return z
end


function factor_over_coprime_base(x::FacElem{NfOrdIdl, NfOrdIdlSet}, coprime_base::Vector{NfOrdIdl})
  ev = Dict{NfOrdIdl, fmpz}()
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
    v = fmpz(0)
    for (b, e) in x
      if iszero(e)
        continue
      end
      if divisible(norm(b, copy = false), P)
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

function simplify!(x::FacElem{NfOrdIdl, NfOrdIdlSet}; refine::Bool = false)
  if length(x.fac) <= 1
    return nothing
  elseif all(x -> iszero(x), values(x.fac))
    x.fac = Dict{NfOrdIdl, fmpz}()
    return nothing
  end
  base_x = NfOrdIdl[y for (y, v) in x if !iszero(v)]
  cp = coprime_base(base_x, refine = refine)
  ev = factor_over_coprime_base(x, cp)
  x.fac = ev
  return nothing
end

function simplify(x::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  z = copy(x)
  simplify!(z)
  return z
end

function simplify!(x::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  de = factor_coprime(x)
  if length(de)==0
    de = Dict(ideal(order(base_ring(parent(x))), 1) => fmpz(1))
  end
  x.fac = Dict((i//1, k) for (i,k) = de)
end

@doc Markdown.doc"""
    factor_coprime(x::FacElem{NfOrdIdl, NfOrdIdlSet}) -> Dict{NfOrdIdl, Int}

Computed a partial factorisation of $x$, ie. writes $x$ as a product
of pariwise coprime integral ideals.
"""
function factor_coprime(x::FacElem{NfOrdIdl, NfOrdIdlSet})
  z = copy(x)
  simplify!(z)
  return Dict{NfOrdIdl, Int}(p=>Int(v) for (p,v) = z.fac)
end

function factor_coprime!(x::FacElem{NfOrdIdl, NfOrdIdlSet}; refine::Bool = false)
  simplify!(x, refine = refine)
  return Dict{NfOrdIdl, Int}(p => Int(v) for (p,v) = x.fac)
end
