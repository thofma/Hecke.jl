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
  bb = FacElem(b)
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
  bb = FacElem(b)
  simplify!(bb)
  return bb
end

function norm(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  return evaluate(factored_norm(A))
end

const FacElemQ = Union{FacElem{fmpq, FlintRationalField}, FacElem{fmpz, FlintIntegerRing}}

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
  C = deepcopy(B)
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
  if !all(isprime, keys(Q.fac))
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
  for (p, e)=S
    lp = factor(p)
    for (q, v) in lp
      fac[q] = Int(v*e)
    end
  end
  return fac
end

