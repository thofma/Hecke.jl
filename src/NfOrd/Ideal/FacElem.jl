function factored_norm(A::FacElem{NfOrdIdl, NfOrdIdlSet})
  b = Dict{fmpz, fmpz}()
  for (p, k) = A.fac
    n = norm(p)
    add_to_key!(b, n, k)
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
  return FacElem(Dict(numerator(n) => 1, denominator(n) => -1))
end

function factored_norm(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  b = Dict{fmpz, fmpz}()
  for (p, k) = A.fac
    n = norm(p)
    v = numerator(n)
    add_to_key!(b, v, k)
    #if haskey(b, v)
    #  b[v] += k
    #else
    #  b[v] = k
    #end
    v = denominator(n)
    add_to_key!(b, v, -k)
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
    #if haskey(B, ak)
    #  B[ak] += v
    #else
    #  B[ak] = v
    #end
  end
  if length(B) == 0
    return FacElem(FlintZZ)
  end
  return FacElem(B)
end

function ==(A::T, B::T) where {T <: FacElemQ}
  C = A*B^-1
  simplify!(C)
  return all(iszero, values(C.fac))
end

function isone(A::FacElemQ)
  C = simplify(A)
  return all(iszero, values(C.fac))
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
  return isone(A*inv(B))
end
function ==(A::FacElem{NfOrdIdl,NfOrdIdlSet}, B::FacElem{NfOrdIdl,NfOrdIdlSet})
  return isone(A*inv(B))
end
function ==(A::FacElem{NfOrdIdl,NfOrdIdlSet}, B::FacElem{NfOrdFracIdl,NfOrdFracIdlSet})
  return isone(A*inv(B))
end

==(A::FacElem{NfOrdFracIdl,NfOrdFracIdlSet}, B::FacElem{NfOrdIdl,NfOrdIdlSet}) = B==A

==(A::NfOrdFracIdl, B::FacElem{NfOrdIdl,NfOrdIdlSet}) = isone(A*inv(B))

function *(A::FacElem{NfOrdIdl,NfOrdIdlSet}, B::FacElem{NfOrdFracIdl,NfOrdFracIdlSet})
  C = deepcopy(B)
  for (i,k) = A.fac
    C *= FacElem(Dict(i//1 => k))
  end
  return C
end
*(A::FacElem{NfOrdFracIdl,NfOrdFracIdlSet}, B::FacElem{NfOrdIdl,NfOrdIdlSet}) = B*A

function isone(A::FacElem{NfOrdIdl, NfOrdIdlSet})
  A = simplify(A)
  return length(A.fac) == 1 && isone(first(keys(A.fac)))
end

function isone(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  A = simplify(A)
  return length(A.fac) == 1 && isone(first(keys(A.fac)))
end

