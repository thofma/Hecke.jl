function norm(A::FacElem{NfOrdIdl, NfOrdIdlSet})
  b = Dict{fmpz, fmpz}()
  for (p, k) = A.fac
    n = norm(p)
    if haskey(b, n)
      b[n] += k
    else
      b[n] = k
    end
  end
  bb = FacElem(b)
  simplify!(bb)
  return evaluate(bb)
end

function norm(A::FacElem{NfOrdFracIdl, NfOrdFracIdlSet})
  b = Dict{fmpz, fmpz}()
  for (p, k) = A.fac
    n = norm(p)
    v = numerator(n)
    if haskey(b, v)
      b[v] += k
    else
      b[v] = k
    end
    v = denominator(n)
    if haskey(b, v)
      b[v] -= k
    else
      b[v] = -k
    end
  end
  bb = FacElem(b)
  simplify!(bb)
  return evaluate(bb)
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

