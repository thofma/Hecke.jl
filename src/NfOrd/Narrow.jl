function ==(A::NfOrdIdl, B::NfOrdFracIdl)
  C = simplify(B)
  if C.den != 1 || C.num != A
    return false
  else
    return true
  end
end

==(A::NfOrdFracIdl, B::NfOrdIdl) = B==A

@doc Markdown.doc"""
***
    reduce_ideal2(A::FacElem{NfOrdIdl}) -> NfOrdIdl, FacElem{nf_elem}
> Computes $B$ and $\alpha$ in factored form, such that $\alpha B = A$.
"""
function reduce_ideal2(I::FacElem{NfOrdIdl, NfOrdIdlSet})
  O = order(first(keys(I.fac)))
  K = nf(O)
  fst = true
  a = FacElem(Dict(K(1) => fmpz(1)))
  A = ideal(O, 1)

  for (k,v) = I.fac
    @assert order(k) === O
    if iszero(v)
      continue
    end
    if fst
      A, a = power_reduce2(k, v)
      @hassert :PID_Test 1 (v>0 ? k^Int(v) : inv(k)^Int(-v)) == A*evaluate(a)
      fst = false
    else
      B, b = power_reduce2(k, v)
      @hassert :PID_Test (v>0 ? k^Int(v) : inv(k)^Int(-v)) == B*evaluate(b)
      A = A*B
      a = a*b
      if norm(A) > abs(discriminant(O))
        A, c = reduce_ideal2(A)
        a = a*FacElem(Dict(K(c) => fmpz(-1)))
      end
    end
  end
  @hassert :PID_Test 1 A*evaluate(a) == evaluate(I)
  return A, a
end
