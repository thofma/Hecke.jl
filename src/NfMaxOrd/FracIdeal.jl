export NfMaxOrdFracIdl

function basis_mat(x::NfMaxOrdFracIdl)
  return FakeFmpqMat(basis_mat(num(x)), den(x))
end

function order(x::NfMaxOrdFracIdl)
  return x.parent.order
end

num(x::NfMaxOrdFracIdl) = x.num

den(x::NfMaxOrdFracIdl) = x.den

function show(io::IO, s::NfMaxOrdFracIdlSet)
   print(io, "Set of fractional ideals of ")
   print(io, s.order)
end

function show(io::IO, id::NfMaxOrdFracIdl)
  print(io, "1//", id.den, " * ")
  show(io, id.num)
end

function norm(A::NfMaxOrdFracIdl)
  return norm(A.num)//A.den^degree(A.num.parent.order)
end

function minimum(A::NfMaxOrdFracIdl)
  return minimum(A.num)//A.den
end

function prod_by_int(A::NfMaxOrdFracIdl, a::fmpz)
  return NfMaxOrdFracIdl(prod_by_int(A.num, a), A.den)
end

function inv(A::NfMaxOrdFracIdl)
  B = inv(A.num)
  g = gcd(B.den, A.den)
  B.den = divexact(B.den, g)
  a = divexact(A.den, g)
  return prod_by_int(B, a)
end

function simplify(A::NfMaxOrdFracIdl)
  simplify(A.num)
  m = minimum(A.num)
  g = gcd(m, A.den)
  if g != 1
    A.num.gen_one = divexact(A.num.gen_one, g)
    A.num.gen_two = divexact(A.num.gen_two, g)
    A.den = divexact(A.den, g)
    A.num.minimum = divexact(A.num.minimum, g)
    A.num.norm = divexact(A.num.norm, g^degree(A.num.parent.order))
    simplify(A.num)
  end
  return A
end

is_prime_known(A::NfMaxOrdFracIdl) = is_prime_known(A.num)

function prod(a::NfMaxOrdFracIdl, b::NfMaxOrdFracIdl)
  A = prod(a.num, b.num)
  return NfMaxOrdFracIdl(A, a.den*b.den)
end

function ==(A::NfMaxOrdFracIdl, B::NfMaxOrdFracIdl)
  C = simplify(prod(A, inv(B)))
  return norm(C)==1 && C.den == 1
end

*(A::NfMaxOrdFracIdl, B::NfMaxOrdFracIdl) = prod(A, B)
*(A::NfMaxOrdIdl, B::NfMaxOrdFracIdl) = NfMaxOrdFracIdl(A*B.num, B.den)
*(A::NfMaxOrdFracIdl, B::NfMaxOrdIdl) = NfMaxOrdFracIdl(A.num*B, A.den)

function *(A::NfMaxOrdFracIdl, a::nf_elem)
  C = *(A, Idl(order(num(A))), a)
  return C
end

function /(A::NfMaxOrdFracIdl, B::NfMaxOrdIdl)
  C = prod(A, inv(B))
  return C
end

function /(A::NfMaxOrdFracIdl, a::nf_elem)
  C = prod(A, Idl((order(num(A)), inv(a))))
  return C
end

function Base.call(ord::NfMaxOrdIdlSet, b::NfMaxOrdFracIdl)
   b.den > 1 && error("not integral")
   return b.num
end

*(x::nf_elem, y::NfMaxOrdFracIdl) = y * x

