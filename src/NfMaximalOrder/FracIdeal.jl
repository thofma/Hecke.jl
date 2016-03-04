export NfMaxOrdFracIdeal

function basis_mat(x::NfMaxOrdFracIdeal)
  return FakeFmpqMat(basis_mat(num(x)), den(x))
end

num(x::NfMaxOrdFracIdeal) = x.num

den(x::NfMaxOrdFracIdeal) = x.den

function show(io::IO, s::NfMaxOrdFracIdealSet)
   print(io, "Set of fractional ideals of ")
   print(io, s.order)
end

function show(io::IO, id::NfMaxOrdFracIdeal)
  print(io, "1//", id.den, " * ")
  show(io, id.num)
end

function norm(A::NfMaxOrdFracIdeal)
  return norm(A.num)//A.den^degree(A.num.parent.order)
end

function minimum(A::NfMaxOrdFracIdeal)
  return minimum(A.num)//A.den
end

function prod_by_int(A::NfMaxOrdFracIdeal, a::fmpz)
  return NfMaxOrdFracIdeal(prod_by_int(A.num, a), A.den)
end

function inv(A::NfMaxOrdFracIdeal)
  B = inv(A.num)
  g = gcd(B.den, A.den)
  B.den = divexact(B.den, g)
  a = divexact(A.den, g)
  return prod_by_int(B, a)
end

function simplify(A::NfMaxOrdFracIdeal)
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

is_prime_known(A::NfMaxOrdFracIdeal) = is_prime_known(A.num)

function prod(a::NfMaxOrdFracIdeal, b::NfMaxOrdFracIdeal)
  A = prod(a.num, b.num)
  return NfMaxOrdFracIdeal(A, a.den*b.den)
end

function ==(A::NfMaxOrdFracIdeal, B::NfMaxOrdFracIdeal)
  C = simplify(prod(A, inv(B)))
  return norm(C)==1 && C.den == 1
end

*(A::NfMaxOrdFracIdeal, B::NfMaxOrdFracIdeal) = prod(A, B)
*(A::NfMaxOrdIdeal, B::NfMaxOrdFracIdeal) = NfMaxOrdFracIdeal(A*B.num, B.den)
*(A::NfMaxOrdFracIdeal, B::NfMaxOrdIdeal) = NfMaxOrdFracIdeal(A.num*B, A.den)

function *(A::NfMaxOrdFracIdeal, a::nf_elem)
  C = *(A, Ideal(order(num(A))), a)
  return C
end

function /(A::NfMaxOrdFracIdeal, B::NfMaxOrdIdeal)
  C = prod(A, inv(B))
  return C
end

function /(A::NfMaxOrdFracIdeal, a::nf_elem)
  C = prod(A, Ideal((order(num(A)), inv(a))))
  return C
end

function Base.call(ord::NfMaxOrdIdlSet, b::NfMaxOrdFracIdeal)
   b.den > 1 && error("not integral")
   return b.num
end

*(x::nf_elem, y::NfMaxOrdFracIdeal) = y * x

