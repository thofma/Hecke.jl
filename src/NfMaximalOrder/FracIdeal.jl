export NfMaximalOrderFracIdeal

function basis_mat(x::NfMaximalOrderFracIdeal)
  return FakeFmpqMat(basis_mat(num(x)), den(x))
end

num(x::NfMaximalOrderFracIdeal) = x.num

den(x::NfMaximalOrderFracIdeal) = x.den

function show(io::IO, s::NfMaximalOrderFracIdealSet)
   print(io, "Set of fractional ideals of ")
   print(io, s.order)
end

function show(io::IO, id::NfMaximalOrderFracIdeal)
  print(io, "1//", id.den, " * ")
  show(io, id.num)
end

function norm(A::NfMaximalOrderFracIdeal)
  return norm(A.num)//A.den^degree(A.num.parent.order)
end

function minimum(A::NfMaximalOrderFracIdeal)
  return minimum(A.num)//A.den
end

function prod_by_int(A::NfMaximalOrderFracIdeal, a::fmpz)
  return NfMaximalOrderFracIdeal(prod_by_int(A.num, a), A.den)
end

function inv(A::NfMaximalOrderFracIdeal)
  B = inv(A.num)
  g = gcd(B.den, A.den)
  B.den = divexact(B.den, g)
  a = divexact(A.den, g)
  return prod_by_int(B, a)
end

function simplify(A::NfMaximalOrderFracIdeal)
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

is_prime_known(A::NfMaximalOrderFracIdeal) = is_prime_known(A.num)

function prod(a::NfMaximalOrderFracIdeal, b::NfMaximalOrderFracIdeal)
  A = prod(a.num, b.num)
  return NfMaximalOrderFracIdeal(A, a.den*b.den)
end

function ==(A::NfMaximalOrderFracIdeal, B::NfMaximalOrderFracIdeal)
  C = simplify(prod(A, inv(B)))
  return norm(C)==1 && C.den == 1
end

*(A::NfMaximalOrderFracIdeal, B::NfMaximalOrderFracIdeal) = prod(A, B)
*(A::NfMaximalOrderIdeal, B::NfMaximalOrderFracIdeal) = NfMaximalOrderFracIdeal(A*B.num, B.den)
*(A::NfMaximalOrderFracIdeal, B::NfMaximalOrderIdeal) = NfMaximalOrderFracIdeal(A.num*B, A.den)

function *(A::NfMaximalOrderFracIdeal, a::nf_elem)
  C = *(A, Ideal(order(num(A))), a)
  return C
end

function /(A::NfMaximalOrderFracIdeal, B::NfMaximalOrderIdeal)
  C = prod(A, inv(B))
  return C
end

function /(A::NfMaximalOrderFracIdeal, a::nf_elem)
  C = prod(A, Ideal((order(num(A)), inv(a))))
  return C
end

function Base.call(ord::NfMaximalOrderIdealSet, b::NfMaximalOrderFracIdeal)
   b.den > 1 && error("not integral")
   return b.num
end

*(x::nf_elem, y::NfMaximalOrderFracIdeal) = y * x

