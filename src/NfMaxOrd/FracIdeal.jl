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
  return NfMaxOrdFracIdl(A.num * a, A.den)
end

function inv(A::NfMaxOrdFracIdl)
  B = inv(A.num)
  g = gcd(B.den, A.den)
  B.den = divexact(B.den, g)
  a = divexact(A.den, g)
  return prod_by_int(B, a)
end

function simplify_exact(A::NfMaxOrdFracIdl)
  g = A.den

  A.den = divexact(A.den, g)

  @assert A.den == 1

  if has_2_elem(A.num)
    A.num.gen_one = divexact(A.num.gen_one, g)
    A.num.gen_two = divexact(A.num.gen_two, g)
  end

  if has_minimum(A.num)
    A.num.minimum = divexact(A.num.minimum, g)
  end
  if has_norm(A.num)
    A.num.norm = divexact(A.num.norm, g^degree(A.num.parent.order))
  end
  if has_basis_mat(A.num)
    A.num.basis_mat = divexact(A.num.basis_mat, g)
  end
end

function simplify(A::NfMaxOrdFracIdl)
  simplify(A.num)
  b = basis_mat(A.num)
  g = den(A)
  for i in 1:rows(b)
    for j in 1:cols(b)
      g = gcd(g, b[i, j])
    end
  end

  if g != 1
    if has_2_elem(A.num)
      A.num.gen_one = divexact(A.num.gen_one, g)
      A.num.gen_two = divexact(A.num.gen_two, g)
    end
    A.den = divexact(A.den, g)
    if has_minimum(A.num)
      A.num.minimum = divexact(A.num.minimum, g)
    end
    if has_norm(A.num)
      A.num.norm = divexact(A.num.norm, g^degree(A.num.parent.order))
    end
    if has_basis_mat(A.num)
      A.num.basis_mat = divexact(A.num.basis_mat, g)
    end
  end

#  m = minimum(A.num)
#  println("minimum is $m")
#  g = gcd(m, A.den)
#  println("gcd is $g")
#  println("now do something with $(A.num)")
#  if g != 1
#    if has_2_elem(A.num)
#      A.num.gen_one = divexact(A.num.gen_one, g)
#      A.num.gen_two = divexact(A.num.gen_two, g)
#    end
#    A.den = divexact(A.den, g)
#    if has_minimum(A.num)
#      A.num.minimum = divexact(A.num.minimum, g)
#    end
#    if has_norm(A.num)
#      A.num.norm = divexact(A.num.norm, g^degree(A.num.parent.order))
#    end
#    if has_basis_mat(A.num)
#      A.num.basis_mat = divexact(A.num.basis_mat, g)
#    end
#    simplify(A.num)
#  end
  return A
end

is_prime_known(A::NfMaxOrdFracIdl) = is_prime_known(A.num)

function prod(a::NfMaxOrdFracIdl, b::NfMaxOrdFracIdl)
  #println("==================\n", has_2_elem(a.num))
  #println(has_2_elem(b.num))
  A = a.num* b.num
  #println(has_2_elem(A))
  return NfMaxOrdFracIdl(A, a.den*b.den)
end

function ==(A::NfMaxOrdFracIdl, B::NfMaxOrdFracIdl)
  #return B.den * basis_mat(A.num) == A.den * basis_mat(B.num)
  D = inv(B)
  E = prod(A, D)
  C = simplify(E)
  return norm(C)==1 && C.den == 1
end

*(A::NfMaxOrdFracIdl, B::NfMaxOrdFracIdl) = prod(A, B)

function *(A::NfMaxOrdIdl, B::NfMaxOrdFracIdl)
  z = NfMaxOrdFracIdl(A*B.num, B.den)
  return z
end

*(A::NfMaxOrdFracIdl, B::NfMaxOrdIdl) = NfMaxOrdFracIdl(A.num*B, A.den)

function *(A::NfMaxOrdFracIdl, a::nf_elem)
  C = *(A, a*order(num(A)))
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

function *(x::nf_elem, y::NfMaxOrd)
  b, z = _check_elem_in_order(den(x, y)*x, y)
  return NfMaxOrdFracIdl(ideal(y, y(z)), den(x, y))
end
  
function deepcopy(x::NfMaxOrdFracIdl)
  z = NfMaxOrdFracIdl(deepcopy(x.num), deepcopy(x.den))
  if isdefined(x, :basis_mat)
    z.basis_mat = deepcopy(x.basis_mat)
  end
  return z
end
