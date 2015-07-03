###########################################################################################
#
#   MaximalOrderIdeals.jl : ideals in Nemo
#
###########################################################################################
export IdealSet, minimum, is_prime_known, MaximalOrderIdeal, basis_mat,
       valuation, defines_2_normal, *, /, ==, MaximalOrderIdealSet, norm

###########################################################################################
#
#   Types and memory management
#
###########################################################################################

MaximalOrderIdealSetID = Dict{fmpq_poly, Ring}()

type MaximalOrderIdealSet <: Ring
   order::PariMaximalOrder
   function MaximalOrderIdealSet(O::PariMaximalOrder)
     try
       return MaximalOrderIdealSetID[O.pari_nf.nf.pol]
     catch
       r = new()
       r.order = O
       MaximalOrderIdealSetID[O.pari_nf.nf.pol] = r
       return r
     end
   end
end

type MaximalOrderIdeal <: RingElem
   basis::Tuple{fmpz_mat, fmpz}
   gen_one::fmpz
   gen_two::nf_elem
   gens_are_short::Int
   gens_are_normal::fmpz
   gens_are_weakly_normal:: Int  # 1 if Norm(A) = gcd(Norm, Norm) and gen_one is int
                                 # weaker than normality - at least potentialy
   norm :: fmpz
   minimum :: fmpz
   is_prime::Int     # 0: don't know, 1 known to be prime, 2 known to be not prime
   is_principal::Int # as above
   princ_gen::Union(fmpz, nf_elem)
   splitting_type::Tuple{Int, Int}

   valuation::Function #a function returning "the" valuation - mind that the ideal is not prime
 
   parent::MaximalOrderIdealSet

   function MaximalOrderIdeal(A::PariIdeal, ord::MaximalOrderIdealSet)
      r = new()
      K = ord.order.pari_nf.nf
      p, a, e, f = __prime_ideal_components(A)
      r.gen_one = p
      r.gen_two = K(a)
      r.norm = p^f
      r.minimum = p
      r.is_prime = 1
      r.gens_are_normal = p
      r.gens_are_weakly_normal = 1
      r.parent = ord
      r.splitting_type = e, f
      return r
   end

   function MaximalOrderIdeal(a::Tuple{fmpz_mat, fmpz}, ord::MaximalOrderIdealSet)
      r = new(a)
      r.parent = ord
      return r
   end

   function MaximalOrderIdeal(a::fmpz, b::nf_elem, ord::MaximalOrderIdealSet)
      r = new();
      @assert denominator(b, ord.order) == 1
      r.gen_one = a
      r.gen_two = b
      r.parent = ord;
      return r
   end

   function MaximalOrderIdeal(ord::MaximalOrderIdealSet)
      r = new();
      r.parent = ord;
      return r
   end
end

# for some strange reason use outer constructors!

function MaximalOrderIdeal(b::nf_elem, ord::MaximalOrderIdealSet)
   O = ord.order
   d = denominator(b, O)
   @assert d==1
   bi = inv(b)
   C = MaximalOrderIdeal(ord)
   C.gen_one = denominator(bi, O)
   C.minimum = C.gen_one
   C.gen_two = b
   C.norm = num(abs(norm(b)))
   @assert(gcd(C.gen_one^degree(O), ZZ(norm(C.gen_two))) == C.norm);
   C.princ_gen = b
   C.gens_are_normal = C.gen_one
   C.gens_are_weakly_normal = 1
   return C
end

MaximalOrderFracIdealSetID = Dict{fmpq_poly, Ring}()

type MaximalOrderFracIdealSet <: Ring
   order::PariMaximalOrder
   function MaximalOrderFracIdealSet(O::PariMaximalOrder)
     try
       return MaximalOrderFracIdealSetID[O.pari_nf.nf.pol]
     catch
       r = new()
       r.order = O
       MaximalOrderFracIdealSetID[O.pari_nf.nf.pol] = r
       return r
     end
   end
end

type MaximalOrderFracIdeal
  I::MaximalOrderIdeal
  den::fmpz
end

###########################################################################################
#
#   String I/O
#
###########################################################################################

function show(io::IO, s::MaximalOrderIdealSet)
   print(io, "Set of ideals of ")
   print(io, s.order)
end

function show(io::IO, s::MaximalOrderFracIdealSet)
   print(io, "Set of fractional ideals of ")
   print(io, s.order)
end

function show(io::IO, id::MaximalOrderIdeal)
   if has_2_elem(id)
     print(io, "<", id.gen_one, ", ", id.gen_two, ">" )
   else
     print(io, "<no 2-elts present>");
   end
   if has_norm(id)
     print(io, "\nNorm: ", id.norm);
   end
   if has_minimum(id)
     print(io, "\nMinimum: ", id.minimum);
   end
   if isdefined(id, :princ_gen)
     print(io, "\nprincipal by ", id.princ_gen)
   end
#   if isdefined(id, :basis)
#     print(io, "\nbasis_mat ", id.basis)
#   end
   if isdefined(id, :gens_are_normal)
     print(io, "\ntwo normal wrt: ", id.gens_are_normal)
   end
   println(io)
end

function show(io::IO, id::MaximalOrderFracIdeal)
  print(io, "1//", id.den, " * ")
  show(io, id.I)
end

###########################################################################################
#
#  Standard predicates
#
###########################################################################################

function norm(A::MaximalOrderIdeal)
  if isdefined(A, :norm)
    return A.norm
  end
  if has_2_elem(A) && A.gens_are_weakly_normal == 1
    A.norm = gcd(norm(K(A.gen_one)), norm(A.gen_two))
  end
  assert(has_2_elem(A) || has_basis(A))
  O = A.parent.order
  if has_basis(A)
    A.norm = determinant(A.basis[1])//A.basis[2]^degree(O) // index(O)
  end
  assert(isdefined(A, :norm))
  return A.norm
end

function norm(A::MaximalOrderFracIdeal)
  return norm(A.I)//A.den^degree(A.I.parent.order)
end

function norm_via_basis(A::MaximalOrderIdeal)
  assert(has_2_elem(A) || has_basis(A))
  O = A.parent.order
  b = basis_mat(A)
  A.norm = determinant(b[1])//b[2]^degree(O) // index(O)
  return A.norm
end

function minimum(A::MaximalOrderIdeal)
  if has_minimum(A) 
    return A.minimum
  end
  if is_weakly_normal(A)
    d = denominator(inv(A.gen_two), A.parent.order)
    d = gcd(d, ZZ(A.gen_one))
    A.minimum = d
    return d
  end
  println("cannot min of", A)
  @assert false
end 

function minimum(A::MaximalOrderFracIdeal)
  return minimum(A.I)//A.den
end

function is_prime_known(A::MaximalOrderIdeal)
  return A.is_prime!=0
end

is_prime_known(A::MaximalOrderFracIdeal) = is_prime_known(A.I)


function has_2_elem(A::MaximalOrderIdeal)
  return isdefined(A, :gen_one)
end

function has_minimum(A::MaximalOrderIdeal)
  return isdefined(A, :minimum)
end

function has_norm(A::MaximalOrderIdeal)
  return isdefined(A, :norm)
end

function is_weakly_normal(A::MaximalOrderIdeal)
  return (isdefined(A, :gens_are_weakly_normal) && A.gens_are_weakly_normal==1) ||
         is_2_normal(A)
end

function is_2_normal(A::MaximalOrderIdeal)
  return isdefined(A, :gens_are_normal)
end

# check if gen_one,gen_two is a P(gen_one)-normal presentation
# see Pohst-Zassenhaus p. 404
function defines_2_normal(A::MaximalOrderIdeal)
  m = A.gen_one
  gen = A.gen_two
  mg = denominator(inv(gen), parent(I).order) # the minimum of ideal generated by g
  g = gcd(m,mg)
  return gcd(m,div(m,g)) == 1
end


###########################################################################################
#
#  Mult via 2-normal
#
###########################################################################################

# Berstein: coprime bases
# ppio(a,b) = (c,n) where v_p(c) = v_p(a) if v_p(b) !=0, 0 otherwise
#                         c*n = a
# or c = gcd(a, b^infty)

function ppio(a::fmpz, b::fmpz) 
  c = gcd(a, b)
  n = div(a, c)
  m = c
  g = gcd(c, n)
  while g != 1
    c = c*g
    n = div(n, g)
    g = gcd(c, n)
  end
  return (c, n)
end

function prod_via_2_elem_normal(a::MaximalOrderIdeal, b::MaximalOrderIdeal)
  assert(is_2_normal(a))
  assert(is_2_normal(b))
  a1 = ZZ(a.gen_one)
  b1 = ZZ(b.gen_one)
  m = lcm(a1, b1)
  e, f = ppio(m, a1)
  if f == 1
    a2 = a.gen_two
  else
    g, x, y = gcdx(f, a1^2) # we need to become normal at m, we are normal at a
                           # higher powers in a are fine
                           # CRT: the 2nd gen of a needs to stay the same at a
                           # and should be  1 at f
    assert(g==1)                       
    a2 = a.gen_two*f*x + y*a1^2 # now (a1, a2) should be m-normal for a
  end

  e, f = ppio(m, b1)
  if f == 1
    b2 = b.gen_two
  else
    g, x, y = gcdx(f, b1^2)
    assert(g==1)                       
    b2 = b.gen_two*f*x + y*b1^2
  end

  C = MaximalOrderIdeal(a1*b1, a2*b2, a.parent)
  C.norm = a.norm * b.norm
  if C.norm != gcd(C.gen_one^degree(C.parent.order), ZZ(norm(C.gen_two)))
    println("a:", a)
    println("b:", b)
    println("C:", C)
  assert(gcd(a1^degree(a.parent.order), ZZ(norm(a2))) == a.norm)
  assert(gcd(b1^degree(b.parent.order), ZZ(norm(b2))) == b.norm)
#    assert(false)
  end

  if has_minimum(a) && has_minimum(b) && gcd(minimum(a), minimum(b))==1 
    C.minimum = minimum(a) * minimum(b) # otherwise, I don't know the correct value
  end

  C.gens_are_normal = m

  return C
end

function prod_via_2_elem_weakly(a::MaximalOrderIdeal, b::MaximalOrderIdeal)
  assert(has_2_elem(a));
  assert(has_2_elem(b));

  O = a.parent.order
  K = O.pari_nf.nf
  bas = basis(K, O)
  n = length(bas)

  norm_c = norm(a) * norm(b)        # we ARE in the maximal order case
  norm_int_c = norm_c
  mod_c = 1
  
  if has_minimum(a) 
    mod_c *= a.minimum 
  else
    mod_c *= a.norm
  end

  if has_minimum(b) 
    mod_c *= b.minimum 
  else
    mod_c *= b.norm
  end
  
  if mod_c > 250
    r = -500:500  # should still have enough elements...
  else
    r = -Int(div(mod_c, 2)):Int(div(mod_c, 2))
  end

#  println("a:", a, "\nb:", b)
#  println("using basis: ", bas)

  gen = K() 
  gen2 = K() 
  t = K()
  s = K()
  u = K()

  cnt = 1
  while true
    cnt += 1
    Nemo.rand_into!(bas, r, t)
    r2 = rand(r)
    Nemo.rand_into!(bas, r, s)
    r4 = rand(r)
    Nemo.mult_into!(t, a.gen_two, t)
    Nemo.add_into!(t, r2*a.gen_one, t)
    Nemo.mult_into!(s, b.gen_two, s)
    Nemo.add_into!(s, r4*b.gen_one, s)
    Nemo.mult_into!(s, t, u)
    Nemo.add_into!(u, gen, gen)
#    gen2 += (r1*K(a.gen_two) + r2*a.gen_one) *
#           (r3*K(b.gen_two) + r4*b.gen_one)
    gen = element_reduce_mod(gen, O, ZZ(mod_c)^2)
    if gcd(ZZ(norm(gen)), ZZ(norm_int_c)^2) == norm_int_c # should be ^n, but for the test ^2 is sufficient
      break
    end
  end

  println("prod_via_2_elem: used ", cnt, " tries");

  c = MaximalOrderIdeal(norm_int_c, gen, a.parent)

  c.norm = norm_c

  if has_minimum(a) && has_minimum(b) && gcd(minimum(a), minimum(b))==1 
    c.minimum = minimum(a) * minimum(b) # otherwise, I don't know the correct value
  end

  c.gens_are_weakly_normal = 1

  return c
end

###########################################################################################
#
# Mult by elt
#
###########################################################################################

function make_pid(A::MaximalOrderIdealSet, b::nf_elem)
  d = denominator(b, A.order)
  return MaximalOrderFracIdeal(MaximalOrderIdeal(b*d, A), d)
end

function make_pid(A::PariMaximalOrder, b::nf_elem)
  return make_pid(IdealSet(A), b)
end

function prod_by_elt(A::MaximalOrderIdeal, b::nf_elem)
  if has_2_elem(A)
    C = MaximalOrderIdeal(b, A.parent)
    @assert is_2_normal(C)
    @assert is_2_normal(A)
    return prod(A,C)
  end
  error("not implemented yet...")
end

global last
function prod_by_int(A::MaximalOrderIdeal, a::fmpz)
  global last = (A, a)
  @assert has_2_elem(A) && is_2_normal(A)
  if a==1 || a==-1 
    println("shortcut: returning ", A)
    return A
  end
  println("prod_by_int", A, " and ", a)
  # <a,a> is a a-normal presentation
  # we need to have a common presentation for A and a though
  m = lcm(a, A.gens_are_normal)

  e, f = ppio(m, A.gen_one)
  if f == 1
    a2 = A.gen_two
  else
    g, x, y = gcdx(f, A.gen_one^2) # we need to become normal at m, we are normal at a
                           # higher powers in a are fine
                           # CRT: the 2nd gen of a needs to stay the same at a
                           # and should be  1 at f
    assert(g==1)                       
    a2 = A.gen_two*f*x + y*A.gen_one^2 # now (a1, a2) should be m-normal for a
  end
  B = MaximalOrderIdeal(A.gen_one*a, a2*a, A.parent)
  B.gens_are_normal = m
  if has_minimum(A)
    B.minimum = A.minimum * a
  end
  if has_norm(A)
    B.norm = A.norm * a^degree(A.parent.order)
  end
  println("final ", B)
  @assert has_2_elem(B) && is_2_normal(B)
  return B
end

function prod_by_int(A::MaximalOrderFracIdeal, a::fmpz)
  return MaximalOrderFracIdeal(prod_by_int(A.I, a), A.den)
end

###########################################################################################
#
# 2-element-normal
#
###########################################################################################

function assure_2_normal(A::MaximalOrderIdeal)
  if has_2_elem(A) && is_2_normal(A)
    return
  end 
  O = A.parent.order
  K = O.pari_nf.nf
  n = degree(K)

  if has_2_elem(A)  && is_weakly_normal(A)
    m = minimum(A)
    bas = basis(K, O)
    r = -div(m+1, 2):div(m+1, 2)
    if length(r) > 1000 
      r = -500:500
    end
    gen = K()
    s = K()
    cnt = 0
    while true
      cnt += 1
      Nemo.rand_into!(bas, r, s)
      Nemo.mult_into!(s, A.gen_two, s)
      Nemo.add_into!(gen, rand(r)*A.gen_one, gen)
      Nemo.add_into!(gen, s, gen)
#      gen += rand(r)*A.gen_one + rand(bas, r)*A.gen_two
      gen = element_reduce_mod(gen, O, m^2)
      mg = denominator(inv(gen), O) # the minimum of <gen>
      g = gcd(m, mg)
      if gcd(m, div(m, g)) == 1 
        if gcd(m^n, ZZ(norm(gen))) != norm(A)
          println("\n\noffending ideal", A)
          println("gen is", gen)
          println("Wrong ideal\n\n")
          cnt += 10
          continue
        end
        break
      end
    end
    println("used ", cnt, " attempts")
    A.gen_one = m
    A.gen_two = gen
    A.gens_are_normal = m
    return
  end
  error("not implemented yet...")
end

###########################################################################################
#
# inverse
#
###########################################################################################

function inv(A::MaximalOrderIdeal) 
  if has_2_elem(A) && is_weakly_normal(A)
    assure_2_normal(A)
    alpha = inv(A.gen_two)
    d = denominator(alpha, A.parent.order)
    m = ZZ(A.gen_one)
    g = gcd(m, d)
    while g > 1
      d = div(d, g)
      g = gcd(m, d)
    end
    Ai = A.parent()
    dn = denominator(d*alpha, A.parent.order)
    Ai.gen_one = dn 
    Ai.gen_two = d*alpha*dn
    temp = dn^degree(A.parent.order)//norm(A)
    @assert den(temp)==1
    Ai.norm = num(temp)
    Ai.gens_are_normal = A.gens_are_normal
    return MaximalOrderFracIdeal(Ai, dn)
  end
  error("not implemented yet")
end

function inv(A::MaximalOrderFracIdeal)
  B = inv(A.I)
  g = gcd(B.den, A.den)
  B.den = divexact(B.den, g)
  a = divexact(A.den, g)
  return prod_by_int(B, a)
end
###########################################################################################
#
#   Basis
#
###########################################################################################

function has_basis(A::MaximalOrderIdeal)
  return isdefined(A, :basis)
end

function basis_mat(A::MaximalOrderIdeal)
  if isdefined(A, :basis)
    return A.basis
  end

  assert(has_2_elem(A))

  K = A.parent.order.pari_nf.nf
  n = degree(K)
  d1 = denominator(A.gen_one)
  d2 = denominator(A.gen_two)
  d = lcm(d1, d2)
  bm = basis_mat(K, A.parent.order)
  ma = bm[1]*representation_mat(K(A.gen_one)*d)
  mb = bm[1]*representation_mat(A.gen_two*d)
  c = vcat(ma, mb)
#  println("mat is ", c, " / ", d, "/", bm[2])
  c = hnf(c)
  c = submat(c, 1, 1, n, n)
  A.basis = c,d*bm[2]
  return c,d*bm[2]  # not simplified!
end

###########################################################################################
#
#  copy
#
###########################################################################################

function copy(A::MaximalOrderIdeal)
  B = MaximalOrderIdeal(A.parent)
  for i in fieldnames(A)
    if isdefined(A, i)
      setfield!(B, i, getfield(A, i))
    end
  end
  return B
end

###########################################################################################
#
#   simplification
#
###########################################################################################

function simplify(A::MaximalOrderIdeal)
  if has_2_elem(A) && is_weakly_normal(A)
    if maximum(element_to_sequence(A.gen_two)) > A.gen_one^2
      A.gen_two = element_reduce_mod(A.gen_two, A.parent.order, A.gen_one^2)
    end
    A.minimum = gcd(A.gen_one, denominator(inv(A.gen_two), A.parent.order)) 
    A.gen_one = A.minimum
    n = gcd(A.gen_one^degree(A.parent.order), ZZ(norm(A.gen_two)))
    if isdefined(A, :norm)
    end
    A.norm = n
    A.gen_two = element_reduce_mod(A.gen_two, A.parent.order, A.gen_one^2)
    return A
  end
end

function simplify(A::MaximalOrderFracIdeal)
  simplify(A.I)
  m = minimum(A.I)
  g = gcd(m, A.den)
  if g != 1
    A.I.gen_one = divexact(A.I.gen_one, g)
    A.I.gen_two = divexact(A.I.gen_two, g)
    A.den = divexact(A.den, g)
    A.I.minimum = divexact(A.I.minimum, g)
    A.I.norm = divexact(A.I.norm, g^degree(A.I.parent.order))
    simplify(A.I)
  end
  return A
end

###########################################################################################
#
#   reduced element in same class
#
###########################################################################################

function reduce_ideal_class(A::MaximalOrderIdeal)
  B = inv(A)
  bas = basis_mat(B)
  L = lll(bas[1])
  a = element_from_mat_row(A.parent.order.pari_nf.nf, L, 1)
  a = divexact(a, bas[2])
  B = prod_by_elt(A, a)
  B = simplify(B)
  return B, a
end

###########################################################################################
#
#   valuation
#
###########################################################################################

function valuation(a::nf_elem, p::MaximalOrderIdeal)
  assert(a !=0) # can't handle infinity yet
  if isdefined(p, :valuation)
    return p.valuation(a)
  end
  pi = inv(p)
  e = divexact(pi.I.gen_two, pi.den)
  P = p.gen_one
  O = p.parent.order

  p.valuation = function(x::nf_elem)
    v = -1
    d = denominator(x, O)
    x *= d
    while gcd(denominator(x, O), P)==1
      x *= e
      v += 1
    end
    return v-valuation(d, P)[1]*p.splitting_type[1]
  end

  return p.valuation(a)
end

function valuation(a::fmpz, p::MaximalOrderIdeal)
  P = p.gen_one
  return valuation(a, P)[1]* p.splitting_type[1]
end

function valuation(A::MaximalOrderIdeal, p::MaximalOrderIdeal)
  return min(valuation(A.gen_one, p)[1], valuation(A.gen_two, p))
end


###########################################################################################
#
#  prod
#
###########################################################################################

function prod(a::MaximalOrderIdeal, b::MaximalOrderIdeal)
  if is_2_normal(a) && is_2_normal(b)
    return prod_via_2_elem_normal(a, b)
  end
  if has_2_elem(a) && has_2_elem(b)
    return prod_via_2_elem_weakly(a, b)
  end
  error("algorithm missing")
end

function prod(a::MaximalOrderFracIdeal, b::MaximalOrderFracIdeal)
  A = simplify(prod(a.I, b.I))
  return MaximalOrderFracIdeal(A, a.den*b.den)
end


###########################################################################################
#
#   trivia
#
###########################################################################################

function parent(A::MaximalOrderIdeal)
  return A.parent
end

#TODO: very bad algorithm! too slow. Note: asypmtotically FASTER than anything!
# need to move part of simplify into prod
function ==(A::MaximalOrderIdeal, B::MaximalOrderIdeal)
  C = simplify(prod(A, inv(B)))
  return norm(C)==1 
end

function ==(A::MaximalOrderFracIdeal, B::MaximalOrderFracIdeal)
  C = simplify(prod(A, inv(B)))
  return norm(C)==1 && C.den == 1
end


*(A::MaximalOrderIdeal, B::MaximalOrderIdeal) = prod(A, B)
*(A::MaximalOrderFracIdeal, B::MaximalOrderFracIdeal) = prod(A, B)
*(A::MaximalOrderIdeal, B::MaximalOrderFracIdeal) = MaximalOrderFracIdeal(A*B.I, B.den)
*(A::MaximalOrderFracIdeal, B::MaximalOrderIdeal) = MaximalOrderFracIdeal(A.I*B, A.den)

function *(A::MaximalOrderFracIdeal, a::nf_elem)
  C = prod(A, make_pid(parent(A.I), a))
  return C
end

function *(a::nf_elem, A::MaximalOrderFracIdeal)
  C = prod(A, make_pid(A.I.parent, a))
  return C
end

function *(O::PariMaximalOrder, a::nf_elem)
  C = make_pid(O, a)
  return C
end

function *(a::nf_elem, O::PariMaximalOrder)
  C = make_pid(O, a)
  return C
end

function /(A::MaximalOrderFracIdeal, B::MaximalOrderIdeal)
  C = prod(A, inv(B))
  return C
end

function /(A::MaximalOrderFracIdeal, a::nf_elem)
  C = prod(A, make_pid(A.parent, inv(a)))
  return C
end

###########################################################################################
#
#   Parent call overloads
#
###########################################################################################

function Base.call(ord::MaximalOrderIdealSet, b::PariIdeal)
   return MaximalOrderIdeal(b, ord)
end

function Base.call(ord::MaximalOrderIdealSet, b::MaximalOrderFracIdeal)
   b.den > 1 && error("not integral")
   return b.I
end

function Base.call(ord::MaximalOrderIdealSet)
   return MaximalOrderIdeal(ord)
end

function Base.call(ord::MaximalOrderIdealSet, a::nf_elem)
   return make_pid(ord, a)
end



###########################################################################################
#
#   MaximalOrder constructor
#
###########################################################################################

function IdealSet(r::PariMaximalOrder)
   return MaximalOrderIdealSet(r)
end

