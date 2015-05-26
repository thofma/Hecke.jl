#################################################################################
#
#   NfMaximalOrderIdeals.jl : ideals in Nemo
#
#################################################################################

export NfMaximalOrderIdealSet, NfMaximalOrderIdeal

export IdealSet, minimum, is_prime_known, MaximalOrderIdeal, basis_mat,
       valuation, defines_2_normal, *, /, ==, MaximalOrderIdealSet, norm, Ideal

#################################################################################
#
#  Types and memory management
#
#################################################################################

NfMaximalOrderIdealSetID = Dict{NfMaximalOrder, Ring}()

type NfMaximalOrderIdealSet <: Ring
  order::NfMaximalOrder
  function NfMaximalOrderIdealSet(O::NfMaximalOrder)
    try
      return NfMaximalOrderIdealSetID[O]
    catch
      r = new(O)
      NfMaximalOrderIdealSetID[O] = r
      return r
    end
  bas = basis_mat(B)
  end
end

order(S::NfMaximalOrderIdealSet) = S.order

type NfMaximalOrderIdeal <: RingElem
  basis::Array{NfMaximalOrderElem, 1}
  basis_mat::fmpz_mat
  gen_one::fmpz
  gen_two::NfMaximalOrderElem
  gens_are_short::Int
  gens_are_normal::fmpz
  gens_are_weakly_normal::Int  # 1 if Norm(A) = gcd(Norm, Norm) and gen_one is
                               # int
                               # weaker than normality - at least potentialy
  norm::fmpz
  minimum::fmpz
  is_prime::Int                # 0: don't know
                               # 1 known to be prime
                               # 2 known to be not prime
  is_principal::Int            # as above
  princ_gen::NfMaximalOrderElem
  splitting_type::Tuple{Int, Int}

  valuation::Function #a function returning "the" valuation - mind that the ideal is not prime

  parent::NfMaximalOrderIdealSet

  function NfMaximalOrderIdeal(A::PariIdeal, ord::NfMaximalOrderIdealSet)
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

  function NfMaximalOrderIdeal(a::fmpz_mat, par::NfMaximalOrderIdealSet)
    r = new()
    r.basis_mat = a
    r.parent = par
    return r
  end

  function NfMaximalOrderIdeal(a::fmpz, b::NfMaximalOrderElem)
    r = new();
    r.gen_one = a
    r.gen_two = b
    r.parent = NfMaximalOrderIdealSet(parent(b))
    return r
  end
  
  function NfMaximalOrderIdeal(a::fmpz, b::nf_elem, par::NfMaximalOrderIdealSet)
    r = new()
    (x,y) = _check_elem_in_maximal_order(b,order(par))
    @hassert :NfMaximalOrder x
    r.gen_one = a
    r.gen_two = order(par)(b, y)
    r.parent = par
    return r
  end

  function NfMaximalOrderIdeal(O::NfMaximalOrder)
     r = new()
     r.parent = NfMaximalOrderIdealSet(O)
     return r
  end
  
  function NfMaximalOrderIdeal(b::nf_elem, par::NfMaximalOrderIdealSet)
    O = order(par)
    
    # check if element is contained in maximal order
    (x,y) = _check_elem_in_maximal_order(b,order(par))
    @hassert :NfMaximalOrder x

    bi = inv(b)

    C = NfMaximalOrderIdeal(order(par))
    C.gen_one = denominator(bi, O)
    C.minimum = C.gen_one
    C.gen_two = O(b, y)
    C.norm = abs(num(norm(b)))
    @hassert :NfMaximalOrder gcd(C.gen_one^degree(O), ZZ(norm(C.gen_two))) == C.norm
    C.princ_gen = C.gen_two

    if C.gen_one == 1
      C.gens_are_normal = 2*C.gen_one
    else
      C.gens_are_normal = C.gen_one
    end
    C.gens_are_weakly_normal = 1
    return C
  end
end

order(x::NfMaximalOrderIdeal) = order(parent(x))

parent(x::NfMaximalOrderIdeal) = x.parent

nf(x::NfMaximalOrderIdeal) = nf(order(x))

function deepcopy(A::NfMaximalOrderIdeal)
  B = NfMaximalOrderIdeal(A.parent)
  for i in fieldnames(A)
    if isdefined(A, i)
      setfield!(B, i, getfield(A, i))
    end
  end
  return B
end

#################################################################################
#
#  String I/O
#
#################################################################################

function show(io::IO, S::NfMaximalOrderIdealSet)
   print(io, "Set of ideals of ")
   print(io, order(S))
end

function show(io::IO, id::NfMaximalOrderIdeal)
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
    print(io, "\nprincipal generator ", id.princ_gen)
  end
#   if isdefined(id, :basis)
#     print(io, "\nbasis_mat ", id.basis)
#   end
  if isdefined(id, :gens_are_normal)
    print(io, "\ntwo normal wrt: ", id.gens_are_normal)
  end
end

#################################################################################
#
#  Standard predicates
#
#################################################################################

function norm(A::NfMaximalOrderIdeal)
  if isdefined(A, :norm)
    return A.norm
  end
  if has_2_elem(A) && A.gens_are_weakly_normal == 1
    A.norm = gcd(norm(K(A.gen_one)), norm(A.gen_two))
  end
  @hassert :NfNfMaximalOrder 1 has_2_elem(A) || has_basis(A)
  O = A.parent.order
  if has_basis(A)
    A.norm = abs(determinant(basis_mat(A)))
  end
  @hassert :NfNfMaximalOrder 1 isdefined(A, :norm)
  return A.norm
end

function minimum(A::NfMaximalOrderIdeal)
  if has_minimum(A) 
    return A.minimum
  end
  if is_weakly_normal(A)
    d = denominator(inv(A.gen_two), A.parent.order)
    d = gcd(d, ZZ(A.gen_one))
    A.minimum = d
    return d
  end
  println("cannot find minimum of", A)
  @hassert :NfNfMaximalOrder 0 false
end 

function is_prime_known(A::NfMaximalOrderIdeal)
  return A.is_prime != 0
end

function has_2_elem(A::NfMaximalOrderIdeal)
  return isdefined(A, :gen_one)
end

function has_minimum(A::NfMaximalOrderIdeal)
  return isdefined(A, :minimum)
end

function has_norm(A::NfMaximalOrderIdeal)
  return isdefined(A, :norm)
end

function is_weakly_normal(A::NfMaximalOrderIdeal)
  return (isdefined(A, :gens_are_weakly_normal) &&
        A.gens_are_weakly_normal==1) || is_2_normal(A)
end

function is_2_normal(A::NfMaximalOrderIdeal)
  return isdefined(A, :gens_are_normal) && A.gens_are_normal > 1
end

# check if gen_one,gen_two is a P(gen_one)-normal presentation
# see Pohst-Zassenhaus p. 404

function defines_2_normal(A::NfMaximalOrderIdeal)
  m = A.gen_one
  gen = A.gen_two
  mg = denominator(inv(gen), parent(I).order) # the minimum of ideal generated by g
  g = gcd(m,mg)
  return gcd(m,div(m,g)) == 1
end

#################################################################################
#
#  Mult via 2-normal
#
#################################################################################

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

function prod_via_2_elem_normal(a::NfMaximalOrderIdeal, b::NfMaximalOrderIdeal)
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

  C = NfMaximalOrderIdeal(a1*b1, a2*b2, a.parent)
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

function prod_via_2_elem_weakly(a::NfMaximalOrderIdeal, b::NfMaximalOrderIdeal)
  assert(has_2_elem(a));
  assert(has_2_elem(b));

  O = a.parent.order
  K = O.pari_nf.nf
  bas = basis(O, K)
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

  c = NfMaximalOrderIdeal(norm_int_c, gen, a.parent)

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

function make_pid(A::NfMaximalOrderIdealSet, b::nf_elem)
  d = denominator(b,order(A))
  if d == 1
    return NfMaximalOrderIdeal(b, A)
  else
    return NfMaximalOrderFracIdeal(NfMaximalOrderIdeal(b*d, A), d)
  end
end

function make_pid(A::NfMaximalOrder, b::nf_elem)
  return make_pid(IdealSet(A), b)
end

function prod_by_elt(A::NfMaximalOrderIdeal, b::nf_elem)
  if has_2_elem(A)
    C = NfMaximalOrderIdeal(b, A.parent)
    @assert is_2_normal(C)
    @assert is_2_normal(A)
    return prod(A,C)
  end
  error("not implemented yet...")
end

global last
function prod_by_int(A::NfMaximalOrderIdeal, a::fmpz)
  global last = (A, a)
  @assert has_2_elem(A) && is_2_normal(A)
  if a==1 || a==-1 
    println ("shortcut: returning ", A)
    return A
  end
  println("prod_by_int", A, " and ", a)
  # <a,a> is a a-normal presentation
  # we need to have a common presentation for A and a though
  m = lcm(a, A.gen_one)

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
  B = NfMaximalOrderIdeal(A.gen_one*a, a2*a, A.parent)
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


###########################################################################################
#
# 2-element-normal
#
###########################################################################################

function assure_2_normal(A::NfMaximalOrderIdeal)
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

function inv(A::NfMaximalOrderIdeal) 
  if has_2_elem(A) && is_weakly_normal(A)
    assure_2_normal(A)
    O = order(A)
    alpha = inv(elem_in_nf(A.gen_two))
    d = denominator(alpha, O)
    m = A.gen_one
    g = gcd(m, d)
    while g > 1
      d = div(d, g)
      g = gcd(m, d)
    end
    Ai = parent(A)()
    dn = denominator(d*alpha, O)
    Ai.gen_one = dn 
    Ai.gen_two = O(d*alpha*dn; check = false)
    temp = dn^degree(A.parent.order)//norm(A)
    @hassert :NfMaximalOrder 1 den(temp) == 1
    Ai.norm = num(temp)
    Ai.gens_are_normal = A.gens_are_normal
    return NfMaximalOrderFracIdeal(Ai, dn)
  end
  error("Not implemented yet")
end

###########################################################################################
#
#   Basis
#
###########################################################################################

function has_basis(A::NfMaximalOrderIdeal)
  return isdefined(A, :basis)
end

function basis_mat(A::NfMaximalOrderIdeal)
  if isdefined(A, :basis_mat)
    return A.basis_mat
  end

  @hassert :NfMaximalOrder 1 has_2_elem(A)

  K = nf(order(A))
  n = degree(K)
  c = vcat(representation_mat(order(A)(A.gen_one)), representation_mat(A.gen_two))
  c = hnf(c)
  c = submat(c, 1, 1, n, n)
  A.basis_mat = c
  return c  
end

###########################################################################################
#
#  copy
#
###########################################################################################


###########################################################################################
#
#   simplification
#
###########################################################################################

function simplify(A::NfMaximalOrderIdeal)
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

###########################################################################################
#
#   reduced element in same class
#
###########################################################################################

function reduce_ideal_class(A::NfMaximalOrderIdeal)
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

function valuation(a::nf_elem, p::NfMaximalOrderIdeal)
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

function valuation(a::fmpz, p::NfMaximalOrderIdeal)
  P = p.gen_one
  return valuation(a, P)[1]* p.splitting_type[1]
end

function valuation(A::NfMaximalOrderIdeal, p::NfMaximalOrderIdeal)
  return min(valuation(A.gen_one, p)[1], valuation(A.gen_two, p))
end


###########################################################################################
#
#  prod
#
###########################################################################################

function prod(a::NfMaximalOrderIdeal, b::NfMaximalOrderIdeal)
  if is_2_normal(a) && is_2_normal(b)
    return prod_via_2_elem_normal(a, b)
  end
  if has_2_elem(a) && has_2_elem(b)
    return prod_via_2_elem_weakly(a, b)
  end
  error("algorithm missing")
end

################################################################################
#
#  Comparison
#
################################################################################

# This does not work

#function ==(A::NfMaximalOrderIdeal, B::NfMaximalOrderIdeal)
#  C = simplify(A * inv(B))
#  return norm(C)==1 
#end

# Use bases for the _moment_

function ==(x::NfMaximalOrderIdeal, y::NfMaximalOrderIdeal)
  return basis_mat(x) == basis_mat(y)
end

*(A::NfMaximalOrderIdeal, B::NfMaximalOrderIdeal) = prod(A, B)


function *(O::NfMaximalOrder, a::nf_elem)
  C = make_pid(O, a)
  return C
end

function *(a::nf_elem, O::NfMaximalOrder)
  C = make_pid(O, a)
  return C
end

###########################################################################################
#
#   Parent call overloads
#
###########################################################################################

function Base.call(ord::NfMaximalOrderIdealSet, b::PariIdeal)
   return NfMaximalOrderIdeal(b, ord)
end

function Base.call(S::NfMaximalOrderIdealSet)
   return NfMaximalOrderIdeal(order(S))
end

function Base.call(ord::NfMaximalOrderIdealSet, a::nf_elem)
   return make_pid(ord, a)
end

function Ideal(O::NfMaximalOrder, b::PariIdeal)
  return NfMaximalOrderIdeal(NfMaximalOrderIdealSet(O), b)
end

function Ideal(O::NfMaximalOrder, a::nf_elem)
  return NfMaximalOrderIdealSet(O)(a)
end

function Ideal(O::NfMaximalOrder, a::fmpz_mat)
  return NfMaximalOrderIdeal(a, NfMaximalOrderIdealSet(O))
end

###########################################################################################
#
#   NfMaximalOrder constructor
#
###########################################################################################

function IdealSet(r::NfMaximalOrder)
   return NfMaximalOrderIdealSet(r)
end

###############################################################################
#
#   Extract info from pari-prime ideals (5 component vector) to Nemo objects
#
###########################################################################################

function __prime_ideal_components(id::PariIdeal)
   QQx = id.parent.order.pari_nf.nf.pol.parent
   av = unsafe_load(Nemo.avma, 1)
   p = Nemo.ZZ!(ZZ(), pari_load(id.ideal, 2)) ## the minimum of the prime ideal
   a = Nemo.fmpq_poly!(QQx(), Nemo.residue(Nemo.basistoalg(id.parent.order.pari_nf.data, pari_load(id.ideal, 3)))) ## the 2nd generator
   e = Int(Nemo.ZZ!(ZZ(), pari_load(id.ideal, 4))) ## the ramification
   f = Int(Nemo.ZZ!(ZZ(), pari_load(id.ideal, 5))) ## the inertia
   unsafe_store!(Nemo.avma, av, 1)
   return p, a, e, f
end

