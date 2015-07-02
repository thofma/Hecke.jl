################################################################################
#
#   NfMaximalOrderIdeals.jl : ideals in Nemo
#
################################################################################

export NfMaximalOrderIdealSet, NfMaximalOrderIdeal

export IdealSet, minimum, is_prime_known, MaximalOrderIdeal, basis_mat,
       valuation, defines_2_normal, *, /, ==, MaximalOrderIdealSet, norm, Ideal

################################################################################
#
#  Types and memory management
#
################################################################################

NfMaximalOrderIdealSetID = Dict{NfMaximalOrder, Ring}()

type NfMaximalOrderIdealSet <: Ring
  order::NfMaximalOrder
  function NfMaximalOrderIdealSet(O::NfMaximalOrder)
    if haskey(NfMaximalOrderIdealSetID, O)
      return NfMaximalOrderIdealSetID[O]
    else
      r = new(O)
      NfMaximalOrderIdealSetID[O] = r
      return r
    end
  end
end

order(S::NfMaximalOrderIdealSet) = S.order

type NfMaximalOrderIdeal <: GenNfOrdIdeal
  basis::Array{NfMaximalOrderElem, 1}
  basis_mat::fmpz_mat
  gen_one::fmpz
  gen_two::NfMaximalOrderElem
  gens_short::Bool
  gens_normal::fmpz
  gens_weakly_normal::Bool # true if Norm(A) = gcd(Norm, Norm)
                           # weaker than normality - at least potentialy
  norm::fmpz
  minimum::fmpz
  is_prime::Int            # 0: don't know
                           # 1 known to be prime
                           # 2 known to be not prime
  is_principal::Int        # as above
  princ_gen::NfMaximalOrderElem
  splitting_type::Tuple{Int, Int}

  valuation::Function      # a function returning "the" valuation -
                           # mind that the ideal is not prime

  parent::NfMaximalOrderIdealSet

  function NfMaximalOrderIdeal(A::PariIdeal, ord::NfMaximalOrderIdealSet)
    r = new()
    O = ord.order
    K = nf(O)
    #@hassert :NfMaximalOrder 1 K == A.parent.order.pari_nf.nf
    p, a, e, f = __prime_ideal_components(A)
    r.gen_one = p
    r.gen_two = O(K(a))
    r.norm = p^f
    r.minimum = p
    r.is_prime = 1
    r.gens_normal = p
    r.gens_weakly_normal = 1
    r.parent = ord
    r.splitting_type = e, f
    return r
  end

  function NfMaximalOrderIdeal(a::fmpz_mat, par::NfMaximalOrderIdealSet)
    r = new()
    r.basis_mat = a
    r.parent = par
    r.gens_short = false
    r.gens_weakly_normal = false
    r.is_prime = 0
    r.is_prime = 0
    r.splitting_type = (0,0)
    return r
  end

  function NfMaximalOrderIdeal(a::fmpz, b::NfMaximalOrderElem)
    r = new()
    r.gen_one = a
    r.gen_two = b
    r.parent = NfMaximalOrderIdealSet(parent(b))
    return r
  end
  
  function NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz, b::nf_elem)
    r = new()
    (x,y) = _check_elem_in_order(b,O)
    @hassert :NfMaximalOrder x
    r.gen_one = a
    r.gen_two = O(b, y)
    r.parent = NfMaximalOrderIdealSet(O)
    return r
  end

  function NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz,
                  b::NfMaximalOrderElem)
    r = new()
    r.gen_one = a
    r.gen_two = b
    r.parent = NfMaximalOrderIdealSet(O)
    return r
  end

  function NfMaximalOrderIdeal(O::NfMaximalOrder)
    r = new()
    r.parent = NfMaximalOrderIdealSet(O)
    r.gens_short = false
    r.gens_weakly_normal = false
    r.is_prime = 0
    r.is_prime = 0
    r.splitting_type = (0,0)
    return r
  end
  
  function NfMaximalOrderIdeal(O::NfMaximalOrder, b::nf_elem)
    
    # check if element is contained in maximal order
    (x,y) = _check_elem_in_order(b,O)
    @hassert :NfMaximalOrder x

    bi = inv(b)

    C = new()
    C.parent = NfMaximalOrderIdealSet(O)
    C.gen_one = denominator(bi, O)
    C.minimum = C.gen_one
    C.gen_two = O(b, y)
    C.norm = abs(num(norm(b)))
    @hassert :NfMaximalOrder 1 gcd(C.gen_one^degree(O),
                    ZZ(norm(C.gen_two))) == C.norm
    C.princ_gen = C.gen_two

    if C.gen_one == 1
      C.gens_normal = 2*C.gen_one
    else
      C.gens_normal = C.gen_one
    end
    C.gens_weakly_normal = 1
    return C
  end
end

parent(x::NfMaximalOrderIdeal) = x.parent

order(x::NfMaximalOrderIdeal) = order(parent(x))

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

################################################################################
#
#  String I/O
#
################################################################################

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
   if isdefined(id, :basis_mat)
     print(io, "\nbasis_mat \n", id.basis_mat)
   end
  if isdefined(id, :gens_normal)
    print(io, "\ntwo normal wrt: ", id.gens_normal)
  end
end

function vshow(A)
  for i in fieldnames(typeof(A))
    if isdefined(A, i)
      println("$i: ")
      println(getfield(A, i), "\n")
    end
  end
end

################################################################################
#
#  Standard predicates
#
################################################################################

function norm(A::NfMaximalOrderIdeal)
  if isdefined(A, :norm)
    return A.norm
  end
  if has_2_elem(A) && A.gens_weakly_normal == 1
    A.norm = gcd(norm(K(A.gen_one)), norm(A.gen_two))
    return A.norm
  end
  @hassert :NfMaximalOrder 1 has_2_elem(A) || has_basis_mat(A)
  O = parent(A)
  if has_basis_mat(A)
    A.norm = abs(determinant(basis_mat(A)))
    return A.norm
  else
    A.norm = abs(determinant(basis_mat(A)))
    return A.norm
  end
end

function minimum(A::NfMaximalOrderIdeal)
  if has_minimum(A) 
    return A.minimum
  end
  if is_weakly_normal(A)
    println(has_2_elem(A))
    vshow(A)
    d = denominator(inv(A.gen_two), A.parent.order)
    d = gcd(d, ZZ(A.gen_one))
    A.minimum = d
    return d
  end
  A.minimum = basis_mat(A)[1,1]
  return fmpz(A.minimum)
  @hassert :NfNfMaximalOrder 0 false
end 

function is_prime_known(A::NfMaximalOrderIdeal)
  return A.is_prime != 0
end

function has_2_elem(A::NfMaximalOrderIdeal)
  return isdefined(A, :gen_two)
end

function has_minimum(A::NfMaximalOrderIdeal)
  return isdefined(A, :minimum)
end

function has_norm(A::NfMaximalOrderIdeal)
  return isdefined(A, :norm)
end

function has_basis_mat(A::NfMaximalOrderIdeal)
  return isdefined(A, :basis_mat)
end

function is_weakly_normal(A::NfMaximalOrderIdeal)
  return (isdefined(A, :gens_weakly_normal) &&
        A.gens_weakly_normal == true) || is_2_normal(A)
end

function is_2_normal(A::NfMaximalOrderIdeal)
  return isdefined(A, :gens_normal) && A.gens_normal > 1
end

# check if gen_one,gen_two is a P(gen_one)-normal presentation
# see Pohst-Zassenhaus p. 404

function defines_2_normal(A::NfMaximalOrderIdeal)
  m = A.gen_one
  gen = A.gen_two
  mg = denominator(inv(gen), order(A))
  # the minimum of ideal generated by g
  g = gcd(m,mg)
  return gcd(m,div(m,g)) == 1
end

################################################################################
#
#  Multplication
#
################################################################################

# using the 2-normal representation

function prod_via_2_elem_normal(a::NfMaximalOrderIdeal, b::NfMaximalOrderIdeal)
  @hassert :NfMaximalOrder 1 is_2_normal(a)
  @hassert :NfMaximalOrder 1 is_2_normal(b)
  O = order(a)
  a1 = a.gen_one
  b1 = b.gen_one
  m = lcm(a1, b1)
  e, f = ppio(m, a1)
  if f == 1
    a2 = a.gen_two
  else
    g, x, y = gcdx(f, a1^2) # we need to become normal at m, we are normal at a
                            # higher powers in a are fine
                            # CRT: the 2nd gen of a needs to stay the same at a
                            # and should be  1 at f
    a2 = a.gen_two*f*x + y*a1^2
                            # now (a1, a2) should be m-normal for a
  end

  e, f = ppio(m, b1)
  if f == 1
    b2 = b.gen_two
  else
    g, x, y = gcdx(f, b1^2)
    b2 = b.gen_two*f*x + y*b1^2
  end
  C = NfMaximalOrderIdeal(O, a1*b1, a2*b2)
  C.norm = norm(a) * norm(b)
  if C.norm != gcd(C.gen_one^degree(O), ZZ(norm(C.gen_two)))
    println("a:", a)
    println("b:", b)
    println("C:", C)
    @hassert :NfMaximalOrder 1 gcd(a1^degree(O), norm(a2)) == norm(a)
    @hassert :NfMaximalOrder 1 gcd(b1^degree(O), norm(b2)) == norm(b)
#    assert(false)
  end

  if has_minimum(a) && has_minimum(b) && gcd(minimum(a), minimum(b)) == 1 
    C.minimum = minimum(a) * minimum(b) # otherwise, I don't know the
                                        # correct value
  end

  C.gens_normal = m

  return C
end

# using the 2-weak-normal representation

function prod_via_2_elem_weakly(a::NfMaximalOrderIdeal, b::NfMaximalOrderIdeal)
  @hassert :NfMaximalOrder 1 has_2_elem(a)
  @hassert :NfMaximalOrder 1 has_2_elem(b)

  O = order(a)
  K = nf(O)
  bas = basis(O)
  n = degree(O)

  norm_c = norm(a) * norm(b)        # we ARE in the maximal order case
  norm_int_c = norm_c
  mod_c = 1
  
  if has_minimum(a) 
    mod_c *= minimum(a)
  else
    mod_c *= norm(a)
  end

  if has_minimum(b) 
    mod_c *= minimum(b)
  else
    mod_c *= norm(b)
  end
  
  # Is this a good idea? Bad magic constants

  if mod_c > 250
    r = -500:500  # should still have enough elements...
  else
    r = -Int(div(mod_c, 2)):Int(div(mod_c, 2))
  end

  @vprint :NfMaximalOrder 1 "a: $a \nb: $b"
  @vprint :NfMaximalOrder 1 "using basis: $bas"

  gen = O()
  gen2 = O()
  t = O()
  s = O()
  u = O()

  cnt = 0
  while true
    cnt += 1
    rand!(t, O, r) # Nemo.rand_into!(bas, r, t)
    r2 = rand(r)
    rand!(s, O, r) # Nemo.rand_into!(bas, r, s)
    r4 = rand(r)
    mul!(t, t, a.gen_two)      # Nemo.mult_into!(t, a.gen_two, t)
    add!(t, t, r2*a.gen_one)   # Nemo.add_into!(t, r2*a.gen_one, t)
    mul!(s, s, b.gen_two)      # Nemo.mult_into!(s, b.gen_two, s)
    add!(s, s, r4*b.gen_one)   # Nemo.add_into!(s, r4*b.gen_one, s)
    mul!(u, s, t)              # Nemo.mult_into!(s, t, u)
    add!(gen, u, gen)          # Nemo.add_into!(u, gen, gen)
#    gen2 += (r1*K(a.gen_two) + r2*a.gen_one) *
#           (r3*K(b.gen_two) + r4*b.gen_one)
    gen = mod(gen, mod_c^2)    # = element_reduce_mod(gen, O, ZZ(mod_c)^2)

    if gcd(norm(gen), norm_int_c^2) == norm_int_c # should be ^n, but for
                                                  # the test ^2 is sufficient
      break
    end
  end

  @vprint :NfMaximalOrder 1 "prod_via_2_elem: used $cnt tries\n"

  c = NfMaximalOrderIdeal(O, norm_int_c, gen)

  c.norm = norm_c

  if has_minimum(a) && has_minimum(b) && gcd(minimum(a), minimum(b)) == 1 
    c.minimum = minimum(a) * minimum(b)
                    # otherwise, I don't know the correct value
  end

  c.gens_weakly_normal = 1

  return c
end

# for all ideals

function *(a::NfMaximalOrderIdeal, b::NfMaximalOrderIdeal)
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
#  Addition
#
################################################################################

function +(a::NfMaximalOrderIdeal, b::NfMaximalOrderIdeal)
  error("algorithm missing")
end

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

function Ideal(O::NfMaximalOrder, x::NfMaximalOrderElem)
  return NfMaximalOrderIdeal(O, x)
end

function Ideal(O::NfMaximalOrder, x::nf_elem)
  return NfMaximalOrderFracIdeal(O, x)
end

#function make_pid(A::NfMaximalOrderIdealSet, b::nf_elem)
#  d = denominator(b,order(A))
#  if d == 1
#    return NfMaximalOrderIdeal(b, A)
#  else
#    return NfMaximalOrderFracIdeal(NfMaximalOrderIdeal(b*d, A), d)
#  end
#end
#
#function make_pid(A::NfMaximalOrder, b::nf_elem)
#  return make_pid(IdealSet(A), b)
#end

#function *(A::NfMaximalOrderIdeal, b::nf_elem)
#  if has_2_elem(A)
#    C = NfMaximalOrderIdeal(b, A.parent)
#    @assert is_2_normal(C)
#    @assert is_2_normal(A)
#    return prod(A,C)
#  end
#  error("not implemented yet...")
#end

global last
function prod_by_int(A::NfMaximalOrderIdeal, a::fmpz)
  global last = (A, a)
  @assert has_2_elem(A) && is_2_normal(A)
  if a==1 || a==-1 
    println("shortcut: returning ", A)
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
  B.gens_normal = m
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

# The following makes sure that A has a weakly normal presentation
# Maybe we should allow an optional paramter (an fmpz),
# which should be the first generator.
# So far, the algorithm just samples (lifts of) random elements of A/m^2,
# where m is the minimum of A.

function _assure_weakly_normal_presentation(A::NfMaximalOrderIdeal)
  if has_2_elem(A) && is_weakly_normal(A)
    return
  end

  @hassert :NfMaximalOrder 1 has_basis_mat(A)

  O = order(A)

  # Because of the interesting choice for the HNF,
  # we don't know the minimum (although we have a basis matrix)
  # Thanks flint!

  @hassert :NfMaximalOrder 1 has_minimum(A)

  M = MatrixSpace(ZZ, 1, degree(O))

  Amin2 = minimum(A)^2
  Amind = minimum(A)^degree(O)

  B = Array(BigInt, 1, degree(O))

  gen = O()

  # first compute something weakly normal
  while true
    # Magic constant
    r = -BigInt(Amin2):BigInt(Amin2)
    rand!(B, r)
    m = M(B)
    mm = m * basis_mat(A)
    # the following should be done inplace
    gen = dot(reshape(Array(mm), degree(O)), basis(O))
    if norm(A) == gcd(Amind, norm(gen))
      A.gen_one = minimum(A)
      A.gen_two = gen
      A.gens_weakly_normal = 1
      return nothing
    end
  end
end

function assure_2_normal(A::NfMaximalOrderIdeal)
  if has_2_elem(A) && is_2_normal(A)
    return
  end 
  O = A.parent.order
  K = nf(O)
  n = degree(K)

  if has_2_elem(A)  && is_weakly_normal(A)
    m = minimum(A)
    bas = basis(O)
    # Magic constants
    if m > 1000 
      r = -500:500
    else
      r = -div(Int(m)+1,2):div(Int(m)+1,2)
    end
    #gen = K()
    #s = K()
    gen = zero(O)
    s = O()
    cnt = 0
    while true
      cnt += 1
      #Nemo.rand_into!(bas, r, s)
      rand!(s, O, r)
      #Nemo.mult_into!(s, A.gen_two, s)
      mul!(s, s, A.gen_two)
      #Nemo.add_into!(gen, rand(r)*A.gen_one, gen)
      add!(gen, rand(r)*A.gen_one, gen)
      #Nemo.add_into!(gen, s, gen)
      add!(gen, s, gen)
#      gen += rand(r)*A.gen_one + rand(bas, r)*A.gen_two
      #gen = element_reduce_mod(gen, O, m^2)
      gen = mod(gen, m^2)
      mg = denominator(inv(elem_in_nf(gen)), O) # the minimum of <gen>
      g = gcd(m, mg)
      if gcd(m, div(m, g)) == 1 
        if gcd(m^n, norm(gen)) != norm(A)
          @vprint :NfMaximalOrder 1 "\n\noffending ideal $A \ngen is $gen\nWrong ideal\n"
          cnt += 10
          continue
        end
        break
      end
    end
    @vprint :NfMaximalOrder 1 "used $cnt attempts\n"
    A.gen_one = m
    A.gen_two = gen
    A.gens_normal = m
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
    Ai.gens_normal = A.gens_normal
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
  T = MatrixSpace(FlintZZ, n, n)::Nemo.FmpzMatSpace
  c = vcat(T(A.gen_one)::fmpz_mat, representation_mat(A.gen_two)::fmpz_mat)::fmpz_mat
  c = _hnf(c, :lowerleft)
  c = sub(c, n + 1:2*n, 1:n)
  A.basis_mat = c
  return c::fmpz_mat
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
  @hassert :NfMaximalOrder 0 !iszero(a)
  #assert(a !=0) # can't handle infinity yet
  if isdefined(p, :valuation)
    return p.valuation(a)
  end
  K = nf(order(p))
  pi = inv(p)
  e = divexact(K(pi.num.gen_two), pi.den)
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
  return min(valuation(A.gen_one, p)[1], valuation(elem_in_nf(A.gen_two), p))
end


################################################################################
#
#  prod
#
################################################################################

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

################################################################################
#
#  Prime ideals
#
################################################################################

function prime_decomposition(O::NfMaximalOrder, p::Integer)
  if mod(fmpz(index(O)),p) == 0
    return prime_dec_index(O, p)
  end
  return prime_dec_nonindex(O, p)
end

function prime_dec_nonindex(O::NfMaximalOrder, p::Integer)
  K = nf(O)
  f = K.pol
  I = IdealSet(O)
  R = parent(f)
  Zx, x = PolynomialRing(ZZ,"x")
  Zf = Zx(f)
  fmodp = PolynomialRing(ResidueRing(ZZ, p), "y")[1](Zf)
  fac = factor(fmodp)
  result = Array(Tuple{typeof(I()),Int}, length(fac))
  t = fmpq_poly()
  b = K()
  fill!(result,(I(),0))
  for k in 1:length(fac)
    t = parent(f)(lift(Zx,fac[k][1]))
    b = K(t)
    ideal = I()
    ideal.gen_one = p
    ideal.gen_two = O(b, check = false)
    ideal.is_prime = 1
    ideal.parent = I
    ideal.splitting_type = fac[k][2], degree(fac[k][1])
    ideal.norm = ZZ(p)^degree(fac[k][1])
    ideal.minimum = ZZ(p)

    # We have to do something to get 2-normal presentation:
    # if ramified or valuation val(b,P) == 1, (p,b)
    # is a P(p)-normal presentation
    # otherwise we need to take p+b
    # I SHOULD CHECK THAT THIS WORKS

    if !((mod(norm(b),(ideal.norm)^2) != 0) || (fac[k][2] > 1))
      ideal.gen_two = ideal.gen_two + O(p)
    end

    ideal.gens_normal = p
    ideal.gens_weakly_normal = true

    if length(fac) == 1 && ideal.splitting_type[1] == 1
      # Prime number is inert, in particular principal
      ideal.is_principal = 1
      ideal.princ_gen = O(p)
    end
    result[k] =  (ideal, fac[k][2])
  end
  return result
end

function prime_dec_index(O::NfMaximalOrder, p::Integer)
  # Firstly compute the p-radical of O
  Ip = pradical(O, p)
  # I only want the rank, so it doesn't matter
  BB = _get_fp_basis(O, Ip, p)
  AA = _split_algebra(BB, Ip, p)
  I = IdealSet(O)
  result = Array(Tuple{typeof(I()),Int}, length(AA))
  # We now have all prime ideals, but only their basis matrices
  # We need the ramification indices and a 2-element presentation
  for j in 1:length(AA)
    P = AA[j]
    vshow(P)
    _assure_weakly_normal_presentation(P)
    assure_2_normal(P)
    e = Int(valuation(NfMaximalOrderIdeal(O, nf(O)(p)), P))
    f = 0
    for i in 1:degree(O)
      f = f + valuation(basis_mat(P)[i,i], fmpz(p))[1]
    end
    P.splitting_type = e, f
    P.norm = fmpz(p)^f
    P.is_prime = 1
    result[j] = (P, e)
  end
  return result
end

function _split_algebra(BB::Array{NfMaximalOrderElem}, Ip::NfMaximalOrderIdeal, p::Integer)
  if length(BB) == 1
    return [ Ip ]
  end
  O = order(Ip)
  C = zero(MatrixSpace(ResidueRing(ZZ, p), length(BB)+1, degree(O)))
  D = zero(MatrixSpace(ResidueRing(ZZ, p), length(BB), degree(O)))
  for i in 1:length(BB)
    A = elem_in_basis(mod(BB[i]^p - BB[i], Ip))
    for j in 1:degree(O)
      D[i,j] = A[j]
    end
  end
  r = rank(D)
  k = length(BB) - r
  # k is the dimension of the kernel of x -> x^p - x
  if k == 1
    # the algebra is a field over F_p
    # the ideal Ip is a prime ideal!
    return [ Ip ]
  end
  
  while true
    r = rand(0:p-1, length(BB))
    x = dot(BB,r)
    # now compute the minimal polynomial
    for i in 0:length(BB)
      ar = elem_in_basis(mod(x^i,Ip))
      for j in 1:degree(O)
        C[i+1,j] = ar[j]
      end
    end
    K = kernel(C)
    length(K) == 0 ? continue : nothing
    KK = K[1]
    f = PolynomialRing(ResidueRing(ZZ, p), "x")[1](KK)
    degree(f) < 2 ? continue : nothing
    @hassert :NfMaximalOrder 0 issquarefree(f)
    # By theory, all factors should have degree 1 # exploit this if p is small!
    fac = factor(f)
    F = fac[1][1]
    H = divexact(f,F)
    E, U, V = gcdx(F, H)
    @hassert :NfMaximalOrder 0 E == 1
    H = U*F;
    idem = O(coeff(H,0).data)
    for i in 1:degree(H)
      idem = idem + coeff(H,i).data*x^i
    end
    # build bases for the two new ideals
    I1 = Ip + NfMaximalOrderIdeal(O, elem_in_nf(idem))
    I2 = Ip + NfMaximalOrderIdeal(O, elem_in_nf(O(1)-idem))
    BB1 = _get_fp_basis(O, I1, p)
    BB2 = _get_fp_basis(O, I2, p)
    return vcat(_split_algebra(BB1, I1, p),_split_algebra(BB2, I2, p))
    break
  end
end


function _get_fp_basis(O::NfMaximalOrder, I::NfMaximalOrderIdeal, p::Integer)
  A = basis_mat(I)
  FpMat = MatrixSpace(ResidueRing(ZZ, p), A.r, A.c)
  Amodp = FpMat(A)
  # I think rref can/should also return the rank
  B = rref(Amodp)
  r = rank(B)
  C = zero(MatrixSpace(ResidueRing(ZZ, p), degree(O)-r, A.c))
  BB = Array(NfMaximalOrderElem, degree(O) - r)
  pivots = Array(Int, 0)
  # get he pivots of B
  for i in 1:r
    for j in 1:degree(O)
      if !iszero(B[i,j])
        push!(pivots, j)
        break
      end
    end
  end
  i = 1
  k = 1
  while i <= degree(O)-r
    for j in k:degree(O)
      if !in(j, pivots)
        BB[i] = basis(O)[j]
        C[i,j] = 1
        k = j + 1
        i = i + 1
        break
      end
    end
  end
  return BB
end

function mod(x::NfMaximalOrderElem, y::NfMaximalOrderIdeal)
  # *** minimum doesn't work so use norm
  # this function assumes that HNF is upper right 
  # !!! This must be changes as soon as HNF is lower left
  O = order(y)
  b = elem_in_basis(x)
  a = copy(b)
  b = basis_mat(y)
  t = fmpz(0)
  for i in 1:degree(O)
    k = degree(O) - i + 1
    t = div(a[k],b[k,k])
    for j in 1:k
      a[j] = a[j] - t*b[k,j]
    end
  end
  return O(a)
end

function prime_decomposition_type(O::NfMaximalOrder, p::Integer)
  K = nf(O)
  f = K.pol
  R = parent(f)
  Zx, x = PolynomialRing(ZZ,"x")
  Zf = Zx(f)
  fmodp = PolynomialRing(ResidueRing(ZZ,p), "y")(Zf)
  fac = factor_shape(fmodp)
  return fac
end

# The following function needs a clean up and a proper name
# Maybe two functions?

function prime_ideals_up_to(O::NfMaximalOrder, B::Int;
                            complete = true,
                            degree_limit = 0)
  p = 1
  r = NfMaximalOrderIdeal[]
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    li = prime_decomposition(O, p)
    if !complete
      if degree_limit <= 0
        for P in li
          if norm(P[1]) <= B
            push!(r, P[1])
          end
        end
      else 
        for P in li
          if norm(P[1]) <= B && P[1].splitting_type[2] < degree_limit
            push!(r, P[1])
          end
        end
      end
    else
      for P in li
        push!(r, P[1])
      end
    end
  end
  return r
end

function factor_dict(A::NfMaximalOrderIdeal)
  lf = my_factor(minimum(A))
  lF = Dict{typeof(A), Int}()
  n = norm(A)
  O = order(A)
  for (i, (p, v)) in enumerate(lf)
    lP = prime_decomposition(O, p)
    for P in lP
      v = valuation(A, P[1])
      if v != 0
        lF[P[1]] = v
        n = n//norm(P[1])^v
      end
      if n == 1 
        return lF
      end
    end
  end
  return lF
end

################################################################################
#
#  Compute the p-radical of an order
#
################################################################################

function ideal(O::NfMaximalOrder, x::fmpz_mat)
  return NfMaximalOrderIdeal(x, NfMaximalOrderIdealSet(O))
end

function +(x::NfMaximalOrderIdeal, y::NfMaximalOrderIdeal)
  H = sub(_hnf(vcat(basis_mat(x),basis_mat(y)), :lowerleft), degree(order(x))+1:2*degree(order(x)), 1:degree(order(x)))::fmpz_mat
  return NfMaximalOrderIdeal(H, parent(x))
end

function mod(a::NfMaximalOrderElem, m::fmpz)
  ar = copy(elem_in_basis(a))
  for i in 1:degree(parent(a))
    ar[i] = mod(ar[i],m)
  end
  return parent(a)(ar)
end

dot(x::BigInt, y::NfMaximalOrderElem) = x * y

colon(start::fmpz, stop::fmpz) = StepRange(start, fmpz(1), stop)

test(a::Int) = fmpz(a)
test2(a::Int) = FlintZZ(a)
