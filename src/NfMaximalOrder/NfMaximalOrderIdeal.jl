################################################################################
#
#   NfMaximalOrderIdeals.jl : ideals in Nemo
#
################################################################################

export NfMaximalOrderIdealSet, NfMaximalOrderIdeal

export IdealSet, minimum, is_prime_known, MaximalOrderIdeal, basis_mat,
       valuation, defines_2_normal, *, /, ==, MaximalOrderIdealSet, norm, Ideal,
       prime_decomposition_type, prime_decomposition

################################################################################
#
#  NfMaximalOrderIdealSet
#
################################################################################

const NfMaximalOrderIdealSetID = ObjectIdDict()

type NfMaximalOrderIdealSet <: Ring
  order::NfMaximalOrder
  function NfMaximalOrderIdealSet(O::NfMaximalOrder)
    if haskey(NfMaximalOrderIdealSetID, O)
      return NfMaximalOrderIdealSetID[O]::NfMaximalOrderIdealSet
    else
      r = new(O)
      NfMaximalOrderIdealSetID[O] = r
      return r
    end
  end
end

###########################################################################################
#
#  User friendly constructor
#
###########################################################################################

function IdealSet(O::NfMaximalOrder)
   return NfMaximalOrderIdealSet(O)
end

################################################################################
#
#  Field acess
#
################################################################################

order(S::NfMaximalOrderIdealSet) = S.order

################################################################################
#
#  NfMaximalOrderIdeal
#
################################################################################

@doc """
  NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz_mat) -> NfMaximalOrderIdeal

    Creates the ideal of O with basis matrix a.
    No sanity checks. No data is copied, a should not be used anymore.

  NfMaximalOrderIdeal(a::fmpz, b::NfOrderElem) -> NfMaximalOrderIdeal

    Creates the ideal (a,b) of the order of b.
    No sanity checks. Note data is copied, a and b should not be used anymore.
  
  NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz, b::nf_elem) -> NfMaximalOrderIdeal

    Creates the ideal (a,b) of O.
    No sanity checks. No data is copied, a and b should be used anymore.
  
  NfMaximalOrderIdeal(x::NfOrderElem) -> NfMaximalOrderIdeal

    Creates the principal ideal (x) of the order of O.
    No sanity checks. No data is copied, x should not be used anymore.

""" ->
type NfMaximalOrderIdeal <: GenNfOrdIdl
  basis::Array{NfOrderElem, 1}
  basis_mat::fmpz_mat
  basis_mat_inv::FakeFmpqMat
  gen_one::fmpz
  gen_two::NfOrderElem
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
  princ_gen::NfOrderElem
  splitting_type::Tuple{Int, Int}

  valuation::Function      # a function returning "the" valuation -
                           # mind that the ideal is not prime

  parent::NfMaximalOrderIdealSet
  
  function NfMaximalOrderIdeal(O::NfMaximalOrder)
    # populate the bits types (Bool, Int) with default values
    r = new()
    r.parent = NfMaximalOrderIdealSet(O)
    r.gens_short = false
    r.gens_weakly_normal = false
    r.is_prime = 0
    r.is_principal = 0
    r.splitting_type = (0,0)
    return r
  end

  function NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz_mat)
    # create ideal of O with basis_matrix a
    # Note that the constructor 'destroys' a, a should not be used anymore
    r = NfMaximalOrderIdeal(O)
    r.basis_mat = a
    return r
  end

  function NfMaximalOrderIdeal(a::fmpz, b::NfOrderElem)
    # create ideal (a,b) of order(b)
    r = NfMaximalOrderIdeal(parent(b))
    r.gen_one = a
    r.gen_two = b
    return r
  end
 
  function NfMaximalOrderIdeal(O::NfMaximalOrder, a::fmpz, b::nf_elem)
    # create ideal (a,b) of O
    r = NfMaximalOrderIdeal(a, O(b, false))
    return r
  end

  function NfMaximalOrderIdeal(x::NfOrderElem)
    # create ideal (x) of parent(x)
    # Note that the constructor 'destroys' x, x should not be used anymore
    O = parent(x)
    b = x.elem_in_nf

    bi = inv(b)

    C = NfMaximalOrderIdeal(O)
    C.gen_one = denominator(bi, O)
    C.minimum = C.gen_one
    C.gen_two = x
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

################################################################################
#
#  Parent object overloading and user friendly constructors
#
################################################################################

@doc """
ideal(O::NfMaximalOrder, x::nf_elem, check::Bool = true) -> NfMaximalOrderIdeal

    Creates the principal ideal (x) of O. If check is set, then containment of
    x in O will be checked. Data will be copied.

""" ->
function ideal(O::NfMaximalOrder, x::nf_elem, check::Bool = true)
  # Data will be copied, as O(x) will copy data.
  if check
    (b,y) = _check_elem_in_order(x,O)
    !b && error("Element not contained in the order")
    return NfMaximalOrderIdeal(O(x, y))
  else
    return NfMaximalOrderIdeal(O(x, false))
  end
end

@doc """
  ideal(O::NfMaximalOrder, x::nf_elem, check::Bool = true) -> NfMaximalOrderIdeal

    Creates the principal ideal (x) of O. Data will be copied.

""" ->
function ideal(O::NfMaximalOrder, x::NfOrderElem)
  return NfMaximalOrderIdeal(deepcopy(x))
end

@doc """
  ideal(O::NfMaximalOrder, x::fmpz_mat, check::Bool = false) -> NfMaximalOrderIdeal

    Creates the ideal of O with basis matrix x. If check is set, then it is
    checked wether x defines an ideal (expensive). Data will be copied.

""" ->
function ideal(O::NfMaximalOrder, x::fmpz_mat)
  return NfMaximalOrderIdeal(O, deepcopy(x))
end

@doc """
  ideal(O::NfMaximalOrder, x::fmpz, y::NfOrderElem) -> NfMaximalOrderIdeal
  
    Creates the ideal (x,y) of O. Data will be copied.

""" ->
function ideal(O::NfMaximalOrder, x::fmpz, y::NfOrderElem)
  return NfMaximalOrderIdeal(deepcopy(x), deepcopy(y))
end

@doc """
  ideal(O::NfMaximalOrder) -> NfMaximalOrderIdeal

    Creates an empty object of type NfMaximalOrderIdeal.

""" ->
function ideal(O::NfMaximalOrder)
  return NfMaximalOrderIdeal(O)
end


function call(S::NfMaximalOrderIdealSet)
   return NfMaximalOrderIdeal(order(S))
end

################################################################################
#
#  Field access
#
################################################################################

@doc """
  parent(x::NfMaximalOrderIdeal) -> NfMaximalOrderIdealSet

    Returns the set of ideals to which x belongs.

""" ->
parent(x::NfMaximalOrderIdeal) = x.parent

@doc """
  order(x::NfMaximalOrderIdeal) -> NfMaximalOrder

    Returns the order, of which x is an ideal.

""" ->
order(x::NfMaximalOrderIdeal) = order(parent(x))

@doc """
  nf(x::NfMaximalOrderIdeal) -> NfNumberField

    Returns the number field, of which x is an integral ideal.

""" ->
nf(x::NfMaximalOrderIdeal) = nf(order(x))

@doc """
  deepcopy(x::NfMaximalOrderIdeal) -> NfMaximalOrderIdeal

    Returns a copy of the ideal x.

""" ->
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

@doc """
  vshow(A::NfMaximalOrderIdeal) -> Void

    Prints all fields of A.

""" ->
function vshow(A)
  for i in fieldnames(typeof(A))
    if isdefined(A, i)
      println("$i: ")
      println(getfield(A, i), "\n")
    else
      println("$i: Not definied")
    end
  end
end

################################################################################
#
#  Standard predicates
#
################################################################################

@doc """
  norm(A::NfMaximalOrderIdeal) -> fmpz

    Returns the norm of A, that is, the cardinality of O/A, where O is the order of A.

""" ->
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

@doc """
  minimum(A::NfMaximalOrderIdeal) -> fmpz

    Returns the smallest positive element in 𝐴 ⋂  𝐙.

""" ->
function minimum(A::NfMaximalOrderIdeal)
  if has_minimum(A) 
    return A.minimum
  end
  if is_weakly_normal(A)
    K = A.parent.order.nf
    d = denominator(inv(K(A.gen_two)), A.parent.order)
    d = gcd(d, ZZ(A.gen_one))
    A.minimum = d
    return d
  end
  A.minimum = basis_mat(A)[1,1]
  return fmpz(A.minimum)
  @hassert :NfNfMaximalOrder 0 false
end 

@doc """
  is_prime_known(A::NfMaximalOrderIdeal) -> Bool

    Returns wether A knows if it is prime.

""" ->
function is_prime_known(A::NfMaximalOrderIdeal)
  return A.is_prime != 0
end

@doc """
  has_2_elem(A::NfMaximalOrderIdeal) -> Bool

    Returns wether A is generated by two elements.

""" ->
function has_2_elem(A::NfMaximalOrderIdeal)
  return isdefined(A, :gen_two)
end

@doc """
  has_minimum(A::NfMaximalOrderIdeal) -> Bool

    Returns wether A knows its mininum.

""" ->
function has_minimum(A::NfMaximalOrderIdeal)
  return isdefined(A, :minimum)
end

@doc """
  has_norm(A::NfMaximalOrderIdeal) -> Bool

    Returns wether A knows its norm.

""" ->
function has_norm(A::NfMaximalOrderIdeal)
  return isdefined(A, :norm)
end

@doc """
  has_basis_mat(A::NfMaximalOrderIdeal) -> Bool

    Returns wether A knows its basis matrix.

""" ->
function has_basis_mat(A::NfMaximalOrderIdeal)
  return isdefined(A, :basis_mat)
end

@doc """
  is_weakly_normal(A::NfMaximalOrderIdeal) -> Bool

    Returns wether A has weakly normal two element generators.

""" ->
function is_weakly_normal(A::NfMaximalOrderIdeal)
  return (isdefined(A, :gens_weakly_normal) &&
        A.gens_weakly_normal == true) || is_2_normal(A)
end

@doc """
  is_2_normal(A::NfMaximalOrderIdeal) -> Bool
    
    Returns wether A has normal two element generators.

""" ->
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
  C = ideal(O, a1*b1, a2*b2)
  C.norm = norm(a) * norm(b)
#  
#CF: too expensive, need norm_mod to compute the norm only modulo...
#
#  if C.norm != gcd(C.gen_one^degree(O), ZZ(norm(C.gen_two)))
#    println("a:", a)
#    println("b:", b)
#    println("C:", C)
#    @hassert :NfMaximalOrder 1 gcd(a1^degree(O), norm(a2)) == norm(a)
#    @hassert :NfMaximalOrder 1 gcd(b1^degree(O), norm(b2)) == norm(b)
##    assert(false)
#  end

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

# dispatching 

@doc """
  *(x::NfMaximalOrderIdeal, y::NfMaximalOrderIdeal)
    
    Returns the ideal x*y.

""" ->
function *(x::NfMaximalOrderIdeal, y::NfMaximalOrderIdeal)
  if is_2_normal(x) && is_2_normal(y)
    return prod_via_2_elem_normal(x, y)
  end
  if has_2_elem(x) && has_2_elem(y)
    return prod_via_2_elem_weakly(x, y)
  end
  # Fall back to the generic algorithm _mul(::GenNfOrdIdl, ::GenNfOrdIdl)
  return _mul(x, y)
end

################################################################################
#
#  Addition
#
################################################################################

# Falls back to generic algorithm +(::GenNfOrdIdl, ::GenNfOrdIdl)

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

# multiplication by fmpz, using two normal presentation

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
    g, x, y = gcdx(f, A.gen_one^2)
                           # we need to become normal at m, we are normal at a
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

function *(x::NfMaximalOrderIdeal, y::fmpz)
  if has_2_elem(x) && is_2_normal(x)
    return prod_by_int(x,y)
  else
    error("Algorithm not yet implemented")
  end
end

*(x::fmpz, y::NfMaximalOrderIdeal) = y * x

*(x::NfMaximalOrderIdeal, y::Integer) = x * ZZ(y)

*(x::Integer, y::NfMaximalOrderIdeal) = y * x

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
#  Inverse
#
###########################################################################################

@doc """
  inv(A::NfMaximalOrderIdeal) -> NfMaximalOrderFracIdeal

    Computes the inverse of A.

""" ->
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
    Ai.gen_two = O(d*alpha*dn, false)
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

@doc """
  has_basis(A::NfMaximalOrderIdeal) -> Bool

    Returns wether A has a basis.

""" ->
function has_basis(A::NfMaximalOrderIdeal)
  return isdefined(A, :basis)
end

@doc """
  basis(A::NfMaximalOrder) -> Array{NfOrderElem, 1}

    Returns the basis of A

""" ->
function basis(A::NfMaximalOrderIdeal)
  if isdefined(A, :basis)
    return A.basis
  else
    O = order(A)
    M = basis_mat(A)
    B = Array(NfOrderElem, degree(O))
    y = O()
    for i in 1:degree(O)
      z = O()
      for k in 1:degree(O)
        mul!(y, M[i,k], basis(O)[k])
        add!(z, z, y)
      end
      B[i] = z
    end
    A.basis = B
    return A.basis
  end
end
        
@doc """
  basis_mat(A::NfMaximalOrderIdeal) -> fmpz_mat

    Returns the basis matrix of A.

""" ->
function basis_mat(A::NfMaximalOrderIdeal)
  if isdefined(A, :basis_mat)
    return A.basis_mat
  end

  @hassert :NfMaximalOrder 1 has_2_elem(A)
  K = nf(order(A))
  n = degree(K)
#  T = MatrixSpace(FlintZZ, n, n)::Nemo.FmpzMatSpace
#  c = vcat(T(A.gen_one)::fmpz_mat, representation_mat(A.gen_two)::fmpz_mat)::fmpz_mat
  #c = modular_hnf(A.gen_one, representation_mat(A.gen_two), :lowerleft)
  c = _hnf_modular(representation_mat(A.gen_two), A.gen_one, :lowerleft)
#  c = sub(c, n + 1:2*n, 1:n)
  A.basis_mat = c
  return c::fmpz_mat
end

function basis_mat_inv(A::NfMaximalOrderIdeal)
  if isdefined(A, :basis_mat_inv)
    return A.basis_mat_inv
  else
    A.basis_mat_inv = FakeFmpqMat(pseudo_inverse(basis_mat(A)))
    return A.basis_mat_inv
  end
end

###########################################################################################
#
#  Simplification
#
###########################################################################################

# ??

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
#  Find reduced ideal in the same class
#
###########################################################################################

# The following function is broken

@doc """
  reduce_ideal_class(A::NfMaximalOrderIdeal) -> NfMaximalOrderIdeal, nf_elem

  This function is broken.
""" ->
function reduce_ideal_class(A::NfMaximalOrderIdeal)
  B = inv(A)
  bas = basis_mat(B)
  L = lll(bas[1])
  a = element_from_mat_row(nf(order(A)), L, 1)
  a = divexact(a, bas[2])
  B = prod_by_elt(A, a)
  B = simplify(B)
  return B, a
end

###########################################################################################
#
#  Valuation
#
###########################################################################################

@doc """
  valuation(a::nf_elem, p::NfMaximalOrderIdeal) -> fmpz

    Computes the p-adic valuation of a, that is, the largest i such that a is contained in p^i.

""" ->
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

@doc """
  valuation(a::fmpz, p::NfMaximalOrderIdeal) -> fmpz

    Computes the p-adic valuation of a, that is, the largest i such that a is contained in p^i.

""" ->
function valuation(a::fmpz, p::NfMaximalOrderIdeal)
  P = p.gen_one
  return valuation(a, P)[1]* p.splitting_type[1]
end

@doc """
  valuation(A::NfMaximalOrderIdeal, p::NfMaximalOrderIdeal) -> fmpz

    Computes the p-adic valuation of A, that is, the largest i such that A is contained in p^i.

""" ->
function valuation(A::NfMaximalOrderIdeal, p::NfMaximalOrderIdeal)
  return min(valuation(A.gen_one, p)[1], valuation(elem_in_nf(A.gen_two), p))
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

# at the moment ==(A::NfMaximalOrderIdeal, B::NfMaximalOrderIdeal)
# falls back to ==(A::GenNfOrdIdl, B::GenNfOrdIdl)

################################################################################
#
#  Principal ideals
#
################################################################################

@doc """
  *(O::NfMaximalOrder, a::nf_elem) -> NfMaximalOrderIdeal
  *(a::nf_elem, O::NfMaximalOrder) -> NfMaximalOrderIdeal
    
    Returns the principal ideal (a) of O. Sanity checks are performed.

""" ->
function *(O::NfMaximalOrder, a::nf_elem)
  nf(O) != parent(a) && error("Number field of order must be parent of element")
  return ideal(O, a)
end

*(a::nf_elem, O::NfMaximalOrder) = O*a

@doc """
  *(O::NfMaximalOrder, x::NfOrderElem) -> NfMaximalOrderIdeal
  *(x::NfOrderElem, O::NfMaximalOrder) -> NfMaximalOrderIdeal

    Returns the principal ideal (x) of O. Sanity checks are performed.

""" ->
function *(O::NfMaximalOrder, x::NfOrderElem)
  order(x) != O && error("Order of element does not coincide with order")
  return ideal(O, x)
end

*(x::NfOrderElem, O::NfMaximalOrder) = O*x

################################################################################
#
#   Extract info from pari-prime ideals (5 component vector) to Nemo objects
#
################################################################################

# This function is broken. Pari interfaced got changed.

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

@doc """
  prime_decomposition(O::NfMaximalOrder, p::Integer) -> Array{Tuple{NfMaximalOrderIdeal, Integer}, 1}

    Returns an array of tuples (p_i,e_i) such that pO is the product of the p_i^e_i.

""" ->
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
    ideal.gen_two = O(b, false)
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
    _assure_weakly_normal_presentation(P)
    assure_2_normal(P)
    e = Int(valuation(fmpz(p), P))
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

function _split_algebra(BB::Array{NfOrderElem}, Ip::NfMaximalOrderIdeal, p::Integer)
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
    I1 = Ip + ideal(O, idem)
    I2 = Ip + ideal(O, O(1)-idem)
    
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
  BB = Array(NfOrderElem, degree(O) - r)
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

# Don't use the following functions. It does not work for index divisors
function prime_decomposition_type(O::NfMaximalOrder, p::Integer)
  if (mod(discriminant(O), p)) != 0 && (mod(fmpz(index(O)), p) != 0)
    K = nf(O)
    f = K.pol
    R = parent(f)
    Zx, x = PolynomialRing(ZZ,"x")
    Zf = Zx(f)
    fmodp = PolynomialRing(ResidueRing(ZZ,p), "y")[1](Zf)
    fac = factor_shape(fmodp)
    g = sum([ x[2] for x in fac])
    res = Array(Tuple{Int, Int}, g)
    k = 1
    for i in length(fac)
      for j in 1:fac[i][2]
        res[k] = (fac[i][1], 1)
        k = k + 1
      end
    end
  else
    lp = prime_decomposition(O, p)
    res = Array(Tuple{Int, Int}, length(lp))
    for i in 1:length(lp)
      res[i] = (lp[i][1].splitting_type[2], lp[i][1].splitting_type[1])
    end
  end
  return res
end

@doc """
  prime_ideals_up_to(O::NfMaximalOrder, B::Int; complete::Bool = true, degree_limit::Int = 0)

    Computes the prime ideals with norm up to B with parameters I forogt.
""" ->
function prime_ideals_up_to(O::NfMaximalOrder, B::Int;
                            complete::Bool = true,
                            degree_limit::Int = 0)
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

################################################################################
#
#  Facotrization into prime ideals
#
################################################################################

@doc """
  factor_dict(A::NfMaximalOrderIdeal) -> Dict{NfMaximalOrderIdeal, Int}

    Computes the prime ideal factorization as a dictionary, the keys being the prime ideal divisors.
    If lp = factor_dict(A), then keys(lp) are the prime ideal divisors of A and lp[P] is the P-adic valuation of A for all P in keys(lp).

""" ->
function factor_dict(A::NfMaximalOrderIdeal)
  lf = my_factor(minimum(A))
  lF = Dict{NfMaximalOrderIdeal, Int}()
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

