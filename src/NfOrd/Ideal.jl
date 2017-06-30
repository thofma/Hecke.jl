# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
#  Copyright (C) 2015, 2016, 2017 Tommy Hofmann
#  Copyright (C) 2015, 2016, 2017 Claus Fieker 
#
################################################################################

add_verbose_scope(:NfOrd)
add_assert_scope(:NfOrd)

export show, ideal

import Base.isprime

export IdealSet, valuation,prime_decomposition_type, prime_decomposition,
       prime_ideals_up_to, factor, divexact, isramified, anti_uniformizer,
       uniformizer

export NfOrdIdl

export deepcopy, parent, order, basis, basis_mat, basis_mat_inv, minimum, norm,
       ==, in, +, *, intersection, lcm, idempotents, mod, pradical

################################################################################
#
#  Deepcopy
#
################################################################################

# The valuation is an anonymous function which contains A in its environment.
# Thus deepcopying A.valuation will call deepcopy(A) and we run in an
# infinite recursion.
#
# We hack around it by don't deepcopying A.valuation.
# Note that B therefore contains a reference to A (A cannot be freed unless
# B is freed).
function Base.deepcopy_internal(A::NfOrdIdl, dict::ObjectIdDict)
  B = typeof(A)(order(A))
  for i in fieldnames(A)
    if i == :parent
      continue
    end
    if isdefined(A, i)
      if i == :basis
        setfield!(B, i, NfOrdElem[ deepcopy(x) for x in A.basis])
      elseif i == :valuation
        setfield!(B, i, getfield(A, i))
      else
        setfield!(B, i, deepcopy(getfield(A, i)))
      end
    end
  end
  return B
end

################################################################################
#
#  Parent
#
################################################################################

parent(a::NfOrdIdl) = a.parent


#################################################################################
#
#  Parent constructor
#
#################################################################################

function IdealSet(O::NfOrd)
   return NfOrdIdlSet(O)
end
 
elem_type(::Type{NfOrdIdlSet}) = NfOrdIdl

parent_type(::Type{NfOrdIdl}) = NfOrdIdlSet

################################################################################
#
#  Construction
#  Field acess
#
################################################################################

# a (bad) hash function
# - slow (due to basis)
# - unless basis is in HNF it si also non-unique
function hash(A::NfOrdIdl, h::UInt)
  return hash(basis_mat(A), h)
end  

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfOrdIdlSet)
  print(io, "Set of ideals of $(order(a))\n")
end

function show(io::IO, a::NfOrdIdl)
  if ismaximal_known(order(a)) && ismaximal(order(a))
    return show_maximal(io, a)
  else
    return show_gen(io, a)
  end
end

function show_gen(io::IO, a::NfOrdIdl)
  print(io, "Ideal of (")
  print(io, order(a), ")\n")
  print(io, "with basis matrix\n")
  print(io, basis_mat(a))
end

function show_maximal(io::IO, id::NfOrdIdl)
  compact = get(io, :compact, false)
  if compact
    if has_2_elem(id)
      print(io, "<", id.gen_one, ", ", id.gen_two, ">" )
    else
      print(io, "<no 2-elts present>");
    end
  else
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
end

################################################################################
#
#  Copy
#
################################################################################

function copy(i::NfOrdIdl)
  return i
end

################################################################################
#
#  Number field
#
################################################################################

doc"""
***
    nf(x::NfOrdIdl) -> AnticNumberField

> Returns the number field, of which $x$ is an integral ideal.
"""
nf(x::NfOrdIdl) = nf(order(x))


################################################################################
#
#  Parent object overloading and user friendly constructors
#
################################################################################

doc"""
***
    ideal(O::NfOrd, x::NfOrdElem) -> NfOrdIdl

> Creates the principal ideal $(x)$ of $\mathcal O$.
"""
function ideal(O::NfOrd, x::NfOrdElem)
  return NfOrdIdl(deepcopy(x))
end

doc"""
***
    ideal(O::NfOrd, x::fmpz_mat, check::Bool = false) -> NfOrdIdl

> Creates the ideal of $\mathcal O$ with basis matrix $x$. If check is set, then it is
> checked whether $x$ defines an ideal (expensive).
"""
function ideal(O::NfOrd, x::fmpz_mat, check::Bool = false)
  check && error("Not yet implemented")
  return NfOrdIdl(O, deepcopy(x))
end

doc"""
***
    ideal(O::NfOrd, x::fmpz, y::NfOrdElem) -> NfOrdIdl
  
> Creates the ideal $(x,y)$ of $\mathcal O$.
"""
function ideal(O::NfOrd, x::fmpz, y::NfOrdElem)
  return NfOrdIdl(deepcopy(x), deepcopy(y))
end

function ideal(O::NfOrd)
  return NfOrdIdl(O)
end

function (S::NfOrdIdlSet)()
   return NfOrdIdl(order(S))
end

doc"""
***
    ideal(O::NfOrd, a::fmpz) -> NfOrdIdl

> Returns the ideal of $\mathcal O$ which is generated by $a$.
"""
ideal(O::NfOrd, a::fmpz)  = NfOrdIdl(O, deepcopy(a))

doc"""
***
    ideal(O::NfOrd, a::Int) -> NfOrdIdl

> Returns the ideal of $\mathcal O$ which is generated by $a$.
"""
ideal(O::NfOrd, a::Int) = NfOrdIdl(O, a)

order(a::NfOrdIdlSet) = a.order

doc"""
***
    parent(I::NfOrdIdl) -> NfOrd

> Returns the order of $I$.
"""
order(a::NfOrdIdl) = order(parent(a))

################################################################################
#
#  Principal ideal creation
#
################################################################################

doc"""
    *(O::NfOrd, x::NfOrdElem) -> NfOrdIdl
    *(x::NfOrdElem, O::NfOrd) -> NfOrdIdl

> Returns the principal ideal $(x)$ of $\mathcal O$.
"""
function *(O::NfOrd, x::NfOrdElem)
  parent(x) != O && error("Order of element does not coincide with order")
  return ideal(O, x)
end

*(x::NfOrdElem, O::NfOrd) = O*x


################################################################################
#
#  Basic invariants
#
################################################################################

doc"""
***
    norm(A::NfOrdIdl) -> fmpz

> Returns the norm of $A$, that is, the cardinality of $\mathcal O/A$, where
> $\mathcal O$ is the order of $A$.
"""
function norm(A::NfOrdIdl)
  if isdefined(A, :norm)
    return A.norm
  end
  if has_2_elem(A) && A.gens_weakly_normal == 1
    A.norm = gcd(norm(order(A)(A.gen_one)), norm(A.gen_two))
    return A.norm
  end

  if isdefined(A, :princ_gen)
    A.norm = abs(norm(A.princ_gen))
  else
    A.norm = abs(det(basis_mat(A)))
  end
  return A.norm
end

################################################################################
#
#  Minimum
#
################################################################################

doc"""
***
    minimum(A::NfOrdIdl) -> fmpz

> Returns the smallest positive element in $A \cap \mathbf Z$.
"""
function minimum(A::NfOrdIdl)
  if has_minimum(A) 
    return A.minimum
  end

  if isdefined(A, :princ_gen)
    b = A.princ_gen.elem_in_nf
    if iszero(b)
      A.minimum = fmpz(0)
      A.iszero = 1
    else
      bi = inv(b)
      A.minimum =  den(bi, order(A))
    end
    return deepcopy(A.minimum)
  end

  if has_weakly_normal(A)
    K = A.parent.order.nf
    d = den(inv(K(A.gen_two)), A.parent.order)
    d = gcd(d, ZZ(A.gen_one))
    A.minimum = d
    return d
  end

  @hassert :NfOrd 2 isone(basis(order(A))[1])
  A.minimum = basis_mat(A)[1, 1]
  return deepcopy(A.minimum)
end 

################################################################################
#
#  Predicates
#
################################################################################

doc"""
***
    isprime_known(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows if it is prime.
"""
function isprime_known(A::NfOrdIdl)
  return A.is_prime != 0
end

doc"""
***
    isprime(A::NfOrdIdl) -> Bool

> Returns whether $A$ is a prime ideal.
"""
function isprime(A::NfOrdIdl)
  if isprime_known(A)
    return A.is_prime == 1
  elseif minimum(A) == 0
    A.is_prime = 2
    return false
  end
  fac = factor(A)
  if length(fac) == 1 && collect(values(fac))[1] == 1
    A.is_prime = 1
    return true
  else
    A.is_prime = 2
    return false
  end
end

doc"""
***
    has_2_elem(A::NfOrdIdl) -> Bool

> Returns whether $A$ is generated by two elements.
"""
function has_2_elem(A::NfOrdIdl)
  return isdefined(A, :gen_two)
end

doc"""
***
    has_minimum(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows its mininum.
"""
function has_minimum(A::NfOrdIdl)
  return isdefined(A, :minimum)
end

doc"""
***
    has_norm(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows its norm.
"""
function has_norm(A::NfOrdIdl)
  return isdefined(A, :norm)
end

doc"""
***
    has_basis_mat(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows its basis matrix.
"""
function has_basis_mat(A::NfOrdIdl)
  return isdefined(A, :basis_mat)
end

doc"""
***
    has_weakly_normal(A::NfOrdIdl) -> Bool

> Returns whether $A$ has weakly normal two element generators.
""" 
function has_weakly_normal(A::NfOrdIdl)
  return (isdefined(A, :gens_weakly_normal) &&
        A.gens_weakly_normal == true) || has_2_elem_normal(A)
end

doc"""
***
    has_2_elem_normal(A::NfOrdIdl) -> Bool
    
> Returns whether $A$ has normal two element generators.
"""
function has_2_elem_normal(A::NfOrdIdl)
  #the one ideal <1, ?> is automatomatically normal>
  return isdefined(A, :gens_normal) && (A.gen_one == 1 || A.gens_normal > 1)
end

# check if gen_one,gen_two is a P(gen_one)-normal presentation
# see Pohst-Zassenhaus p. 404
function defines_2_normal(A::NfOrdIdl)
  m = A.gen_one
  gen = A.gen_two
  mg = den(inv(gen), order(A))
  # the minimum of ideal generated by g
  g = gcd(m,mg)
  return gcd(m, div(m,g)) == 1
end


doc"""
***
    isone(A::NfOrdIdl) -> Bool
    isunit(A::NfOrdIdl) -> Bool

> Tests if $A$ is the trivial ideal generated by $1$.
"""
function isone(I::NfOrdIdl)
  return isone(minimum(I))
end

function isunit(I::NfOrdIdl)
  return isunit(minimum(I))
end

################################################################################
#
#  Equality
#
################################################################################

doc"""
***
    ==(x::NfOrdIdl, y::NfOrdIdl)

> Returns whether $x$ and $y$ are equal.
"""
function ==(x::NfOrdIdl, y::NfOrdIdl)
  return basis_mat(x) == basis_mat(y)
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

doc"""
***
    in(x::NfOrdElem, y::NfOrdIdl)
    in(x::nf_elem, y::NfOrdIdl)
    in(x::fmpz, y::NfOrdIdl)

> Returns whether $x$ is contained in $y$.
"""
function in(x::NfOrdElem, y::NfOrdIdl)
  parent(x) != order(y) && error("Order of element and ideal must be equal")
  v = transpose(MatrixSpace(FlintZZ, degree(parent(x)), 1)(elem_in_basis(x)))
  t = FakeFmpqMat(v, fmpz(1))*basis_mat_inv(y)
  return t.den == 1
end

function in(x::nf_elem, y::NfOrdIdl)
  parent(x) != nf(order(y)) && error("Number field of element and ideal must be equal")
  return in(order(y)(x),y)
end

in(x::fmpz, y::NfOrdIdl) = in(order(y)(x),y)

################################################################################
#
#  Binary operations
#
################################################################################

doc"""
***
    +(x::NfOrdIdl, y::NfOrdIdl)

> Returns $x + y$.
"""
function +(x::NfOrdIdl, y::NfOrdIdl)
  d = degree(order(x))
  H = vcat(basis_mat(x), basis_mat(y))
  g = gcd(minimum(x), minimum(y))
  if isone(g)
    return ideal(order(x), g)
  end
  H = sub(_hnf_modular_eldiv(H, g, :lowerleft), (d + 1):2*d, 1:d)
  return ideal(order(x), H)
end

doc"""
    intersection(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl
    lcm(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl

> Returns $x \cap y$.
"""
function intersection(x::NfOrdIdl, y::NfOrdIdl)
  d = degree(order(x))
  H = vcat(basis_mat(x), basis_mat(y))
  K = _kernel(H)
  g = lcm(minimum(x),minimum(y))
  return ideal(order(x), _hnf_modular_eldiv(sub(K, 1:d, 1:d)*basis_mat(x), g, :lowerleft))
end

doc"""
    intersection(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl
    lcm(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdIdl

> Returns $x \cap y$.
"""
lcm(x::NfOrdIdl, y::NfOrdIdl) = intersection(x, y)

doc"""
    *(x::NfOrdIdl, y::NfOrdIdl)

> Returns $x \cdot y$.
"""
function *(x::NfOrdIdl, y::NfOrdIdl)
  if ismaximal_known(order(x)) && ismaximal(order(x))
    return mul_maximal(x, y)
  else
    return mul_gen(x, y)
  end
end

function mul_gen(x::NfOrdIdl, y::NfOrdIdl)
  order(x) != order(y) && error("Not compatible")
  O = order(x)
  d = degree(O)
  l = minimum(x)*minimum(y)
  z = MatrixSpace(FlintZZ, degree(O)*degree(O), degree(O))()
  X = basis(x)
  Y = basis(y)
  for i in 1:d
    for j in 1:d
      t = elem_in_basis(X[i]*Y[j])
      for k in 1:d
        z[(i - 1)*d + j, k] = t[k]
      end
    end
  end
  # This is a d^2 x d matrix
  return ideal(O, sub(_hnf_modular_eldiv(z, l, :lowerleft),
                      (d*(d - 1) + 1):d^2, 1:d))
end

# using the 2-normal representation
function prod_via_2_elem_normal(a::NfOrdIdl, b::NfOrdIdl)
  @hassert :NfOrd 1 has_2_elem_normal(a)
  @hassert :NfOrd 1 has_2_elem_normal(b)
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
#    @hassert :NfOrd 1 gcd(a1^degree(O), norm(a2)) == norm(a)
#    @hassert :NfOrd 1 gcd(b1^degree(O), norm(b2)) == norm(b)
##    assert(false)
#  end

  if has_minimum(a) && has_minimum(b) && gcd(minimum(a), minimum(b)) == 1 
    C.minimum = minimum(a) * minimum(b) # otherwise, I don't know the
                                        # correct value
  end

  C.gens_normal = m
  C.gens_weakly_normal = true #for the 1-ideal: it will not be normal...

  return C
end

# using the 2-weak-normal representation
function prod_via_2_elem_weakly(a::NfOrdIdl, b::NfOrdIdl)
  @hassert :NfOrd 1 has_2_elem(a)
  @hassert :NfOrd 1 has_2_elem(b)

  O = order(a)
  K = nf(O)
  bas = basis(O)
  n = degree(O)

  norm_c = norm(a) * norm(b)        # we ARE in the maximal order case
  norm_int_c = norm_c
  mod_c = fmpz(1)
  
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

  @vprint :NfOrd 1 "a: $a \nb: $b"
  @vprint :NfOrd 1 "using basis: $bas"

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

  @vprint :NfOrd 1 "prod_via_2_elem: used $cnt tries\n"

  c = ideal(O, norm_int_c, gen)

  c.norm = norm_c

  if has_minimum(a) && has_minimum(b) && gcd(minimum(a), minimum(b)) == 1 
    c.minimum = minimum(a) * minimum(b)
                    # otherwise, I don't know the correct value
  end

  c.gens_weakly_normal = 1

  return c
end

# dispatching 
doc"""
***
  *(x::NfMaxIdl, y::NfOrdIdl)
    
> Returns the ideal x*y.
"""
function mul_maximal(x::NfOrdIdl, y::NfOrdIdl)
  if x.iszero == 1 || y.iszero == 1
    z = ideal(order(x), zero(MatrixSpace(FlintZZ, degree(order(x)), degree(order(x)))))
    z.iszero = 1
    return z
  end
  if has_2_elem_normal(x) && has_2_elem_normal(y)
    return prod_via_2_elem_normal(x, y)
  end
  if has_2_elem(x) && has_2_elem(y)
    return prod_via_2_elem_weakly(x, y)
  end
  # Fall back to the generic algorithm _mul(::NfOrdIdl, ::NfOrdIdl)
  # Could also use invoke
  return mul_gen(x, y)
end

################################################################################
#
#  Addition
#
################################################################################

# Falls back to generic case +(::NfOrd, ::NfOrd)
#for ideals in the maximal order, the gcd is well defined...

doc"""
***
  gcd(A::NfOrdIdl, B::NfOrdIdl) -> NfOrdIdl
> The gcd or sum (A+B).
"""
function gcd(A::NfOrdIdl, B::NfOrdIdl)
  return A+B
end

function gcd_into!(A::NfOrdIdl, B::NfOrdIdl, C::NfOrdIdl)
  return C+B
end

#TODO: write a ppio versino that allows for p-powers as well
doc"""
***
  gcd(A::NfOrdIdl, p::fmpz) -> NfOrdIdl
> The gcd or sum (A+ pO).
"""
function gcd(A::NfOrdIdl, p::fmpz)
  if isdefined(A, :minimum)
    if gcd(A.minimum, p) == 1
      return ideal(order(A), fmpz(1))
    end
  end
  if isdefined(A, :norm)
    if gcd(A.norm, p) == 1
      return ideal(order(A), fmpz(1))
    end
  end
  if Hecke.has_2_elem(A)
    g = gcd(A.gen_one, p)
    @assert !isone(g)
    return ideal(order(A), g, A.gen_two)
  else
    @assert isdefined(A, :basis_mat)
    return A + ideal(order(A), p)
  end
end


################################################################################
#
#  Ad hoc multiplication
#
################################################################################

# multiplication by fmpz, using two normal presentation
function prod_by_int_2_elem_normal(A::NfOrdIdl, a::fmpz)
  @assert has_2_elem(A) && has_2_elem_normal(A)

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

  B = NfOrdIdl(A.gen_one*a, a2*a)
  B.gens_normal = m

  if has_minimum(A)
    B.minimum = A.minimum * a
  end

  if has_norm(A)
    B.norm = A.norm * a^degree(A.parent.order)
  end

  @assert has_2_elem(B) && has_2_elem_normal(B)
  return B
end

function prod_by_int_2_elem(A::NfOrdIdl, a::fmpz)
  @assert has_2_elem(A)

  B = NfOrdIdl(A.gen_one*a, A.gen_two*a)
  B.gens_normal = A.gens_normal

  if has_minimum(A)
    B.minimum = A.minimum * a
  end

  if has_norm(A)
    B.norm = A.norm * a^degree(A.parent.order)
  end

  @assert has_2_elem(B)
  return B
end



doc"""
***
    *(x::NfOrdIdl, y::fmpz) -> NfOrdIdl

> Returns the ideal $x \cdot y$.
"""
function *(x::NfOrdIdl, y::fmpz)
  if ismaximal_known(order(x)) && ismaximal(order(x))
    return mul_maximal(x, y)
  else
    return mul_gen(x, y)
  end
end

function mul_maximal(x::NfOrdIdl, y::fmpz)
  if y == 1 || y == -1 
    return x
  end

  if has_2_elem(x) 
    if has_2_elem_normal(x)
      return prod_by_int_2_elem_normal(x,y)
# this does not make any sense since prod_by_int_2_elem(x, y) works only if has_2_elem_norm(x) == true
#    else
#      return prod_by_int_2_elem(x,y)
    end  
  end

  return x*ideal(order(x), y)
end

*(x::fmpz, y::NfOrdIdl) = y * x

doc"""
***
    *(x::NfOrdIdl, y::Integer) -> NfOrdIdl

> Returns the ideal $x \cdot y$.
"""
*(x::NfOrdIdl, y::Integer) = x * fmpz(y)

*(x::Integer, y::NfOrdIdl) = y * x

function *(x::NfOrdElem, y::NfOrdIdl)
  parent(x) != order(y) && error("Orders of element and ideal must be equal")
  return ideal(parent(x), x) * y
end

*(x::NfOrdIdl, y::NfOrdElem) = y * x

function mul_gen(x::NfOrdIdl, y::fmpz)
  z = ideal(order(x), basis_mat(x)*y)
  if isdefined(x, :princ_gen)
    z.princ_gen = x.princ_gen * y
  end
  if isdefined(x, :princ_gen_special)
    z.princ_gen_special = (2, 0, x.princ_gen_special[x.princ_gen_special[1] + 1] * y)
  end
  return z
end


################################################################################
#
#  Idempotents
#
################################################################################

doc"""
    idempotents(x::NfOrdIdl, y::NfOrdIdl) -> NfOrdElem, NfOrdElem

> Returns a tuple `(e, f)` consisting of elements `e in x`, `f in y` such that
> `1 = e + f`.
>
> If the ideals are not coprime, an error is raised.
"""
function idempotents(x::NfOrdIdl, y::NfOrdIdl)
  O = order(x)
  d = degree(O)

  # form the matrix
  #
  # ( 1 |  1  | 0 )
  # ( 0 | M_x | I )
  # ( 0 | M_y | 0 )

  V = MatrixSpace(FlintZZ, 1 + 2*d, 1 + 2*d)()

  u = elem_in_basis(one(O))

  V[1, 1] = 1

  for i in 1:d
    V[1, i + 1] = u[i]
  end

  Hecke._copy_matrix_into_matrix(V, 2, 2, basis_mat(x))
  Hecke._copy_matrix_into_matrix(V, 2 + d, 2, basis_mat(y))

  for i in 1:d
    V[1 + i, d + 1 + i] = 1
  end

  H = hnf(V) # upper right

  for i in 2:(1 + d)
    if H[1, i] != 0
      error("Ideals are not coprime")
    end
  end

  z = basis(x)[1]*H[1, d + 2]

  for i in 2:d
    z = z + basis(x)[i]*H[1, d + 1 + i]
  end

  @hassert :NfOrd 2 -z in x
  @hassert :NfOrd 2 1 + z in y

  return -z, 1 + z
end

################################################################################
#
#  Reduction of element modulo ideal
#
################################################################################

doc"""
***
    mod(x::NfOrdElem, I::NfOrdIdl)

> Returns the unique element $y$ of the ambient order of $x$ with
> $x \equiv y \bmod I$ and the following property: If
> $a_1,\dotsc,a_d \in \Z_{\geq 1}$ are the diagonal entries of the unique HNF
> basis matrix of $I$ and $(b_1,\dotsc,b_d)$ is the coefficient vector of $y$,
> then $0 \leq b_i < a_i$ for $1 \leq i \leq d$.
"""
function mod(x::NfOrdElem, y::NfOrdIdl)
  parent(x) != order(y) && error("Orders of element and ideal must be equal")
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape
  
  O = order(y)
  a = elem_in_basis(x)
  #a = deepcopy(b)

  if isdefined(y, :princ_gen_special) && y.princ_gen_special[1] != 0
    for i in 1:length(a)
      a[i] = mod(a[i], y.princ_gen_special[1 + y.princ_gen_special[1]])
    end
    return O(a)
  end

  c = basis_mat(y)
  t = fmpz(0)
  for i in degree(O):-1:1
    t = fdiv(a[i], c[i,i])
    for j in 1:i
      a[j] = a[j] - t*c[i,j]
    end
  end
  z = O(a)
  return z
end

function mod(x::NfOrdElem, y::NfOrdIdl, preinv::Array{fmpz_preinvn_struct, 1})
  parent(x) != order(y) && error("Orders of element and ideal must be equal")
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape
  
  O = order(y)
  a = elem_in_basis(x) # this is already a copy

  if isdefined(y, :princ_gen_special) && y.princ_gen_special[1] != 0
    for i in 1:length(a)
      a[i] = mod(a[i], y.princ_gen_special[1 + y.princ_gen_special[1]])
    end
    return O(a)
  end

  c = basis_mat(y)
  q = fmpz()
  r = fmpz()
  for i in degree(O):-1:1
    fdiv_qr_with_preinvn!(q, r, a[i], c[i, i], preinv[i])
    for j in 1:i
      submul!(a[j], q, c[i, j])
    end
  end

  z = typeof(x)(O, a)
  return z
end

################################################################################
#
#  p-radical
#
################################################################################

# TH:
# There is some annoying type instability since we pass to nmod_mat or
# something else. Should use the trick with the function barrier.
doc"""
***
    pradical(O::NfOrd, p::fmpz) -> NfOrdIdl

> Given a prime number $p$, this function returns the $p$-radical
> $\sqrt{p\mathcal O}$ of $\mathcal O$, which is 
> just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
> \in p\mathcal O \}$. It is not checked that $p$ is prime.
"""
function pradical(O::NfOrd, p::fmpz)
  j = clog(fmpz(degree(O)), p)
  local m::fmpz_mat

  @assert p^(j-1) < degree(O)
  @assert degree(O) <= p^j

  R = ResidueRing(FlintZZ, p)
  A = MatrixSpace(R, degree(O), degree(O))()
  for i in 1:degree(O)
    t = powermod(basis(O)[i], p^j, p)
    ar = elem_in_basis(t)
    for k in 1:degree(O)
      A[i,k] = ar[k]
    end
  end
  X = kernel(A)
  Mat = MatrixSpace(FlintZZ, 1, degree(O))
  MMat = MatrixSpace(R, 1, degree(O))
  if length(X) != 0
    m = lift(MMat(X[1]))
    for x in 2:length(X)
      m = vcat(m,lift(MMat(X[x])))
    end
    m = vcat(m, MatrixSpace(FlintZZ, degree(O), degree(O))(p))
  else
    m = MatrixSpace(FlintZZ, degree(O), degree(O))(p)
  end
  mm::fmpz_mat = _hnf(m, :lowerleft)
  r = sub(mm, rows(m) - degree(O) + 1:rows(m), 1:degree(O))
  return ideal(O, r)
end

doc"""
***
    pradical(O::NfOrd, p::Integer) -> NfOrdIdl

> Given a prime number $p$, this function returns the $p$-radical
> $\sqrt{p\mathcal O}$ of $\mathcal O$, which is 
> just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
> \in p\mathcal O \}$. It is not checked that $p$ is prime.
"""
function pradical(O::NfOrd, p::Integer)
  return pradical(O, fmpz(p))
end

################################################################################
#
#  Ring of multipliers
#
################################################################################

doc"""
***
    ring_of_multipliers(I::NfOrdIdl) -> NfOrd

> Computes the order $(I : I)$, which is the set of all $x \in K$
> with $xI \subseteq I$.
"""
function ring_of_multipliers(a::NfOrdIdl)
  B = basis(a)
  O = order(a)
  bmatinv = basis_mat_inv(a)
  #print("First basis element is $(B[1]) \n with representation mat \n")
  #@vprint :NfOrd 1 "$(representation_mat(B[1]))\n"
  #@vprint :NfOrd 1 FakeFmpqMat(representation_mat(B[1]),ZZ(1))*bmatinv
  m = to_fmpz_mat(FakeFmpqMat(representation_mat(B[1]),ZZ(1))*bmatinv)
  for i in 2:degree(O)
    m = hcat(to_fmpz_mat(FakeFmpqMat(representation_mat(B[i]),ZZ(1))*basis_mat_inv(a)),m)
  end
  n = hnf(transpose(m))
  # n is upper right HNF
  n = transpose(sub(n, 1:degree(O), 1:degree(O)))
  b, d = pseudo_inv(n)
  #z = frac_ideal(O, FakeFmpqMat(b, d))
  return Order(nf(O), FakeFmpqMat(b, d)*basis_mat(O))
end  

###########################################################################################
#
#  2-element normal presentation
#
###########################################################################################

# The following makes sure that A has a weakly normal presentation
# Recall that (x,y) are a weakly normal presentation for A
# if and only if norm(A) = gcd(norm(x), norm(y))
#
# Maybe we should allow an optional paramter (an fmpz),
# which should be the first generator.
# So far, the algorithm just samples (lifts of) random elements of A/m^2,
# where m is the minimum of A.

function _assure_weakly_normal_presentation(A::NfOrdIdl)
  if has_2_elem(A) && has_weakly_normal(A)
    return
  end

  if isdefined(A, :princ_gen)
    x = A.princ_gen
    b = x.elem_in_nf

    bi = inv(b)

    A.gen_one = den(bi, order(A))
    A.minimum = A.gen_one
    A.gen_two = x
    A.norm = abs(num(norm(b)))
    @hassert :NfOrd 1 gcd(A.gen_one^degree(order(A)),
                    ZZ(norm(A.gen_two))) == A.norm

    if A.gen_one == 1
      A.gens_normal = 2*A.gen_one
    else
      A.gens_normal = A.gen_one
    end
    A.gens_weakly_normal = 1
    return nothing
  end

  @hassert :NfOrd 1 has_basis_mat(A)

  O = order(A)

  # Because of the interesting choice for the HNF,
  # we don't know the minimum (although we have a basis matrix)
  # Thanks flint!

  minimum(A)

  @hassert :NfOrd 1 has_minimum(A)

  if minimum(A) == 0
    A.gen_one = minimum(A)
    A.gen_two = zero(O)
    A.gens_weakly_normal = 1
    return nothing
  end

  M = MatrixSpace(FlintZZ, 1, degree(O))

  Amin2 = minimum(A)^2
  Amind = minimum(A)^degree(O)

  B = Array{fmpz}(degree(O))

  gen = O()

  r = -Amin2:Amin2

  m = M()

  cnt = 0
  while true
    cnt += 1

    if cnt > 1000
      println("Having a hard time find weak generators for $A")
    end

    rand!(B, r)

    # Put the entries of B into the (1 x d)-Matrix m
    for i in 1:degree(O)
      s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &m, 0, i - 1)
      ccall((:fmpz_set, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}), s, &B[i])
    end

    if iszero(m) 
      continue
    end

    mul!(m, m, basis_mat(A))
    Q = num(basis_mat(O))
    d = den(basis_mat(O))
    mul!(m, m, Q)
    gen = elem_from_mat_row(nf(O), m, 1, d)
    # the following should be done inplace
    #gen = dot(reshape(Array(mm), degree(O)), basis(O))
    if norm(A) == gcd(Amind, num(norm(gen)))
      A.gen_one = minimum(A)
      A.gen_two = O(gen, false)
      A.gens_weakly_normal = 1
      return nothing
    end
  end
end

function assure_2_normal(A::NfOrdIdl)
  if has_2_elem(A) && has_2_elem_normal(A)
    return
  end 
  O = A.parent.order
  K = nf(O)
  n = degree(K)

  if norm(A) == 1
    A.gen_one = fmpz(1)
    A.gen_two = one(O)
    A.gens_normal = fmpz(1)
    return
  end

  if has_2_elem(A)  && has_weakly_normal(A)
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
      if cnt > 1000
        error("Having a hard time making generators normal for $A")
      end
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

      if iszero(gen)
        continue
      end

      mg = den(inv(elem_in_nf(gen)), O) # the minimum of <gen>
      g = gcd(m, mg)
      if gcd(m, div(mg, g)) == 1 
        if gcd(m^n, norm(gen)) != norm(A)
          @vprint :NfOrd 2 "\n\noffending ideal $A \ngen is $gen\nWrong ideal\n"
          cnt += 10
          continue
        end
        break
      end
    end
    @vprint :NfOrd 2 "used $cnt attempts\n"
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

doc"""
***
    inv(A::NfOrdIdl) -> NfOrdFracIdl

> Computes the inverse of A, that is, the fractional ideal $B$ such that
> $AB = \mathcal O_K$.
"""
function inv(A::NfOrdIdl) 
  if ismaximal_known(order(A)) && ismaximal(order(A))
    return inv_maximal(A)
  else
    error("Not implemented (yet)!")
  end
end

function inv_maximal(A::NfOrdIdl) 
  if has_2_elem(A) && has_weakly_normal(A)
    assure_2_normal(A)
    O = order(A)
    if iszero(A.gen_two)
      return ideal(O, 1)//A.gen_one
    end
    alpha = inv(elem_in_nf(A.gen_two))
    d = den(alpha, O)
    m = A.gen_one
    g = gcd(m, d)
    while g > 1
      d = div(d, g)
      g = gcd(m, d)
    end
    Ai = parent(A)()
    dn = den(d*alpha, O)
    Ai.gen_one = dn 
    Ai.gen_two = O(d*alpha*dn, false)
    temp = dn^degree(A.parent.order)//norm(A)
    @hassert :NfOrd 1 den(temp) == 1
    Ai.norm = num(temp)
    Ai.gens_normal = A.gens_normal
    return NfOrdFracIdl(Ai, dn)
  else
    # I don't know if this is a good idea
    _assure_weakly_normal_presentation(A)
    assure_2_normal(A)
    return inv(A)
  end
  error("Not implemented yet")
end

###########################################################################################
#
#   Basis
#
###########################################################################################

doc"""
***
  has_basis(A::NfOrdIdl) -> Bool

    Returns wether A has a basis already computed.

"""
function has_basis(A::NfOrdIdl)
  return isdefined(A, :basis)
end

doc"""
***
  basis(A::NfOrdIdl) -> Array{NfOrdElem, 1}

> Returns the basis of A
"""
function basis(A::NfOrdIdl)
  if isdefined(A, :basis)
    return A.basis
  else
    O = order(A)
    M = basis_mat(A)
    B = Array{NfOrdElem}(degree(O))
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
    
function basis_mat_prime_deg_1(A::NfOrdIdl)
  @assert A.is_prime == 1
  @assert A.minimum == A.norm
  O = order(A)
  n = degree(O)
  b = MatrixSpace(ZZ, n, n)(1)

  K, mK = ResidueField(O, A)
  bas = basis(O)
  if isone(bas[1])
    b[1,1] = A.minimum
  else
    b[1,1] = fmpz(coeff(mK(-bas[1]), 0))
  end
  for i=2:n
    b[i,1] = fmpz(coeff(mK(-bas[i]), 0))
  end
  return b
end

doc"""
***
  basis_mat(A::NfOrdIdl) -> fmpz_mat

> Returns the basis matrix of $A$.
""" 
function basis_mat(A::NfOrdIdl)
  if isdefined(A, :basis_mat)
    return A.basis_mat
  end

  if isdefined(A, :is_prime) && A.is_prime == 1 && A.norm == A.minimum
    A.basis_mat = basis_mat_prime_deg_1(A)
    return A.basis_mat
  else
#    println("bas mat of $A")
  end

  if isdefined(A, :princ_gen)
    m = representation_mat(A.princ_gen)
    A.basis_mat = _hnf_modular_eldiv(m, minimum(A), :lowerleft)
    return A.basis_mat
  end

  @hassert :NfOrd 1 has_2_elem(A)
  K = nf(order(A))
  n = degree(K)
#  T = MatrixSpace(FlintZZ, n, n)::Nemo.FmpzMatSpace
#  c = vcat(T(A.gen_one)::fmpz_mat, representation_mat(A.gen_two)::fmpz_mat)::fmpz_mat
  #c = modular_hnf(A.gen_one, representation_mat(A.gen_two), :lowerleft)
  c = _hnf_modular_eldiv(representation_mat(A.gen_two), A.gen_one, :lowerleft)
#  c = sub(c, n + 1:2*n, 1:n)
  A.basis_mat = c
  return c
end

doc"""
***
    basis_mat_inv(A::NfOrdIdl) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $A$.
""" 
function basis_mat_inv(A::NfOrdIdl)
  if isdefined(A, :basis_mat_inv)
    return A.basis_mat_inv
  else
    A.basis_mat_inv = FakeFmpqMat(pseudo_inv(basis_mat(A)))
    return A.basis_mat_inv
  end
end

###########################################################################################
#
#  Simplification
#
###########################################################################################
#CF: missing a function to compute the gcd(...) for the minimum 
#    without 1st computing the complete inv

function simplify(A::NfOrdIdl)
  if has_2_elem(A) && has_weakly_normal(A)
    #if maximum(element_to_sequence(A.gen_two)) > A.gen_one^2
    #  A.gen_two = element_reduce_mod(A.gen_two, A.parent.order, A.gen_one^2)
    #end
    if A.gen_one == 1 # || test other things to avoid the 1 ideal
      return A
    end
    A.minimum = gcd(A.gen_one, den(inv(A.gen_two.elem_in_nf), A.parent.order)) 
    A.gen_one = A.minimum
    n = gcd(A.gen_one^degree(A.parent.order), ZZ(norm(A.gen_two)))
    if isdefined(A, :norm)
    end
    A.norm = n
    A.gen_two = mod(A.gen_two, A.gen_one^2)
    return A
  end
end

################################################################################
#
#  Valuation
#
################################################################################

# CF:
# Classical algorithm of Cohen, but take a valuation element with smaller (?)
# coefficients. Core idea is that the valuation elementt is, originally, den*gen_two(p)^-1
# where gen_two(p) is "small". Actually, we don't care about gen_two, we
# need gen_two^-1 to be small, hence this version.
function val_func_no_index(p::NfOrdIdl)
  P = p.gen_one
  K = nf(order(p))
  pi = inv(p)
  d = den(K(pi.num.gen_two))
  @assert gcd(d, P) == 1
  e = K(pi.num.gen_two)*d
  M = MatrixSpace(ZZ, 1, degree(K))()
  elem_to_mat_row!(M, 1, d, e)
  @assert d == 1
  P2 = P^2
  P22 = div(P2, 2)
  for i=1:degree(K)
    x = M[1,i] % P2
    if x>P22
      x -= P2
    end
    M[1,i] = x
  end
  e = elem_from_mat_row(K, M, 1, P)
  # e is still a valuation element, but with smaller coefficients.
  return function(x::nf_elem)
    v = 0
    d = den(x)
    x = x*e
    while den(x) % P != 0
      v += 1
      mul!(x, x, e)
    end
    return v-valuation(d, P)*p.splitting_type[1]
  end
end

# CF:
# The idea is that valuations are mostly small, eg. in the class group
# algorithm. So this version computes the completion and the embedding into it
# at small precision and can thus compute (small) valuation at the effective
# cost of an mod(nmod_poly, nmod_poly) operation.
# Isn't it nice?
function val_func_no_index_small(p::NfOrdIdl)
  P = p.gen_one
  @assert P <= typemax(UInt)
  K = nf(order(p))
  Rx = PolynomialRing(ResidueRing(FlintZZ, P))[1]
  Zx = PolynomialRing(FlintZZ)[1]
  g = Rx(p.gen_two.elem_in_nf)
  f = Rx(K.pol)
  g = gcd!(g, g, f)
  g = lift(Zx, g)
  k = flog(fmpz(typemax(UInt)), P)
  g = hensel_lift(Zx(K.pol), g, P, k)
  Sx = PolynomialRing(ResidueRing(FlintZZ, UInt(P)^k))[1]
  g = Sx(g)
  h = Sx()
  return function(x::nf_elem)
    d = den(x)
    nf_elem_to_nmod_poly_no_den!(h, x) # ignores the denominator
    h = rem!(h, h, g)      
    c = lift(FlintZZ, coeff(h, 0))
    v = c==0 ? typemax(Int) : valuation(c, P)
    for i=1:degree(h)
      c = lift(FlintZZ, coeff(h, i))
      v = min(v, c==0 ? typemax(Int) : valuation(c, P))
    end
    return v-valuation(d, P)
  end
end

function val_func_index(p::NfOrdIdl)
  # We are in the index divisor case. In larger examples, a lot of
  # time is spent computing denominators of order elements.
  # By using the representation matrix to multiply, we can stay in the order
  # and still be fast (faster even than in field).

  pi = inv(p)
  M = representation_mat(pi.num.gen_two)
  O = order(p)
  P = p.gen_one
  return function(x::nf_elem)
    v = 0
    d = den(x, O)
    x *= d
    x_mat = MatrixSpace(FlintZZ, 1, degree(O))(elem_in_basis(O(x)))
    Nemo.mul!(x_mat, x_mat, M)
    while gcd(content(x_mat), P) == P  # should divide and test in place
      divexact!(x_mat, x_mat, P)
      Nemo.mul!(x_mat, x_mat, M)
      v += 1
    end
    return v-valuation(d, P)*p.splitting_type[1]
  end
end

doc"""
***
    valuation(a::nf_elem, p::NfOrdIdl) -> fmpz
    valuation(a::NfOrdElem, p::NfOrdIdl) -> fmpz
    valuation(a::fmpz, p::NfOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
> such that $a$ is contained in $\mathfrak p^i$.
"""
function valuation(a::nf_elem, p::NfOrdIdl)
  @hassert :NfOrd 0 !iszero(a)
  #assert(a !=0) # can't handle infinity yet
  if isdefined(p, :valuation)
    return p.valuation(a)
  end
  O = order(p)
  P = p.gen_one

  # for generic ideals
  if p.splitting_type[2] == 0
    global bad_ideal = p
    p.valuation = function(a::nf_elem)
      d = den(a, O)
      x = O(d*a)
      return valuation_naive(ideal(O, x), p) - valuation_naive(ideal(O, d), p)
    end
    return p.valuation(a)
  end

  if p.splitting_type[1]*p.splitting_type[2] == degree(O)
    p.valuation = function(a::nf_elem)
      return divexact(valuation(norm(a), P)[1], p.splitting_type[2])
    end
  elseif mod(index(O),P) != 0 && p.splitting_type[1] == 1
    if p.gen_one <= typemax(UInt)
      f1 = val_func_no_index_small(p)
      f2 = val_func_no_index(p)
      p.valuation = function(x::nf_elem)
        v = f1(x)
        if v > 100  # can happen ONLY if the precision in the .._small function
                    # was too small.
          return f2(x)
        else 
          return v
        end
      end
    else
      return val_func_no_index(p)
    end
  else
    p.valuation = val_func_index(p)
  end

  return p.valuation(a)
end

doc"""
***
    valuation(a::nf_elem, p::NfOrdIdl) -> fmpz
    valuation(a::NfOrdElem, p::NfOrdIdl) -> fmpz
    valuation(a::fmpz, p::NfOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
> such that $a$ is contained in $\mathfrak p^i$.
"""
valuation(a::NfOrdElem, p::NfOrdIdl) = valuation(a.elem_in_nf, p)

doc"""
***
    valuation(a::nf_elem, p::NfOrdIdl) -> fmpz
    valuation(a::NfOrdElem, p::NfOrdIdl) -> fmpz
    valuation(a::fmpz, p::NfOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
> such that $a$ is contained in $\mathfrak p^i$.
"""
function valuation(a::fmpz, p::NfOrdIdl)
  if p.splitting_type[1] == 0
    return valuation_naive(ideal(order(p), a), p)
  end
  P = p.gen_one
  return valuation(a, P)* p.splitting_type[1]
end

#TODO: some more intelligence here...
function valuation_naive(A::NfOrdIdl, B::NfOrdIdl)
  Bi = inv(B)
  i = 0
  C = simplify(A* Bi)
  while den(C) == 1
    C = simplify(Bi*C)
    i += 1
  end
  return i
end

doc"""
***
    valuation(A::NfOrdIdl, p::NfOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $A$, that is, the largest $i$
> such that $A$ is contained in $\mathfrak p^i$.
"""
function valuation(A::NfOrdIdl, p::NfOrdIdl)
  _assure_weakly_normal_presentation(A) 
  if !isdefined(p, :splitting_type) || p.splitting_type[1] == 0 #ie. if p is non-prime...
    return valuation_naive(A, p)
  end
  return min(valuation(A.gen_one, p), valuation(elem_in_nf(A.gen_two), p))
end

################################################################################
#
#  Prime ideals
#
################################################################################

doc"""
***
    isramified(O::NfOrd, p::Int) -> Bool

> Returns whether the integer $p$ is ramified in $\mathcal O$.
> It is assumed that $p$ is prime.
"""
function isramified(O::NfOrd, p::Int)
  lp = prime_decomposition(O, p)
  for P in lp
    if P[2] > 1
      return true
    end
  end
  return false
end

doc"""
***
    degree(P::NfOrdIdl) -> Int
> The inertia degree of the prime-ideal $P$.
"""
function degree(A::NfOrdIdl)
  @assert isprime(A)
  return A.splitting_type[2]
end

doc"""
***
    ramification_index(P::NfOrdIdl) -> Int
> The ramification index of the prime-ideal $P$.
"""
function ramification_index(A::NfOrdIdl)
  @assert isprime(A)
  return A.splitting_type[1]
end

doc"""
***
    splitting_type(P::NfOrdIdl) -> Int, Int
> The ramification index and inertia degree of the prime ideal $P$.
> First value is the ramificatio index, the second the degree of $P$.
"""
function splitting_type(A::NfOrdIdl)
  @assert isprime(A)
  return A.splitting_type
end

################################################################################
#
#  Prime decomposition
#
################################################################################

##TODO: make fmpz-safe!!!!

doc"""
***
    prime_decomposition(O::NfOrd,
                        p::Integer,
                        degree_limit::Int = 0,
                        lower_limit::Int = 0) -> Array{Tuple{NfOrdIdl, Int}, 1}

> Returns an array of tuples $(\mathfrak p_i,e_i)$ such that $p \mathcal O$ is the product of
> the $\mathfrak p_i^{e_i}$ and $\mathfrak p_i \neq \mathfrak p_j$ for $i \neq j$.
>
> If `degree_limit` is a nonzero integer $k > 0$, then only those prime ideals
> $\mathfrak p$ with $\deg(\mathfrak p) \leq k$ will be returned.
> Similarly if `\lower_limit` is a nonzero integer $l > 0$, then only those prime ideals
> $\mathfrak p$ with $l \leq \deg(\mathfrak p)$ will be returned.
> Note that in this case it may happen that $p\mathcal O$ is not the product of the
> $\mathfrak p_i^{e_i}$.
"""
function prime_decomposition(O::NfOrd, p::Integer, degree_limit::Int = 0, lower_limit::Int = 0)
  if mod(fmpz(index(O)),p) == 0
    return prime_dec_index(O, p, degree_limit, lower_limit)
  end
  return prime_dec_nonindex(O, p, degree_limit, lower_limit)
end

function prime_dec_nonindex(O::NfOrd, p::Integer, degree_limit::Int = 0, lower_limit::Int = 0)
  K = nf(O)
  f = K.pol
  I = IdealSet(O)
  R = parent(f)
  Zx, x = PolynomialRing(FlintIntegerRing(),"x")
  Zf = Zx(f)
  Zmodpx = PolynomialRing(ResidueRing(FlintIntegerRing(), p, cached=false), "y", cached=false)[1]
  fmodp = Zmodpx(Zf)
  fac = factor(fmodp)
  _fac = Dict{typeof(fmodp), Int}()
  if degree_limit == 0
    degree_limit = degree(K)
  end
  for (k,v) in fac
    if degree(k) <= degree_limit && degree(k) >= lower_limit
      _fac[k] = v
    end
  end
  fac = _fac
  result = Array{Tuple{typeof(I()),Int}}(length(fac))
  k = 1
  t = fmpq_poly()
  b = K()
  #fill!(result,(I(),0))
  for (fi, ei) in fac
    t = parent(f)(lift(Zx,fi))
    b = K(t)
    ideal = I()
    ideal.gen_one = p
    ideal.gen_two = O(b, false)
    ideal.is_prime = 1
    ideal.parent = I
    ideal.splitting_type = ei, degree(fi)
    ideal.norm = ZZ(p)^degree(fi)
    ideal.minimum = ZZ(p)

    # We have to do something to get 2-normal presentation:
    # if ramified or valuation val(b,P) == 1, (p,b)
    # is a P(p)-normal presentation
    # otherwise we need to take p+b
    # I SHOULD CHECK THAT THIS WORKS

    if !((mod(norm(b),(ideal.norm)^2) != 0) || (ei > 1))
      ideal.gen_two = ideal.gen_two + O(p)
    end

    ideal.gens_normal = p
    ideal.gens_weakly_normal = true

    # Find an "anti-uniformizer" in case P is unramified
    # We don't call it anti-unfiformizer anymore

    #if ideal.splitting_type[1] == 1
    #  t = parent(f)(lift(Zx, divexact(fmodp, fi)))
    #  ideal.anti_uniformizer = O(K(t), false)
    #end

    if length(fac) == 1 && ideal.splitting_type[2] == degree(f)
      # Prime number is inert, in particular principal
      ideal.is_principal = 1
      ideal.princ_gen = O(p)
    end
    result[k] =  (ideal, ei)
    k += 1
  end
  return result
end

function prime_dec_index(O::NfOrd, p::Int, degree_limit::Int = 0, lower_limit::Int = 0)
  if degree_limit == 0
    degree_limit = degree(O)
  end

  if haskey(O.index_div, fmpz(p))
    lp = O.index_div[fmpz(p)]
    println("retrieving info...")
    return [(p, e) for (p,e) = lp if degree(p) <= degree_limit]
  end

  # Firstly compute the p-radical of O
  Ip = pradical(O, p)
  R = quoringalg(O, Ip, p)
  AA = split(R)

  I = IdealSet(O)
  result = Array{Tuple{typeof(I()),Int}, 1}()
  # We now have all prime ideals, but only their basis matrices
  # We need the ramification indices and a 2-element presentation

  for j in 1:length(AA)
    P = AA[j].ideal
    f = 0

    # First compute the residue degree
    for i in 1:degree(O)
      f = f + valuation(basis_mat(P)[i,i], fmpz(p))
    end

    P.norm = fmpz(p)^f
    P.splitting_type = (0, f)

    if f > degree_limit || f < lower_limit
      continue
    end

    # The following does not work if there is only one prime ideal
    if length(AA) > 1 && (1-1/p)^degree(O) < 0.1
      # Finding the second element might take some time
      @vprint :NfOrd 1 "chances are very low: ~$((1-1/p)^degree(O))"
      # This is rougly Algorithm 6.4 of Belabas' "Topics in comptutational algebraic
      # number theory".

      # Compute Vp = P_1 * ... * P_j-1 * P_j+1 * ... P_g
      if j == 1
        Vp = AA[2].ideal
        k = 3
      else
        Vp = AA[1].ideal;
        k = 2;
      end

      for i in k:length(AA)
        if i == j
          continue
        else
          Vp = intersection(Vp, AA[i].ideal)
        end
      end

      u, v = idempotents(P, Vp)

      x = zero(parent(u))

      if !iszero(mod(norm(u), norm(P)*p))
        x = u
      elseif !iszero(mod(norm(u + p), norm(P)*p))
        x = u + p
      elseif !iszero(mod(norm(u - p), norm(P)*p))
        x = u - p
      else
        for i in 1:degree(O)
          if !iszero(mod(norm(v*basis(P)[i] + u), norm(P)*p))
            x = v*basis(P)[i] + u
          end
        end
      end

      @hassert :NfOrd 1 !iszero(x)
      @hassert :NfOrd 2 O*O(p) + O*x == P
      
      P.gen_one = p
      P.gen_two = x
      P.gens_normal = p
      P.gens_weakly_normal = 1
    else
      _assure_weakly_normal_presentation(P)
      assure_2_normal(P)
    end

    e = Int(valuation(nf(O)(p), P))
    P.splitting_type = e, f
    P.is_prime = 1
    push!(result, (P, e))
  end
  if degree_limit >= degree(O)
    O.index_div[fmpz(p)] = result
  end
  return result
end

function uniformizer(P::NfOrdIdl)
  p = minimum(P)
  if P.gens_normal == p
    return P.gen_two
  else
    if p > 250
      r = 500  # should still have enough elements...
    else
      r = Int(div(p, 2))
    end
    while true
      z = rand(P, r)
      if valuation(z, P) == 1
        break
      end
    end
  end
end

# Belabas p. 40
function anti_uniformizer(P::NfOrdIdl)
  if isdefined(P, :anti_uniformizer)
    return P.anti_uniformizer
  else
    p = minimum(P)
    M = representation_mat(uniformizer(P))
    Mp = MatrixSpace(ResidueRing(FlintZZ, p), rows(M), cols(M))(M)
    p > typemax(Int) && error("Not yet implemented")
    K = kernel(Mp)
    @assert length(K) > 0
    P.anti_uniformizer = elem_in_nf(order(P)(_lift(K[1])))//p
    return P.anti_uniformizer
  end
end

doc"""
***
    anti_uniformizers(d::Dict{NfOrdIdl, Int})
    
> Given a dictionary of prime ideals, the function returns a set of independent anti-uniformizers

"""
function anti_uniformizers(d::Dict{NfOrdIdl, Int})
  
  
  anti_uni=Dict{NfOrdIdl, nf_elem}()
  for (q,v) in d
    anti_uni[q]=Hecke.anti_uniformizer(q)
    found=true
    for (q1,v1) in d
      if q!= q1 && valuation(anti_uni[q],q1)!=0
        found=false
        break
      end
    end
    while found==false
      p = minimum(q)
      if p > 250
        r = 500  # should still have enough elements...
      else
        r = Int(div(p, 2))
      end
      z=rand(q,r)
      while true   
        if z!= 0 && valuation(z, q) == 1
          break
        end
        z = rand(q, r)
      end
      M = representation_mat(z)
      Mp = MatrixSpace(ResidueRing(FlintZZ, p), rows(M), cols(M))(M)
      p > typemax(Int) && error("Not yet implemented")
      K = Hecke.kernel(Mp)
      @assert length(K) > 0
      i=1
      while i<length(K)
        q.anti_uniformizer = elem_in_nf(order(q)(Hecke._lift(K[i])))//p
        anti_uni[q]=q.anti_uniformizer
        found=true
        for (q1,v1) in d
          if q!= q1 && valuation(anti_uni[q],q1)!=0
            found=false
            break
          end
        end
        i=i+1
      end
    end
  end
  
  return anti_uni
  
end






# Don't use the following function. It does not work for index divisors
# TH: Or does it?
function prime_decomposition_type(O::NfOrd, p::Integer)
  if (mod(discriminant(O), p)) != 0 && (mod(fmpz(index(O)), p) != 0)
    K = nf(O)
    f = K.pol
    R = parent(f)
    Zx, x = PolynomialRing(ZZ,"x")
    Zf = Zx(f)
    fmodp = PolynomialRing(ResidueRing(ZZ,p, cached = false), "y", cached = false)[1](Zf)
    fac = factor_shape(fmodp)
    g = sum([ x for x in values(fac)])
    res = Array{Tuple{Int, Int}}(g)
    k = 1
    for (fi, ei) in fac 
      for j in 1:ei
        res[k] = (fi, 1)
        k = k + 1
      end
    end
  else
    lp = prime_decomposition(O, p)
    res = Array{Tuple{Int, Int}}(length(lp))
    for i in 1:length(lp)
      res[i] = (lp[i][1].splitting_type[2], lp[i][1].splitting_type[1])
    end
  end
  return res
end

doc"""
***
    prime_ideals_up_to(O::NfOrd,
                       B::Int;
                       degree_limit::Int = 0) -> Array{NfOrdIdl, 1}

> Computes the prime ideals $\mathcal O$ with norm up to $B$.
> 
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
"""
function prime_ideals_up_to(O::NfOrd, B::Int;
                            complete::Bool = false,
                            degree_limit::Int = 0)
  p = 1
  r = NfOrdIdl[]
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    if !complete
      deg_lim = Int(floor(log(B)/log(p)))
      if degree_limit >0
        deg_lim = min(deg_lim, degree_limit)
      end
    else
      deg_lim = 0
    end
    @vprint :ClassGroup 2 "decomposing $p ... (bound is $B, deg_lim $deg_lim)\n"
    li = prime_decomposition(O, p, deg_lim)
    for P in li
      push!(r, P[1])
    end
  end
  return r
end

doc"""
***
    prime_ideals_over(O::NfOrd,
                       lp::AbstractArray{Int, 1};
                       degree_limit::Int = 0) -> Array{NfOrdIdl, 1}

> Computes the prime ideals $\mathcal O$ over prime numbers in $lp$.
> 
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
"""
function prime_ideals_over{T <: Union{fmpz, Integer}}(O::NfOrd, lp::AbstractArray{T};
                            degree_limit::Int = 0)
  p = 1
  r = NfOrdIdl[]
  for p in lp
    @vprint :ClassGroup 2 "decomposing $p ... (deg_lim $deg_lim)"
    li = prime_decomposition(O, p, degree_limit)
    for P in li
      push!(r, P[1])
    end
  end
  return r
end


doc"""
***
    prime_ideals_up_to(O::NfOrd,
                       B::Int;
                       complete::Bool = false,
                       degree_limit::Int = 0,
                       F::Function,
                       bad::fmpz)

> Computes the prime ideals $\mathcal O$ with norm up to $B$.
> 
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
>
> The function $F$ must be a function on prime numbers not dividing `bad` such that
> $F(p) = \deg(\mathfrak p)$ for all prime ideals $\mathfrak p$ lying above $p$.
"""
function prime_ideals_up_to(O::NfOrd, B::Int, F::Function, bad::fmpz = discriminant(O);
                            complete::Bool = false,
                            degree_limit::Int = 0)
  p = 1
  r = NfOrdIdl[]
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    if !complete
      deg_lim = flog(fmpz(B), p) # Int(floor(log(B)/log(p)))
      if degree_limit > 0
        deg_lim = min(deg_lim, degree_limit)
      end
    else
      deg_lim = 0
    end
    @vprint :ClassGroup 2 "decomposing $p ... (bound is $B)"
    if mod(bad, p) == 0
      li = prime_decomposition(O, p, deg_lim)
      for P in li
        push!(r, P[1])
      end
    else
      if F(p) <= deg_lim
        li = prime_decomposition(O, p, deg_lim)
        for P in li
          push!(r, P[1])
        end
      end
    end
  end
  return r
end

################################################################################
#
#  Coprime
#
################################################################################
function coprime_base(A::Array{NfOrdIdl, 1}, p::fmpz)
  Ap = [gcd(x, p) for x = A if minimum(x) % p == 0]
  return Hecke.coprime_base_steel(Ap)
end

doc"""
***
    coprime_base(A::Array{NfOrdIdl, 1}) -> Array{NfOrdIdl, 1}
    coprime_base(A::Array{NfOrdElem, 1}) -> Array{NfOrdIdl, 1}
> A coprime base for the (principal) ideals in $A$, ie. the returned array
> generated multiplicatively the same ideals as the input and are pairwise 
> coprime.
"""
function coprime_base(A::Array{NfOrdIdl, 1})
  a = collect(Set(map(minimum, A)))
  a = coprime_base(a)
  C = Array{NfOrdIdl, 1}()

  for p = a
    cp = coprime_base(A, p)
    append!(C, cp)
  end
  return C
end

function coprime_base(A::Array{NfOrdElem, 1})
  O = parent(A[1])
  return coprime_base([ideal(O, x) for x = A])
end

function integral_split(A::NfOrdIdl)
  return A, ideal(Order(A), fmpz(1))
end

################################################################################
#
#  Division
#
################################################################################

# We need to fix the two normal presentation of the trivial ideal
doc"""
***
    divexact(A::NfOrdIdl, y::fmpz) -> NfOrdIdl

> Returns $A/y$ assuming that $A/y$ is again an integral ideal.
"""
function divexact(A::NfOrdIdl, y::fmpz)
#  if has_2_elem(A)
#    z = ideal(order(A), divexact(A.gen_one, y), divexact(A.gen_two, y))
#    if has_basis_mat(A)
#      z.basis_mat = divexact(A.basis_mat, y)
#    end
#  elseif has_basis_mat(A)
  if norm(order(A)(y)) == norm(A)
    return ideal(order(A), one(FlintZZ), order(A)(1))
  else
    m = basis_mat(A)
    z = ideal(order(A), divexact(m, y))
    _assure_weakly_normal_presentation(z)
    assure_2_normal(z)
    return z
  end
end

doc"""
***
    divexact(A::NfOrdIdl, B::NfOrdIdl) -> NfOrdIdl

> Returns $AB^{-1}$ assuming that $AB^{-1}$ is again an integral ideal.
"""
function divexact(A::NfOrdIdl, B::NfOrdIdl)
  # It is assumed that B divides A, that is, A \subseteq B
  t_prod = 0.0
  t_simpl = 0.0
  t_b_mat = 0.0
  t_2_elem_weak = 0.0
  t_2_elem = 0.0

  if norm(A) == norm(B)
    return ideal(order(A), one(FlintZZ), order(A)(1))
  else
    t_prod += @elapsed I = A*inv(B)
    t_simpl += @elapsed simplify_exact(I)
    #t_b_mat += @elapsed B = basis_mat(I)
    I.den != 1 && error("Division not exact")
    #I = ideal(order(A), B.num)
    #t_2_elem_weak += @elapsed _assure_weakly_normal_presentation(I)
    #t_2_elem += @elapsed assure_2_normal(I)
    
    #println("  computation for product: $t_prod")
    #println("  simplification         : $t_simpl")
    #println("  basis matrix           : $t_b_mat")
    #println("  2 weak presentation    : $t_2_elem_weak")
    #println("  2 elem presentation    : $t_2_elem")

    return I.num

  end
end

################################################################################
#
#  Facotrization into prime ideals
#
################################################################################
#TODO: factoring type??? (with unit)
doc"""
***
    factor(A::NfOrdIdl) -> Dict{NfOrdIdl, Int}

> Computes the prime ideal factorization $A$ as a dictionary, the keys being
> the prime ideal divisors:
> If `lp = factor_dict(A)`, then `keys(lp)` are the prime ideal divisors of A
> and `lp[P]` is the `P`-adic valuation of `A` for all `P` in `keys(lp)`.
"""
factor(A::NfOrdIdl) = factor_dict(A)

function factor_dict(A::NfOrdIdl)
  ## this should be fixed
  lf = factor(minimum(A))
  lF = Dict{NfOrdIdl, Int}()
  n = norm(A)
  O = order(A)
  for (i, (p, v)) in enumerate(lf)
    try
      p = Int(p)
    catch
      error("Prime divisor lying over prime > 2^63. Too large.")
    end
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
#  Functions for index divisor splitting
#
################################################################################

type quoringalg <: Ring
  base_order::NfOrd
  ideal::NfOrdIdl
  prime::Int
  basis::Array{NfOrdElem, 1}

  function quoringalg(O::NfOrd, I::NfOrdIdl, p::Int)
    z = new()
    z.base_order = O
    z.ideal = I
    z.prime = p

    # compute a basis
    Amodp = MatrixSpace(ResidueRing(ZZ, p), degree(O), degree(O))(basis_mat(I))
    Amodp = vcat(Amodp, MatrixSpace(ResidueRing(ZZ, p), 1, degree(O))())
    Amodp[1,1] = 1
    Amodp = sub(Amodp, 1:degree(O), 1:degree(O))

    # I think rref can/should also return the rank
    B = rref(Amodp)
    r = rank(B)
    C = zero(MatrixSpace(ResidueRing(ZZ, p), degree(O)-r, degree(O)))
    BB = Array{NfOrdElem}(degree(O) - r)
    pivots = Array{Int}(0)
#    # get he pivots of B
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
    insert!(BB, 1, basis(O)[1])
    z.basis = BB
    return z
  end
end

type quoelem
  parent::quoringalg
  elem::NfOrdElem
  coord::Array{fmpz, 1}

  function quoelem(R::quoringalg, x::NfOrdElem)
    z = new()
    z.parent = R
    z.elem = x
    
    return z
  end
end
    
function _kernel_of_frobenius(R::quoringalg)
  O = R.base_order
  BB = R.basis
  p = R.prime
  C = zero(MatrixSpace(ResidueRing(ZZ, R.prime), length(BB)+1, degree(O)))
  D = zero(MatrixSpace(ResidueRing(ZZ, R.prime), length(BB), degree(O)))
  for i in 1:length(BB)
    A = elem_in_basis(mod(BB[i]^p - BB[i], R.ideal))
    for j in 1:degree(O)
      D[i,j] = A[j]
    end
  end

  DD = NfOrdElem[ dot(BB, _lift(r)) for r in kernel(D) ]

  return [ quoelem(R, r) for r in DD ]
end

function _lift(T::Array{GenRes{fmpz}, 1})
  return [ z.data for z in T ]
end

function *(x::quoelem, y::quoelem)
  z = mod(x.elem * y.elem, x.parent.ideal)
  return quoelem(x.parent, z)
end

function ^(x::quoelem, y::Int)
  z = mod(x.elem^y, x.parent.ideal)
  return quoelem(x.parent, z)
end

function ==(x::quoelem, y::quoelem)
  z = mod(x.elem - y.elem, x.parent.ideal)
  return zero(parent(z)) == z
end

function minpoly(x::quoelem)
  O = x.parent.base_order
  p = x.parent.prime

  A = MatrixSpace(ResidueRing(ZZ, p), 0, degree(O))()
  B = MatrixSpace(ResidueRing(ZZ, p), 1, degree(O))()

  for i in 0:degree(O)
    ar =  elem_in_basis( (x^i).elem)
    for j in 1:degree(O)
      B[1, j] = ar[j]
    end
    A = vcat(A, B)
    K = kernel(A)
    if length(K)>0
      @assert length(K)==1
      f = PolynomialRing(ResidueRing(ZZ, p), "x")[1](K[1])
      return f
    end
  end
  error("cannot find minpoly")
end

function split(R::quoringalg)
  if length(R.basis) == 1
    return [ R ]
  end
  K = _kernel_of_frobenius(R)
  O = R.base_order
  p = R.prime

  k = length(K)

  if k == 1
    # the algebra is a field over F_p
    # the ideal Ip is a prime ideal!
    return [ R ]
  end

  maxit = 1 

  while true
    maxit = maxit + 1
    r = rand(0:p-1, length(K))

    x = quoelem(R, dot([ x.elem for x in K], r))

    if mod((x^p).elem, R.ideal) != mod(x.elem, R.ideal)
      #println("element^p: $(mod((x^p).elem, R.ideal))")
      #println("element: $(mod(x.elem, R.ideal))")
      #println(R.ideal.basis_mat)
      #println(K)
      error("Strange")
    end

    f = minpoly(x)


    if degree(f) < 2 
      continue
    end
    @assert  issquarefree(f)

#    # By theory, all factors should have degree 1 # exploit this if p is small!
    fac = factor(f)
    F = first(keys(fac.fac))
    @assert length(fac) == degree(f)
    H = divexact(f,F)
    E, U, V = gcdx(F, H)
    @assert E == 1
    H = U*F;
    idem = O(coeff(H,0).data)
    for i in 1:degree(H)
      idem = idem + coeff(H,i).data*x.elem^i
    end

    I1 = R.ideal + ideal(O, idem)
    I2 = R.ideal + ideal(O, O(1)-idem)

    return vcat(split(quoringalg(O, I1, p)), split(quoringalg(O, I2, p)))
    break
  end
end



doc"""
*
  extended_euclid(A::NfOrdIdl, B::NfOrdIdl) -> (NfOrdElem, NfOrdElem)

> Returns elements $a \in A$ and $b \in B$ such that $a + b = 1$.
"""
function extended_euclid(A::NfOrdIdl, B::NfOrdIdl)
  @assert order(A) == order(B)
  O = order(A)
  n = degree(O)
  A_mat = hnf(basis_mat(A))
  B_mat = hnf(basis_mat(B))
  @hassert :NfOrd 2 size(A_mat) == (n,n)
  @hassert :NfOrd 2 size(B_mat) == (n,n)
  C = [ A_mat ; B_mat ]
  H, T = hnf_with_transform(C)
  @hassert :NfOrd 2 submat(H,n+1,1,n,n) == 0
  H = submat(H,1,1,n,n)
  H != 1 && error("A and B not coprime")
  X = MatrixSpace(ZZ,1,n)()
  for i in 1:n
    X[1,i] = T[1,i]
  end
  coeffs = X*A_mat
  a = O(vec(Array(coeffs)))
  b = 1 - a
  @hassert :NfOrd 2 a in A
  @hassert :NfOrd 2 b in B
  return a, b
end


function trace_matrix(A::NfOrdIdl)
  g = trace_matrix(order(A))
  b = basis_mat(A)
#  mul!(b, b, g)   #b*g*b' is what we want.
#                  #g should not be changed? b is a copy.
#  mul!(b, b, b')  #TODO: find a spare tmp-mat and use transpose
  return b*g*b'
end

function random_init(I::AbstractArray{NfOrdIdl, 1}; reduce::Bool = true)
  J = collect(I)
  for i=1:length(J)
    a = rand(1:length(J))
    b = rand(1:length(J))
    if reduce && isodd(rand(1:2))
      J[a] = reduce_ideal(J[a]*inv(J[b]))
    else
      J[a] *= J[b]
      if reduce
        J[a] = reduce_ideal(J[a])
      end
    end
  end
  return J
end  

function random_get(J::Array{NfOrdIdl, 1}; reduce::Bool = true)
  a = rand(1:length(J))
  I = J[a]
  b = rand(1:length(J))
  if reduce && isodd(rand(1:2))
    J[a] = reduce_ideal(J[a]*inv(J[b]))
  else
    J[a] *= J[b]
    if reduce
      J[a] = reduce_ideal(J[a])
    end
  end
  return I
end

################################################################################
#
#  Power detection
#
################################################################################

doc"""
    ispower(I::NfOrdIdl) -> Int, NfOrdIdl
    ispower(a::NfOrdFracIdl) -> Int, NfOrdFracIdl
> Writes $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
"""
function ispower(I::NfOrdIdl)
  m = minimum(I)
  if isone(m)
    return 0, I
  end
  d = discriminant(order(I))
  b, a = ppio(m, d) # hopefully: gcd(a, d) = 1 = gcd(a, b) and ab = m

  e, JJ = ispower_unram(gcd(I, a))

  if isone(e)
    return 1, I
  end

  g = e
  J = one(I)
  lp = factor(b)
  for p = keys(lp.fac)
    lP = prime_decomposition(order(I), Int(p))
    for i=1:length(lP)
      P = lP[i][1]
      v = valuation(I, P)
      gn = gcd(v, g)
      if gn == 1 
        return gn, I
      end
      if g != gn
        J = J^div(g, gn)
      end
      if v != 0
        J *= P^div(v, gn)
      end
      g = gn
    end
  end
  return g, JJ^div(e, g)*J
end

function ispower_unram(I::NfOrdIdl)
  m = minimum(I)
  if isone(m)
    return 0, I
  end

  e, ra = ispower(m)
  J = gcd(I, ra)

  II = J^e//I
  II = simplify(II)
  @assert isone(den(II))

  f, s = ispower_unram(num(II))

  g = gcd(f, e)
  if isone(g) 
    return 1, I
  end

  II = inv(s)^div(f, g) * J^div(e, g)
  II = simplify(II)
  @assert isone(den(II))
  JJ = num(II)
  e = g

  return e, JJ
end
      
function ispower(I::NfOrdFracIdl)
  num, den = integral_split(I)
  e, r = ispower(num)
  if e == 1
    return e, I
  end
  f, s = ispower(den)
  g = gcd(e, f)
  return g, r^div(e, g)//s^div(f, g)
end

doc"""
    ispower(A::NfOrdIdl, n::Int) -> Bool, NfOrdIdl 
    ispower(A::NfOrdFracIdl, n::Int) -> Bool, NfOrdFracIdl 
> Computes, if possible, an ideal $B$ s.th. $B^n==A$ holds. In this
> case, {{{true}}} and $B$ are returned.
"""
function ispower(A::NfOrdIdl, n::Int)
  m = minimum(A)
  if isone(m)
    return true, A
  end
  d = discriminant(order(A))
  b, a = ppio(m, d) # hopefully: gcd(a, d) = 1 = gcd(a, b) and ab = m

  fl, JJ = ispower_unram(gcd(A, a), n)
  A = gcd(A, b) # the ramified part

  if !fl
    return fl, A
  end

  J = one(A)
  lp = factor(b)
  for p = keys(lp.fac)
    lP = prime_decomposition(order(A), Int(p))
    for i=1:length(lP)
      P = lP[i][1]
      v = valuation(A, P)
      if v % n != 0
        return false, A
      end
      if v != 0
        J *= P^div(v, n)
      end
    end
  end
  return true, JJ*J
end

function ispower_unram(I::NfOrdIdl, n::Int)
  m = minimum(I)
  if isone(m)
    return true, I
  end

  fl, ra = ispower(m, n)
  if !fl
    return fl, I
  end
  J = gcd(I, ra)

  II = J^n//I
  II = simplify(II)
  @assert isone(den(II))

  fl, s = ispower_unram(num(II), n)

  if !fl
    return fl, I
  end

  II = inv(s)* J
  II = simplify(II)
  @assert isone(den(II))
  JJ = num(II)

  return true, JJ
end

#TODO: check if the integral_plit is neccessary or if one can just use 
#      the existing denominator
function ispower(A::NfOrdFracIdl, n::Int)
  nu, de = integral_split(A)
  fl, nu = ispower(nu, n)
  if !fl 
    return fl, A
  end
  fl, de = ispower(de, n)
  return fl, nu//de
end

function one(A::NfOrdIdl)
  return ideal(order(A), 1)
end


################################################################################
#
#  Conversion to Magma
#
################################################################################
function toMagma(f::IOStream, clg::NfOrdIdl, order::String = "M")
  print(f, "ideal<$(order)| ", clg.gen_one, ", ",
                    elem_in_nf(clg.gen_two), ">")
end

function toMagma(s::String, c::NfOrdIdl, order::String = "M")
  f = open(s, "w")
  toMagma(f, c, order)
  close(f)
end

