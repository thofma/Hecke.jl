################################################################################
#
#    NfMaxOrd/Ideal.jl : Ideals of maximal orders in absolute number fields
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
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
# (C) 2015, 2016 Tommy Hofmann
# (C) 2016, 2016 Claus Fieker
#
################################################################################

import Base.isprime

export IdealSet, valuation,prime_decomposition_type, prime_decomposition,
       prime_ideals_up_to, factor, divexact, isramified, anti_uniformizer,
       uniformizer

#################################################################################
#
#  Parent constructor
#
#################################################################################

function IdealSet(O::NfMaxOrd)
   return NfMaxOrdIdlSet(O)
end
 
elem_type(::Type{NfMaxOrdIdlSet}) = NfMaxOrdIdl

################################################################################
#
#  Construction
#  Field acess
#
################################################################################

order(S::NfMaxOrdIdlSet) = S.order

# a (bad) hash function
# - slow (due to basis)
# - unless basis is in HNF it si also non-unique
function hash(A::NfMaxOrdIdl)
  return hash(basis_mat(A))
end  
  
################################################################################
#
#  Parent object overloading and user friendly constructors
#
################################################################################

#doc"""
#***
#    ideal(O::NfMaxOrd, x::nf_elem, check::Bool = true) -> NfMaxOrdIdl
#
#> Creates the principal ideal (x) of O. If check is set, then containment of
#> x in O will be checked. 
#
#"""
#function ideal(O::NfMaxOrd, x::nf_elem, check::Bool = true)
#  # Data will be copied, as O(x) will copy data.
#  if check
#    (b,y) = _check_elem_in_order(x,O)
#    !b && error("Element not contained in the order")
#    return NfMaxOrdIdl(O(x, y))
#  else
#    return NfMaxOrdIdl(O(x, false))
#  end
#end

doc"""
***
    ideal(O::NfOrd, x::NfOrdElem) -> NfOrdIdl

> Creates the principal ideal $(x)$ of $\mathcal O$.
"""
function ideal(O::NfMaxOrd, x::NfOrdElem)
  return NfMaxOrdIdl(deepcopy(x))
end

doc"""
***
    ideal(O::NfMaxOrd, x::fmpz_mat, check::Bool = false) -> NfMaxOrdIdl

> Creates the ideal of $\mathcal O$ with basis matrix $x$. If check is set, then it is
> checked whether $x$ defines an ideal (expensive).
"""
function ideal(O::NfMaxOrd, x::fmpz_mat, check::Bool = false)
  check && error("Not yet implemented")
  return NfMaxOrdIdl(O, deepcopy(x))
end

doc"""
***
    ideal(O::NfMaxOrd, x::fmpz, y::NfOrdElem) -> NfMaxOrdIdl
  
> Creates the ideal $(x,y)$ of $\mathcal O$.
"""
function ideal(O::NfMaxOrd, x::fmpz, y::NfOrdElem)
  return NfMaxOrdIdl(deepcopy(x), deepcopy(y))
end

function ideal(O::NfMaxOrd, x::Int)
  return NfMaxOrdIdl(O, x)
end

function ideal(O::NfMaxOrd, x::fmpz)
  return NfMaxOrdIdl(O, x)
end

function ideal(O::NfMaxOrd)
  return NfMaxOrdIdl(O)
end

function (S::NfMaxOrdIdlSet)()
   return NfMaxOrdIdl(order(S))
end

################################################################################
#
#  Copy
#
################################################################################

function copy(i::NfMaxOrdIdl)
  return i
end

################################################################################
#
#  Number field
#
################################################################################

doc"""
***
    nf(x::NfMaxOrdIdl) -> AnticNumberField

> Returns the number field, of which $x$ is an integral ideal.
"""
nf(x::NfMaxOrdIdl) = nf(order(x))

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, S::NfMaxOrdIdlSet)
   print(io, "Set of ideals of ")
   print(io, order(S))
end

function show(io::IO, id::NfMaxOrdIdl)
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
function norm(A::NfMaxOrdIdl)
  if isdefined(A, :norm)
    return A.norm
  end
  if has_2_elem(A) && A.gens_weakly_normal == 1
    A.norm = gcd(norm(order(A)(A.gen_one)), norm(A.gen_two))
    return A.norm
  end
  @hassert :NfMaxOrd 1 has_2_elem(A) || has_basis_mat(A)
  O = parent(A)
  if has_basis_mat(A)
    A.norm = abs(det(basis_mat(A)))
    return A.norm
  else
    A.norm = abs(det(basis_mat(A)))
    return A.norm
  end
end

################################################################################
#
#  Minimum
#
################################################################################

doc"""
***
    minimum(A::NfMaxOrdIdl) -> fmpz

> Returns the smallest positive element in $A \cap \mathbf Z$.
"""
function minimum(A::NfMaxOrdIdl)
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

  A.minimum = basis_mat(A)[1,1]
  return fmpz(A.minimum)
end 

################################################################################
#
#  Predicates
#
################################################################################

doc"""
***
    isprime_known(A::NfMaxOrdIdl) -> Bool

> Returns whether $A$ knows if it is prime.
"""
function isprime_known(A::NfMaxOrdIdl)
  return A.is_prime != 0
end

doc"""
***
    isprime(A::NfMaxOrdIdl) -> Bool

> Returns whether $A$ is a prime ideal.
"""
function isprime(A::NfMaxOrdIdl)
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
    has_2_elem(A::NfMaxOrdIdl) -> Bool

> Returns whether $A$ is generated by two elements.
"""
function has_2_elem(A::NfMaxOrdIdl)
  return isdefined(A, :gen_two)
end

doc"""
***
    has_minimum(A::NfMaxOrdIdl) -> Bool

> Returns whether $A$ knows its mininum.
"""
function has_minimum(A::NfMaxOrdIdl)
  return isdefined(A, :minimum)
end

doc"""
***
    has_norm(A::NfMaxOrdIdl) -> Bool

> Returns whether $A$ knows its norm.
"""
function has_norm(A::NfMaxOrdIdl)
  return isdefined(A, :norm)
end

doc"""
***
    has_basis_mat(A::NfMaxOrdIdl) -> Bool

> Returns whether $A$ knows its basis matrix.
"""
function has_basis_mat(A::NfMaxOrdIdl)
  return isdefined(A, :basis_mat)
end

doc"""
***
    has_weakly_normal(A::NfMaxOrdIdl) -> Bool

> Returns whether $A$ has weakly normal two element generators.
""" 
function has_weakly_normal(A::NfMaxOrdIdl)
  return (isdefined(A, :gens_weakly_normal) &&
        A.gens_weakly_normal == true) || has_2_elem_normal(A)
end

doc"""
***
    has_2_elem_normal(A::NfMaxOrdIdl) -> Bool
    
> Returns whether $A$ has normal two element generators.
"""
function has_2_elem_normal(A::NfMaxOrdIdl)
  return isdefined(A, :gens_normal) && A.gens_normal > 1
end

# check if gen_one,gen_two is a P(gen_one)-normal presentation
# see Pohst-Zassenhaus p. 404
function defines_2_normal(A::NfMaxOrdIdl)
  m = A.gen_one
  gen = A.gen_two
  mg = den(inv(gen), order(A))
  # the minimum of ideal generated by g
  g = gcd(m,mg)
  return gcd(m, div(m,g)) == 1
end

################################################################################
#
#  Multplication
#
################################################################################

# using the 2-normal representation
function prod_via_2_elem_normal(a::NfMaxOrdIdl, b::NfMaxOrdIdl)
  @hassert :NfMaxOrd 1 has_2_elem_normal(a)
  @hassert :NfMaxOrd 1 has_2_elem_normal(b)
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
#    @hassert :NfMaxOrd 1 gcd(a1^degree(O), norm(a2)) == norm(a)
#    @hassert :NfMaxOrd 1 gcd(b1^degree(O), norm(b2)) == norm(b)
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
function prod_via_2_elem_weakly(a::NfMaxOrdIdl, b::NfMaxOrdIdl)
  @hassert :NfMaxOrd 1 has_2_elem(a)
  @hassert :NfMaxOrd 1 has_2_elem(b)

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

  @vprint :NfMaxOrd 1 "a: $a \nb: $b"
  @vprint :NfMaxOrd 1 "using basis: $bas"

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

  @vprint :NfMaxOrd 1 "prod_via_2_elem: used $cnt tries\n"

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
function *(x::NfMaxOrdIdl, y::NfMaxOrdIdl)
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
  return _mul(x, y)
end

################################################################################
#
#  Addition
#
################################################################################

# Falls back to generic case +(::NfOrd, ::NfOrd)

################################################################################
#
#  Intersection
#
################################################################################

# Falls back to generic algorithm intersection(::NfOrdIdl, ::NfOrdIdl)

################################################################################
#
#  Ad hoc multiplication
#
################################################################################

# multiplication by fmpz, using two normal presentation
function prod_by_int_2_elem_normal(A::NfMaxOrdIdl, a::fmpz)
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

  B = NfMaxOrdIdl(A.gen_one*a, a2*a)
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

doc"""
***
    *(x::NfOrdIdl, y::fmpz) -> NfOrdIdl

> Returns the ideal $x \cdot y$.
"""
function *(x::NfMaxOrdIdl, y::fmpz)
  if y == 1 || y == -1 
    return x
  end

  if has_2_elem(x) && has_2_elem_normal(x)
    return prod_by_int_2_elem_normal(x,y)
  else
    return ideal(order(x), y*basis_mat(x))
  end
end

*(x::fmpz, y::NfMaxOrdIdl) = y * x

doc"""
***
    *(x::NfOrdIdl, y::Integer) -> NfOrdIdl

> Returns the ideal $x \cdot y$.
"""
*(x::NfMaxOrdIdl, y::Integer) = x * fmpz(y)

*(x::Integer, y::NfMaxOrdIdl) = y * x

# The case ideal * element is missing

#function *(A::NfMaxOrdIdl, b::nf_elem)
#  if has_2_elem(A)
#    C = NfMaxOrdIdl(b, A.parent)
#    @assert is_2_normal(C)
#    @assert is_2_normal(A)
#    return prod(A,C)
#  end
#  error("not implemented yet...")
#end

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

function _assure_weakly_normal_presentation(A::NfMaxOrdIdl)
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
    @hassert :NfMaxOrd 1 gcd(A.gen_one^degree(order(A)),
                    ZZ(norm(A.gen_two))) == A.norm

    if A.gen_one == 1
      A.gens_normal = 2*A.gen_one
    else
      A.gens_normal = A.gen_one
    end
    A.gens_weakly_normal = 1
    return nothing
  end

  @hassert :NfMaxOrd 1 has_basis_mat(A)

  O = order(A)

  # Because of the interesting choice for the HNF,
  # we don't know the minimum (although we have a basis matrix)
  # Thanks flint!

  minimum(A)

  @hassert :NfMaxOrd 1 has_minimum(A)

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

function assure_2_normal(A::NfMaxOrdIdl)
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
          @vprint :NfMaxOrd 2 "\n\noffending ideal $A \ngen is $gen\nWrong ideal\n"
          cnt += 10
          continue
        end
        break
      end
    end
    @vprint :NfMaxOrd 2 "used $cnt attempts\n"
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
    inv(A::NfMaxOrdIdl) -> NfMaxOrdFracIdl

> Computes the inverse of A, that is, the fractional ideal $B$ such that
> $AB = \mathcal O_K$.
"""
function inv(A::NfMaxOrdIdl) 
  if has_2_elem(A) && has_weakly_normal(A)
    assure_2_normal(A)
    O = order(A)
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
    @hassert :NfMaxOrd 1 den(temp) == 1
    Ai.norm = num(temp)
    Ai.gens_normal = A.gens_normal
    return NfMaxOrdFracIdl(Ai, dn)
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
  has_basis(A::NfMaxOrdIdl) -> Bool

    Returns wether A has a basis already computed.

"""
function has_basis(A::NfMaxOrdIdl)
  return isdefined(A, :basis)
end

doc"""
***
  basis(A::NfOrdIdl) -> Array{NfOrdElem, 1}

> Returns the basis of A
"""
function basis(A::NfMaxOrdIdl)
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
    
function basis_mat_prime_deg_1(A::NfMaxOrdIdl)
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
function basis_mat(A::NfMaxOrdIdl)
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

  @hassert :NfMaxOrd 1 has_2_elem(A)
  K = nf(order(A))
  n = degree(K)
#  T = MatrixSpace(FlintZZ, n, n)::Nemo.FmpzMatSpace
#  c = vcat(T(A.gen_one)::fmpz_mat, representation_mat(A.gen_two)::fmpz_mat)::fmpz_mat
  #c = modular_hnf(A.gen_one, representation_mat(A.gen_two), :lowerleft)
  c = _hnf_modular_eldiv(representation_mat(A.gen_two), A.gen_one, :lowerleft)
#  c = sub(c, n + 1:2*n, 1:n)
  A.basis_mat = c
  return c::fmpz_mat
end

doc"""
***
    basis_mat_inv(A::NfOrdIdl) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $A$.
""" 
function basis_mat_inv(A::NfMaxOrdIdl)
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

function simplify(A::NfMaxOrdIdl)
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

###########################################################################################
#
#  Find reduced ideal in the same class
#
###########################################################################################

# The following function is broken

doc"""
***
    reduce_ideal_class(A::NfMaxOrdIdl) -> NfMaxOrdIdl, nf_elem

> This function is broken.
"""
function reduce_ideal_class(A::NfMaxOrdIdl)
  B = inv(A)
  bas = basis_mat(B)
  L = lll(bas[1])
  a = element_from_mat_row(nf(order(A)), L, 1)
  a = divexact(a, bas[2])
  B = prod_by_elt(A, a)
  B = simplify(B)
  return B, a
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
function val_func_no_index(p::NfMaxOrdIdl)
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
function val_func_no_index_small(p::NfMaxOrdIdl)
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

function val_func_index(p::NfMaxOrdIdl)
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
    valuation(a::nf_elem, p::NfMaxOrdIdl) -> fmpz
    valuation(a::NfOrdElem, p::NfMaxOrdIdl) -> fmpz
    valuation(a::fmpz, p::NfMaxOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
> such that $a$ is contained in $\mathfrak p^i$.
"""
function valuation(a::nf_elem, p::NfMaxOrdIdl)
  @hassert :NfMaxOrd 0 !iszero(a)
  #assert(a !=0) # can't handle infinity yet
  if isdefined(p, :valuation)
    return p.valuation(a)
  end
  O = order(p)
  P = p.gen_one

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
    valuation(a::nf_elem, p::NfMaxOrdIdl) -> fmpz
    valuation(a::NfOrdElem, p::NfMaxOrdIdl) -> fmpz
    valuation(a::fmpz, p::NfMaxOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
> such that $a$ is contained in $\mathfrak p^i$.
"""
valuation(a::NfOrdElem{NfMaxOrd}, p::NfMaxOrdIdl) = valuation(a.elem_in_nf, p)

doc"""
***
    valuation(a::nf_elem, p::NfMaxOrdIdl) -> fmpz
    valuation(a::NfOrdElem, p::NfMaxOrdIdl) -> fmpz
    valuation(a::fmpz, p::NfMaxOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
> such that $a$ is contained in $\mathfrak p^i$.
"""
function valuation(a::fmpz, p::NfMaxOrdIdl)
  P = p.gen_one
  @assert p.splitting_type[1] != 0
  return valuation(a, P)* p.splitting_type[1]
end

doc"""
***
    valuation(A::NfMaxOrdIdl, p::NfMaxOrdIdl) -> fmpz

> Computes the $\mathfrak p$-adic valuation of $A$, that is, the largest $i$
> such that $A$ is contained in $\mathfrak p^i$.
"""
function valuation(A::NfMaxOrdIdl, p::NfMaxOrdIdl)
  return min(valuation(A.gen_one, p), valuation(elem_in_nf(A.gen_two), p))
end

################################################################################
#
#  Comparison
#
################################################################################

# This does not work

#function ==(A::NfMaxOrdIdl, B::NfMaxOrdIdl)
#  C = simplify(A * inv(B))
#  return norm(C)==1 
#end

# At the moment ==(A::NfMaxOrdIdl, B::NfMaxOrdIdl)
# falls back to ==(A::NfOrdIdl, B::NfOrdIdl)

################################################################################
#
#  Prime ideals
#
################################################################################

doc"""
***
    isramified(O::NfMaxOrd, p::Int) -> Bool

> Returns whether the integer $p$ is ramified in $\mathcal O$.
> It is assumed that $p$ is prime.
"""
function isramified(O::NfMaxOrd, p::Int)
  lp = prime_decomposition(O, p)
  for P in lp
    if P[2] > 1
      return true
    end
  end
  return false
end

################################################################################
#
#  Prime decomposition
#
################################################################################

doc"""
***
    prime_decomposition(O::NfMaxOrd,
                        p::Integer,
                        degree_limit::Int = 0,
                        lower_limit::Int = 0) -> Array{Tuple{NfMaxOrdIdl, Int}, 1}

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
function prime_decomposition(O::NfMaxOrd, p::Integer, degree_limit::Int = 0, lower_limit::Int = 0)
  if mod(fmpz(index(O)),p) == 0
    return prime_dec_index(O, p, degree_limit, lower_limit)
  end
  return prime_dec_nonindex(O, p, degree_limit, lower_limit)
end

function prime_dec_nonindex(O::NfMaxOrd, p::Integer, degree_limit::Int = 0, lower_limit::Int = 0)
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

function prime_dec_index(O::NfMaxOrd, p::Int, degree_limit::Int = 0, lower_limit::Int = 0)
  if degree_limit == 0
    degree_limit = degree(O)
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

    if f > degree_limit || f < lower_limit
      continue
    end

    # The following does not work if there is only one prime ideal
    if length(AA) > 1 && (1-1/p)^degree(O) < 0.1
      # Finding the second element might take some time
      @vprint :NfMaxOrd 1 "chances are very low: ~$((1-1/p)^degree(O))"
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

      @hassert :NfMaxOrd 1 !iszero(x)
      @hassert :NfMaxOrd 2 O*O(p) + O*x == P
      
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
  return result
end

function uniformizer(P::NfMaxOrdIdl)
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
function anti_uniformizer(P::NfMaxOrdIdl)
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

# Don't use the following function. It does not work for index divisors
# TH: Or does it?
function prime_decomposition_type(O::NfMaxOrd, p::Integer)
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
    prime_ideals_up_to(O::NfMaxOrd,
                       B::Int;
                       degree_limit::Int = 0) -> Array{NfMaxOrdIdl, 1}

> Computes the prime ideals $\mathcal O$ with norm up to $B$.
> 
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
"""
function prime_ideals_up_to(O::NfMaxOrd, B::Int;
                            complete::Bool = false,
                            degree_limit::Int = 0)
  p = 1
  r = NfMaxOrdIdl[]
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
    @vprint :ClassGroup 2 "decomposing $p ... (bound is $B, deg_lim $deg_lim)"
    li = prime_decomposition(O, p, deg_lim)
    for P in li
      push!(r, P[1])
    end
  end
  return r
end

doc"""
***
    prime_ideals_over(O::NfMaxOrd,
                       lp::AbstractArray{Int, 1};
                       degree_limit::Int = 0) -> Array{NfMaxOrdIdl, 1}

> Computes the prime ideals $\mathcal O$ over prime numbers in $lp$.
> 
> If `degree_limit` is a nonzero integer $k$, then prime ideals $\mathfrak p$
> with $\deg(\mathfrak p) > k$ will be discarded.
"""
function prime_ideals_over(O::NfMaxOrd, lp::AbstractArray{Int};
                            degree_limit::Int = 0)
  p = 1
  r = NfMaxOrdIdl[]
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
    prime_ideals_up_to(O::NfMaxOrd,
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
function prime_ideals_up_to(O::NfMaxOrd, B::Int, F::Function, bad::fmpz = discriminant(O);
                            complete::Bool = false,
                            degree_limit::Int = 0)
  p = 1
  r = NfMaxOrdIdl[]
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
#  Division
#
################################################################################

# We need to fix the two normal presentation of the trivial ideal
doc"""
***
    divexact(A::NfMaxOrdIdl, y::fmpz) -> NfMaxOrdIdl

> Returns $A/y$ assuming that $A/y$ is again an integral ideal.
"""
function divexact(A::NfMaxOrdIdl, y::fmpz)
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
    divexact(A::NfMaxOrdIdl, B::NfMaxOrdIdl) -> NfMaxOrdIdl

> Returns $AB^{-1}$ assuming that $AB^{-1}$ is again an integral ideal.
"""
function divexact(A::NfMaxOrdIdl, B::NfMaxOrdIdl)
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

doc"""
***
    factor(A::NfMaxOrdIdl) -> Dict{NfMaxOrdIdl, Int}

> Computes the prime ideal factorization $A$ as a dictionary, the keys being
> the prime ideal divisors:
> If `lp = factor_dict(A)`, then `keys(lp)` are the prime ideal divisors of A
> and `lp[P]` is the `P`-adic valuation of `A` for all `P` in `keys(lp)`.
"""
factor(A::NfMaxOrdIdl) = factor_dict(A)

function factor_dict(A::NfMaxOrdIdl)
  ## this should be fixed
  lf = factor(BigInt(minimum(A)))
  lF = Dict{NfMaxOrdIdl, Int}()
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
  base_order::NfMaxOrd
  ideal::NfMaxOrdIdl
  prime::Int
  basis::Array{NfOrdElem, 1}

  function quoringalg(O::NfMaxOrd, I::NfMaxOrdIdl, p::Int)
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
  extended_euclid(A::NfMaxOrdIdl, B::NfMaxOrdIdl) -> (NfOrdElem{NfMaxOrd},NfOrdElem{NfMaxOrd})

> Returns elements $a \in A$ and $b \in B$ such that $a + b = 1$.
"""
function extended_euclid(A::NfMaxOrdIdl, B::NfMaxOrdIdl)
  @assert order(A) == order(B)
  O = order(A)
  n = degree(O)
  A_mat = hnf(basis_mat(A))
  B_mat = hnf(basis_mat(B))
  @hassert :NfMaxOrd 2 size(A_mat) == (n,n)
  @hassert :NfMaxOrd 2 size(B_mat) == (n,n)
  C = [ A_mat ; B_mat ]
  H, T = hnf_with_transform(C)
  @hassert :NfMaxOrd 2 submat(H,n+1,1,n,n) == 0
  H = submat(H,1,1,n,n)
  H != 1 && error("A and B not coprime")
  X = MatrixSpace(ZZ,1,n)()
  for i in 1:n
    X[1,i] = T[1,i]
  end
  coeffs = X*A_mat
  a = O(vec(Array(coeffs)))
  b = 1 - a
  @hassert :NfMaxOrd 2 a in A
  @hassert :NfMaxOrd 2 b in B
  return a, b
end


