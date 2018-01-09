################################################################################
#
#    NfOrd/Ideal/Ideal.jl : Ideals in orders of absolute number fields
#
# This file is part of Hecke.
#
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
#  Copyright (C) 2015, 2016, 2017 Tommy Hofmann
#  Copyright (C) 2015, 2016, 2017 Claus Fieker
#
################################################################################

export show, ideal

export IdealSet, valuation,prime_decomposition_type, prime_decomposition,
       prime_ideals_up_to, factor, divexact, isramified, anti_uniformizer,
       uniformizer, iscoprime

export NfOrdIdl

export deepcopy, parent, order, basis, basis_mat, basis_mat_inv, minimum, norm,
       ==, in, +, *, intersection, lcm, idempotents, mod, pradical


add_assert_scope(:Rres)
new = !true

function toggle()
  global new = !new
end

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
      if i == :valuation
        setfield!(B, i, getfield(A, i))
      else
        setfield!(B, i, Base.deepcopy_internal(getfield(A, i), dict))
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

elem_type(::NfOrdIdlSet) = NfOrdIdl

parent_type(::Type{NfOrdIdl}) = NfOrdIdlSet

################################################################################
#
#  Hashing
#
################################################################################

# a (bad) hash function
# - slow (due to basis)
# - unless basis is in HNF it si also non-unique
function Base.hash(A::NfOrdIdl, h::UInt)
  return Base.hash(basis_mat(A, Val{false}), h)
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

################################################################################
#
#  Basic field access
#
################################################################################

doc"""
***
    order(x::NfOrdIdl) -> NfOrd

> Returns the order, of which $x$ is an ideal.
"""
order(a::NfOrdIdlSet) = a.order

doc"""
***
    nf(x::NfOrdIdl) -> AnticNumberField

> Returns the number field, of which $x$ is an integral ideal.
"""
nf(x::NfOrdIdl) = nf(order(x))


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

###########################################################################################
#
#   Basis
#
###########################################################################################

doc"""
***
    has_basis(A::NfOrdIdl) -> Bool

> Returns whether A has a basis already computed.
"""
@inline has_basis(A::NfOrdIdl) = isdefined(A, :basis)

function assure_has_basis(A::NfOrdIdl)
  if isdefined(A, :basis)
    return nothing
  else
    assure_has_basis_mat(A)
    O = order(A)
    M = A.basis_mat
    Ob = basis(O, Val{false})
    B = Vector{NfOrdElem}(degree(O))
    y = O()
    for i in 1:degree(O)
      z = O()
      for k in 1:degree(O)
        mul!(y, M[i, k], Ob[k])
        add!(z, z, y)
      end
      B[i] = z
    end
    A.basis = B
    return nothing
  end
end

doc"""
***
    basis(A::NfOrdIdl) -> Array{NfOrdElem, 1}

> Returns the basis of A.
"""
@inline function basis{T}(A::NfOrdIdl, copy::Type{Val{T}} = Val{true})
  assure_has_basis(A::NfOrdIdl)
  if copy == Val{true}
    return deepcopy(A.basis)
  else
    return A.basis
  end
end

################################################################################
#
#  Basis matrix
#
################################################################################

doc"""
***
    has_basis_mat(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows its basis matrix.
"""
@inline has_basis_mat(A::NfOrdIdl) = isdefined(A, :basis_mat)

doc"""
***
  basis_mat(A::NfOrdIdl) -> fmpz_mat

> Returns the basis matrix of $A$.
"""
function basis_mat(A::NfOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat(A)
  if copy == Val{true}
    return deepcopy(A.basis_mat)
  else
    return A.basis_mat
  end
end

function assure_has_basis_mat(A::NfOrdIdl)
  if isdefined(A, :basis_mat)
    return nothing
  end

  if isdefined(A, :is_prime) && A.is_prime == 1 && A.norm == A.minimum
    # A is a prime ideal of degree 1
    A.basis_mat = basis_mat_prime_deg_1(A)
    return nothing
  end

  if has_princ_gen(A)
    m = representation_mat(A.princ_gen)
    A.basis_mat = _hnf_modular_eldiv(m, minimum(A), :lowerleft)
    return nothing
  end

  @hassert :NfOrd 1 has_2_elem(A)
  K = nf(order(A))
  n = degree(K)
  c = _hnf_modular_eldiv(representation_mat(A.gen_two), abs(A.gen_one), :lowerleft)
  A.basis_mat = c
  return nothing
end

function basis_mat_prime_deg_1(A::NfOrdIdl)
  @assert A.is_prime == 1
  @assert A.minimum == A.norm
  O = order(A)
  n = degree(O)
  b = identity_matrix(FlintZZ, n)

  K, mK = ResidueField(O, A)
  assure_has_basis(O)
  bas = basis(O, Val{false})
  if isone(bas[1])
    b[1, 1] = A.minimum
  else
    b[1, 1] = fmpz(coeff(mK(-bas[1]), 0))
  end
  for i in 2:n
    b[i, 1] = fmpz(coeff(mK(-bas[i]), 0))
  end
  # b is Hermite normal form, but lower left
  return b
end

################################################################################
#
#  Basis matrix inverse
#
################################################################################

doc"""
***
    has_basis_mat_inv(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows its inverse basis matrix.
"""
@inline has_basis_mat_inv(A::NfOrdIdl) = isdefined(A, :basis_mat_inv)

doc"""
***
  basis_mat_inv(A::NfOrdIdl) -> fmpz_mat

> Returns the inverse basis matrix of $A$.
"""
function basis_mat_inv(A::NfOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat_inv(A)
  if copy == Val{true}
    return deepcopy(A.basis_mat_inv)
  else
    return A.basis_mat_inv
  end
end

doc"""
***
    basis_mat_inv(A::NfOrdIdl) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $A$.
"""
function assure_has_basis_mat_inv(A::NfOrdIdl)
  if isdefined(A, :basis_mat_inv)
    return nothing
  else
    A.basis_mat_inv = FakeFmpqMat(pseudo_inv(basis_mat(A, Val{false})))
    return nothing
  end
end

################################################################################
#
#  Minimum
#
################################################################################

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
    minimum(A::NfOrdIdl) -> fmpz

> Returns the smallest nonnegative element in $A \cap \mathbf Z$.
"""
function minimum(A::NfOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_minimum(A)
  if copy == Val{true}
    return deepcopy(A.minimum)
  else
    return A.minimum
  end
end

function assure_has_minimum(A::NfOrdIdl)
  if has_minimum(A)
    return nothing
  end

  if has_princ_gen(A)
    b = A.princ_gen.elem_in_nf
    if iszero(b)
      A.minimum = fmpz(0)
      A.iszero = 1
    else
      if new && order(A).ismaximal == 1
        A.minimum = _minmod(A.gen_one, A.gen_two)
        bi = inv(b)
        @hassert :Rres 1 A.minimum == denominator(bi, order(A))
      else
        bi = inv(b)
        A.minimum =  denominator(bi, order(A))
      end
    end
    return nothing
  end

  if has_weakly_normal(A)
    K = A.parent.order.nf
    if iszero(A.gen_two)
      # A = (A.gen_one, 0) = (A.gen_one)
      d = abs(A.gen_one)
    else
      d = denominator(inv(K(A.gen_two)), order(A))
      d = gcd(d, FlintZZ(A.gen_one))
    end
    A.minimum = d
    return nothing
  end

  @hassert :NfOrd 2 isone(basis(order(A), Val{false})[1])
  A.minimum = basis_mat(A, Val{false})[1, 1]
  return nothing
end

################################################################################
#
#  Norm
#
################################################################################

doc"""
***
    has_norm(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows its norm.
"""
function has_norm(A::NfOrdIdl)
  return isdefined(A, :norm)
end

function assure_has_norm(A::NfOrdIdl)
  if has_norm(A)
    return nothing
  end

  if has_princ_gen_special(A)
    A.norm = princ_gen_special(A)^degree(order(A))
    return nothing
  end

  if has_princ_gen(A)
    A.norm = abs(norm(A.princ_gen))
    return nothing
  end

  if has_2_elem(A) && A.gens_weakly_normal == 1
    if new 
      A.norm = _normmod(A.gen_one^degree(order(A)), A.gen_two)
      @hassert :Rres 1 A.norm == gcd(norm(order(A)(A.gen_one)), norm(A.gen_two))
    else  
      A.norm = gcd(norm(order(A)(A.gen_one)), norm(A.gen_two))
    end  
    return nothing
  end

  assure_has_basis_mat(A)
  A.norm = abs(det(basis_mat(A, Val{false})))
  return nothing
end

doc"""
***
    norm(A::NfOrdIdl) -> fmpz

> Returns the norm of $A$, that is, the cardinality of $\mathcal O/A$, where
> $\mathcal O$ is the order of $A$.
"""
function norm(A::NfOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_norm(A)
  if copy == Val{true}
    return deepcopy(A.norm)
  else
    return A.norm
  end
end

################################################################################
#
#  Principal generators
#
################################################################################

doc"""
***
    has_basis_princ_gen(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows if it is generated by one element.
"""
function has_princ_gen(A::NfOrdIdl)
  return isdefined(A, :princ_gen)
end

doc"""
***
    has_basis_princ_gen_special(A::NfOrdIdl) -> Bool

> Returns whether $A$ knows if it is generated by a rational integer.
"""
function has_princ_gen_special(A::NfOrdIdl)
  return isdefined(A, :princ_gen_special)
end

princ_gen_special(A::NfOrdIdl) = A.princ_gen_special[A.princ_gen_special[1] + 1]

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
  v = transpose(matrix(FlintZZ, degree(parent(x)), 1, elem_in_basis(x)))
  t = FakeFmpqMat(v, fmpz(1))*basis_mat_inv(y)
  return t.den == 1
end

function in(x::nf_elem, y::NfOrdIdl)
  parent(x) != nf(order(y)) && error("Number field of element and ideal must be equal")
  return in(order(y)(x),y)
end

in(x::fmpz, y::NfOrdIdl) = in(order(y)(x),y)

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
    if new
      alpha = _invmod(A.gen_one, A.gen_two)
      _, d = ppio(denominator(alpha, O), A.gen_one)
    else  
      alpha = inv(elem_in_nf(A.gen_two))
      d = denominator(alpha, O)
      m = A.gen_one
      _, d = ppio(d, m)
    end  
    Ai = parent(A)()
    dn = denominator(d*alpha, O)
    Ai.gen_one = dn
    Ai.gen_two = O(d*alpha*dn, false)
    temp = dn^degree(A.parent.order)//norm(A)
    @hassert :NfOrd 1 denominator(temp) == 1
    Ai.norm = numerator(temp)
    Ai.gens_normal = A.gens_normal
    AAi = NfOrdFracIdl(Ai, dn)
    return AAi
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
#  Simplification
#
###########################################################################################
#CF: missing a function to compute the gcd(...) for the minimum
#    without 1st computing the complete inv
# .../ enter rresx and rres!

function (A::Nemo.AnticNumberField)(a::Nemo.fmpz_poly)
  return A(FlintQQ["x"][1](a))
end

function _minmod(a::fmpz, b::NfOrdElem)
#  @show "MinMod"
  if isone(a) 
    return a
  end
  Zk = parent(b)
  k = number_field(Zk)
  d = denominator(b.elem_in_nf)
  S = ResidueRing(FlintZZ, a*d*index(Zk))
  St = PolynomialRing(S)[1]
  B = St(d*b.elem_in_nf)
  F = St(k.pol)
  m, u, v = rresx(B, F)  # u*B + v*F = m mod modulus(S)
  U = lift(FlintZZ["x"][1], u)
  # m can be zero...
  m = lift(m)
  if iszero(m)
    m = a*d*index(Zk)
  end
  bi = k(U)//m*d # at this point, bi*d*b = m mod a*d*idx
  d = denominator(bi, Zk)
  return gcd(d, a)
  # min(<a, b>) = min(<ad, bd>)/d and bd is in the equation order, hence max as well
  # min(a, b) = gcd(a, denominator(b))
  # rres(b, f) = <b, f> meet Z = <r> and
  # ub + vf = r
  # so u/r is the inverse and r is the den in the field
  # we want gcd(r, a). so we use rres
  #at this point, min(<a, b*d>) SHOULD be 
end

function _invmod(a::fmpz, b::NfOrdElem)
#  @show "InvMod"
  Zk = parent(b)
  k = number_field(Zk)
  if isone(a)
    return one(k)
  end
  d = denominator(b.elem_in_nf)
  S = ResidueRing(FlintZZ, a^2*d*index(Zk))
  St = PolynomialRing(S)[1]
  B = St(d*b.elem_in_nf)
  F = St(k.pol)
  m, u, v = rresx(B, F)  # u*B + v*F = m mod modulus(S)
  c = inv(canonical_unit(m))
  U = lift(FlintZZ["x"][1], u*c)
  bi = k(U)//lift(m*c)*d # at this point, bi*d*b = m mod a*d*idx
  return bi
end


function _normmod(a::fmpz, b::NfOrdElem)
#  @show "NormMod"
  if isone(a)
    return a
  end
  Zk = parent(b)
  k = number_field(Zk)
  d = denominator(b.elem_in_nf)
  S = ResidueRing(FlintZZ, a*d^degree(parent(b)))
  St = PolynomialRing(S)[1]
  B = St(d*b.elem_in_nf)
  F = St(k.pol)
  m = resultant_sircana(B, F)  # u*B + v*F = m mod modulus(S)
  m = gcd(modulus(m), lift(m))
  return divexact(m, d^degree(parent(b)))
end


function simplify(A::NfOrdIdl)
  if has_2_elem(A) && has_weakly_normal(A)
    #if maximum(element_to_sequence(A.gen_two)) > A.gen_one^2
    #  A.gen_two = element_reduce_mod(A.gen_two, A.parent.order, A.gen_one^2)
    #end
    if A.gen_one == 1 # || test other things to avoid the 1 ideal
      A.gen_two = order(A)(1)
      A.minimum = fmpz(1)
      A.norm = fmpz(1)
      return A
    end
    if new
      A.minimum = _minmod(A.gen_one, A.gen_two)
      @hassert :Rres 1 A.minimum == gcd(A.gen_one, denominator(inv(A.gen_two.elem_in_nf), A.parent.order))
    else  
      A.minimum = gcd(A.gen_one, denominator(inv(A.gen_two.elem_in_nf), A.parent.order))
    end  
    A.gen_one = A.minimum
    if false && new
      #norm seems to be cheap, while inv is expensive
      #TODO: improve the odds further: currently, the 2nd gen has small coeffs in the
      #      order basis. For this it would better be small in the field basis....
      n = _normmod(A.gen_one^degree(A.parent.order), A.gen_two)
      @hassert :Rres 1 n == gcd(A.gen_one^degree(A.parent.order), FlintZZ(norm(A.gen_two)))
    else  
      n = gcd(A.gen_one^degree(A.parent.order), FlintZZ(norm(A.gen_two)))
    end  
    if isdefined(A, :norm)
      @assert n == A.norm
    end
    A.norm = n
    A.gen_two = mod(A.gen_two, A.gen_one^2)
    return A
  end
  return A
end

################################################################################
#
#  Trace matrix
#
################################################################################

function trace_matrix(A::NfOrdIdl)
  g = trace_matrix(order(A))
  b = basis_mat(A)
#  mul!(b, b, g)   #b*g*b' is what we want.
#                  #g should not be changed? b is a copy.
#  mul!(b, b, b')  #TODO: find a spare tmp-mat and use transpose
  return b*g*b'
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
  @assert isone(denominator(II))

  f, s = ispower_unram(numerator(II))

  g = gcd(f, e)
  if isone(g)
    return 1, I
  end

  II = inv(s)^div(f, g) * J^div(e, g)
  II = simplify(II)
  @assert isone(denominator(II))
  JJ = numerator(II)
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
  @assert isone(denominator(II))

  fl, s = ispower_unram(numerator(II), n)

  if !fl
    return fl, I
  end

  II = inv(s)* J
  II = simplify(II)
  @assert isone(denominator(II))
  JJ = numerator(II)

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
  else
    return mod(x, basis_mat(y, Val{false}), preinv)
  end
end

function mod(x::NfOrdElem, c::Union{fmpz_mat, Array{fmpz, 2}}, preinv::Array{fmpz_preinvn_struct, 1})
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape

  O = parent(x)
  a = elem_in_basis(x) # this is already a copy

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

function mod!(x::NfOrdElem, c::Union{fmpz_mat, Array{fmpz, 2}}, preinv::Array{fmpz_preinvn_struct, 1})
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape

  O = parent(x)
  a = elem_in_basis(x, Val{false}) # this is already a copy

  q = fmpz()
  r = fmpz()
  for i in degree(O):-1:1
    if iszero(a[i])
      continue
    end
    fdiv_qr_with_preinvn!(q, r, a[i], c[i, i], preinv[i])
    for j in 1:i
      submul!(a[j], q, c[i, j])
    end
  end
  # We need to adjust the underlying nf_elem
  t = nf(O)()
  B = O.basis_nf
  zero!(x.elem_in_nf)
  for i in 1:degree(O)
    mul!(t, B[i], a[i])
    add!(x.elem_in_nf, x.elem_in_nf, t)
  end

  @hassert :NfOrd 2 x.elem_in_nf == dot(a, O.basis_nf)

  return x
end

function mod(x::NfOrdElem, Q::NfOrdQuoRing)
  O = parent(x)
  a = elem_in_basis(x) # this is already a copy

  y = ideal(Q)

  if isdefined(y, :princ_gen_special) && y.princ_gen_special[1] != 0
    for i in 1:length(a)
      a[i] = mod(a[i], y.princ_gen_special[1 + y.princ_gen_special[1]])
    end
    return O(a)
  end

  return mod(x, Q.basis_mat_array, Q.preinvn)
end

function mod!(x::NfOrdElem, Q::NfOrdQuoRing)
  O = parent(x)
  a = elem_in_basis(x, Val{false}) # this is already a copy

  y = ideal(Q)

  if isdefined(y, :princ_gen_special) && y.princ_gen_special[1] != 0
    for i in 1:length(a)
      a[i] = mod(a[i], y.princ_gen_special[1 + y.princ_gen_special[1]])
    end
    t = nf(O)()
    B = O.basis_nf
    zero!(x.elem_in_nf)
    for i in 1:degree(O)
      mul!(t, B[i], a[i])
      add!(x.elem_in_nf, x.elem_in_nf, t)
    end
    return x
  end

  return mod!(x, Q.basis_mat_array, Q.preinvn)
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
function pradical(O::NfOrd, p::Union{Integer, fmpz})
  if typeof(p) == fmpz && nbits(p) < 64
    return pradical(O, Int(p))
  end

  j = clog(fmpz(degree(O)), p)
  local m::fmpz_mat

  @assert p^(j-1) < degree(O)
  @assert degree(O) <= p^j

  R = ResidueRing(FlintZZ, p)
  A = zero_matrix(R, degree(O), degree(O))
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
    m = vcat(m, p*identity_matrix(FlintZZ, degree(O)))
  else
    m = p*identity_matrix(FlintZZ, degree(O))
  end
  mm::fmpz_mat = _hnf(m, :lowerleft)
  r = sub(mm, rows(m) - degree(O) + 1:rows(m), 1:degree(O))
  return ideal(O, r)
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
  #@vprint :NfOrd 1 FakeFmpqMat(representation_mat(B[1]),FlintZZ(1))*bmatinv
  m = to_fmpz_mat(FakeFmpqMat(representation_mat(B[1]),FlintZZ(1))*bmatinv)
  for i in 2:degree(O)
    m = hcat(to_fmpz_mat(FakeFmpqMat(representation_mat(B[i]),FlintZZ(1))*basis_mat_inv(a)),m)
  end
  n = hnf(transpose(m))
  # n is upper right HNF
  n = transpose(sub(n, 1:degree(O), 1:degree(O)))
  b, d = pseudo_inv(n)
  #z = frac_ideal(O, FakeFmpqMat(b, d))
  return Order(nf(O), FakeFmpqMat(b, d)*basis_mat(O))
end

################################################################################
#
#  Two element generated ideals
#
################################################################################

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

################################################################################
#
#  Predicates
#
################################################################################

# check if gen_one,gen_two is a P(gen_one)-normal presentation
# see Pohst-Zassenhaus p. 404
function defines_2_normal(A::NfOrdIdl)
  m = A.gen_one
  gen = A.gen_two
  mg = denominator(inv(gen), order(A))
  # the minimum of ideal generated by g
  g = gcd(m,mg)
  return gcd(m, div(m,g)) == 1
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

    A.gen_one = denominator(bi, order(A))
    A.minimum = A.gen_one
    A.gen_two = x
    A.norm = abs(numerator(norm(b)))
    @hassert :NfOrd 1 gcd(A.gen_one^degree(order(A)),
                    FlintZZ(norm(A.gen_two))) == A.norm

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
    Q = numerator(basis_mat(O))
    d = denominator(basis_mat(O))
    mul!(m, m, Q)
    gen = elem_from_mat_row(nf(O), m, 1, d)
    # the following should be done inplace
    #gen = dot(reshape(Array(mm), degree(O)), basis(O))
    if norm(A) == gcd(Amind, numerator(norm(gen)))
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

      mg = denominator(inv(elem_in_nf(gen)), O) # the minimum of <gen>
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

###################################################################################
#
#  Coprimality between ideals
#
###################################################################################

doc"""
***
    iscoprime(I::NfOrdIdl, J::NfOrdIdl) -> Bool
> Test if ideals $I,J$ are coprime

"""

function iscoprime(I::NfOrdIdl, J::NfOrdIdl)
  
  @assert parent(I)==parent(J)
  
  if gcd(minimum(I), minimum(J))==1
    return true
  else 
    return isone(I+J)
  end

end 
