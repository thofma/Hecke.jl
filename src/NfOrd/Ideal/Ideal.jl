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
       uniformizer, iscoprime, conductor, colon, equation_order

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
function Base.deepcopy_internal(A::NfAbsOrdIdl, dict::IdDict)
  B = typeof(A)(order(A))
  for i in fieldnames(typeof(A))
    if isdefined(A, i)
      if i == :valuation || i == :order
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

parent(A::NfAbsOrdIdl) = NfAbsOrdIdlSet(order(A), false)

#################################################################################
#
#  Parent constructor
#
#################################################################################

function IdealSet(O::NfOrd)
   return NfAbsOrdIdlSet(O)
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
# - unless basis is in HNF it is also non-unique
function Base.hash(A::NfAbsOrdIdl, h::UInt)
  return Base.hash(basis_mat(A, Val{false}), h)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfAbsOrdIdlSet)
  print(io, "Set of ideals of $(order(a))\n")
end

function show(io::IO, a::NfAbsOrdIdl)
  if ismaximal_known(order(a)) && ismaximal(order(a))
    return show_maximal(io, a)
  else
    return show_gen(io, a)
  end
end

function show_gen(io::IO, a::NfAbsOrdIdl)
  print(io, "Ideal of (")
  print(io, order(a), ")\n")
  print(io, "with basis matrix\n")
  print(io, basis_mat(a))
end

function show_maximal(io::IO, id::NfAbsOrdIdl)
  compact = get(io, :compact, false)
  if compact
    if has_2_elem(id)
      print(io, "<", id.gen_one, ", ", id.gen_two, ">" )
      return
    elseif isdefined(id, :princ_gen)
        print(io, "\nprincipal generator ", id.princ_gen)
        return
    elseif isdefined(id, :basis_mat)
        print(io, "\nbasis_mat \n", id.basis_mat)
        return
    else    
      error("ideal without data")
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

function copy(i::NfAbsOrdIdl)
  return i
end

################################################################################
#
#  Parent object overloading and user friendly constructors
#
################################################################################

@doc Markdown.doc"""
***
    ideal(O::NfOrd, x::NfOrdElem) -> NfAbsOrdIdl

> Creates the principal ideal $(x)$ of $\mathcal O$.
"""
function ideal(O::NfAbsOrd, x::NfAbsOrdElem)
  return NfAbsOrdIdl(deepcopy(x))
end

@doc Markdown.doc"""
***
    ideal(O::NfOrd, x::fmpz_mat, check::Bool = false, x_in_hnf::Bool = false) -> NfAbsOrdIdl

> Creates the ideal of $\mathcal O$ with basis matrix $x$. If check is set, then it is
> checked whether $x$ defines an ideal (expensive). If x_in_hnf is set, then it is assumed
> that $x$ is already in lower left HNF.
"""
function ideal(O::NfAbsOrd, x::fmpz_mat, check::Bool = false, x_in_hnf::Bool = false)
  !x_in_hnf ? x = _hnf(x, :lowerleft) : nothing #sub-optimal, but == relies on the basis being thus

  I = NfAbsOrdIdl(O, x)
  if check
    J = ideal(O, 0)
    for i=1:degree(O)
      e = O([x[i,j] for j=1:degree(O)])
      J += ideal(O, e)
    end
    
    @assert J == I
  end

  return I
end


@doc Markdown.doc"""
***
    ideal(O::NfOrd, x::fmpz, y::NfOrdElem) -> NfAbsOrdIdl
    ideal(O::NfOrd, x::Integer, y::NfOrdElem) -> NfAbsOrdIdl

> Creates the ideal $(x,y)$ of $\mathcal O$.
"""
function ideal(O::NfAbsOrd, x::fmpz, y::NfOrdElem)
  return NfAbsOrdIdl(deepcopy(x), deepcopy(y))
end

function ideal(O::NfAbsOrd, x::Integer, y::NfOrdElem)
  return NfAbsOrdIdl(fmpz(x), deepcopy(y))
end

function ideal(O::NfAbsOrd)
  return NfAbsOrdIdl(O)
end

function (S::NfAbsOrdIdlSet)()
   return NfAbsOrdIdl(order(S))
end

@doc Markdown.doc"""
***
    ideal(O::NfOrd, a::fmpz) -> NfAbsOrdIdl
    ideal(O::NfOrd, a::Integer) -> NfAbsOrdIdl

> Returns the ideal of $\mathcal O$ which is generated by $a$.
"""
ideal(O::NfAbsOrd, a::fmpz)  = NfAbsOrdIdl(O, deepcopy(a))
ideal(O::NfAbsOrd, a::Int) = NfAbsOrdIdl(O, a)
ideal(O::NfAbsOrd, a::Integer) = NfAbsOrdIdl(O, fmpz(a))

function ideal_from_z_gens(O::NfOrd, b::Vector{NfOrdElem}, check::Bool = false)
  d = degree(O)
  @assert length(b) >= d

  M = zero_matrix(FlintZZ, length(b), d)
  for i = 1:length(b)
    for j = 1:d
      M[i, j] = elem_in_basis(b[i])[j]
    end
  end
  M = _hnf(M, :lowerleft)
  if d < length(b)
    M = sub(M, (length(b) - d + 1):length(b), 1:d)
  end
  return ideal(O, M, check, true)
end

################################################################################
#
#  Basic field access
#
################################################################################

@doc Markdown.doc"""
***
    order(x::NfAbsOrdIdl) -> NfOrd

> Returns the order, of which $x$ is an ideal.
"""
order(a::NfAbsOrdIdlSet) = a.order

@doc Markdown.doc"""
***
    nf(x::NfAbsOrdIdl) -> AnticNumberField

> Returns the number field, of which $x$ is an integral ideal.
"""
nf(x::NfAbsOrdIdl) = nf(order(x))


@doc Markdown.doc"""
***
    order(I::NfAbsOrdIdl) -> NfOrd

> Returns the order of $I$.
"""
@inline order(a::NfAbsOrdIdl) = a.order

################################################################################
#
#  Principal ideal creation
#
################################################################################

@doc Markdown.doc"""
    *(O::NfOrd, x::NfOrdElem) -> NfAbsOrdIdl
    *(x::NfOrdElem, O::NfOrd) -> NfAbsOrdIdl

> Returns the principal ideal $(x)$ of $\mathcal O$.
"""
function *(O::NfOrd, x::NfOrdElem)
  parent(x) !== O && error("Order of element does not coincide with order")
  return ideal(O, x)
end

*(x::NfOrdElem, O::NfOrd) = O*x
*(x::Int, O::NfOrd) = ideal(O, x)
*(x::BigInt, O::NfOrd) = ideal(O, fmpz(x))
*(x::fmpz, O::NfOrd) = ideal(O, x)

###########################################################################################
#
#   Basis
#
###########################################################################################

@doc Markdown.doc"""
***
    has_basis(A::NfAbsOrdIdl) -> Bool

> Returns whether A has a basis already computed.
"""
@inline has_basis(A::NfAbsOrdIdl) = isdefined(A, :basis)

function assure_has_basis(A::NfAbsOrdIdl)
  if isdefined(A, :basis)
    return nothing
  else
    assure_has_basis_mat(A)
    O = order(A)
    M = A.basis_mat
    Ob = basis(O, Val{false})
    B = Vector{elem_type(O)}(undef, degree(O))
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

@doc Markdown.doc"""
***
    basis(A::NfAbsOrdIdl) -> Array{NfOrdElem, 1}

> Returns the basis of A.
"""
@inline function basis(A::NfAbsOrdIdl, copy::Type{Val{T}} = Val{true}) where {T}
  assure_has_basis(A)
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

@doc Markdown.doc"""
***
    has_basis_mat(A::NfAbsOrdIdl) -> Bool

> Returns whether $A$ knows its basis matrix.
"""
@inline has_basis_mat(A::NfAbsOrdIdl) = isdefined(A, :basis_mat)

@doc Markdown.doc"""
***
    basis_mat(A::NfAbsOrdIdl) -> fmpz_mat

> Returns the basis matrix of $A$.
"""
function basis_mat(A::NfAbsOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat(A)
  if copy == Val{true}
    return deepcopy(A.basis_mat)
  else
    return A.basis_mat
  end
end

function assure_has_basis_mat(A::NfAbsOrdIdl)
  if isdefined(A, :basis_mat)
    return nothing
  end

  if iszero(A)
    A.basis_mat = zero_matrix(FlintZZ, degree(order(A)), degree(order(A)))
    return nothing
  end

  if !issimple(nf(order(A))) && isdefined(A, :is_prime) && A.is_prime == 1 && A.norm == A.minimum &&
     !isindex_divisor(order(A), A.minimum)
    # A is a prime ideal of degree 1
    A.basis_mat = basis_mat_prime_deg_1(A)
    return nothing
  end

  if has_princ_gen(A)
    m = representation_matrix(A.princ_gen)
    A.basis_mat = _hnf_modular_eldiv(m, minimum(A), :lowerleft)
    return nothing
  end

  @hassert :NfOrd 1 has_2_elem(A)
  K = nf(order(A))
  n = degree(K)
  c = _hnf_modular_eldiv(representation_matrix(A.gen_two), abs(A.gen_one), :lowerleft)
  A.basis_mat = c
  return nothing
end

function basis_mat_prime_deg_1(A::NfAbsOrdIdl)
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

@doc Markdown.doc"""
***
    has_basis_mat_inv(A::NfAbsOrdIdl) -> Bool

> Returns whether $A$ knows its inverse basis matrix.
"""
@inline has_basis_mat_inv(A::NfAbsOrdIdl) = isdefined(A, :basis_mat_inv)

@doc Markdown.doc"""
***
    basis_mat_inv(A::NfAbsOrdIdl) -> fmpz_mat

> Returns the inverse basis matrix of $A$.
"""
function basis_mat_inv(A::NfAbsOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_basis_mat_inv(A)
  if copy == Val{true}
    return deepcopy(A.basis_mat_inv)
  else
    return A.basis_mat_inv
  end
end

@doc Markdown.doc"""
***
    basis_mat_inv(A::NfAbsOrdIdl) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $A$.
"""
function assure_has_basis_mat_inv(A::NfAbsOrdIdl)
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

@doc Markdown.doc"""
***
    has_minimum(A::NfAbsOrdIdl) -> Bool

> Returns whether $A$ knows its mininum.
"""
function has_minimum(A::NfAbsOrdIdl)
  return isdefined(A, :minimum)
end

@doc Markdown.doc"""
***
    minimum(A::NfAbsOrdIdl) -> fmpz

> Returns the smallest nonnegative element in $A \cap \mathbf Z$.
"""
function minimum(A::NfAbsOrdIdl, copy::Type{Val{T}} = Val{true}) where T
  assure_has_minimum(A)
  if copy == Val{true}
    return deepcopy(A.minimum)
  else
    return A.minimum
  end
end

function assure_has_minimum(A::NfAbsOrdIdl)
  if has_minimum(A)
    return nothing
  end

  if has_princ_gen(A)
    b = A.princ_gen.elem_in_nf
    if iszero(b)
      A.minimum = fmpz(0)
      A.iszero = 1
    else
      if issimple(nf(order(A))) && order(A).ismaximal == 1
        A.minimum = _minmod(A.gen_one, A.gen_two)
        @hassert :Rres 1 A.minimum == denominator(inv(b), order(A))
      else
        bi = inv(b)
        A.minimum =  denominator(bi, order(A))
      end
    end
    return nothing
  end

  if has_weakly_normal(A)
    K = nf(order(A))
    if iszero(A.gen_two)
      # A = (A.gen_one, 0) = (A.gen_one)
      d = abs(A.gen_one)
    else
      if issimple(nf(order(A))) && order(A).ismaximal == 1
        d = _minmod(A.gen_one, A.gen_two)
        @hassert :Rres 1 d == gcd(A.gen_one, denominator(inv(A.gen_two.elem_in_nf), order(A)))
      else
        d = denominator(inv(K(A.gen_two)), order(A))
        d = gcd(d, FlintZZ(A.gen_one))
      end
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

@doc Markdown.doc"""
***
    has_norm(A::NfAbsOrdIdl) -> Bool

> Returns whether $A$ knows its norm.
"""
function has_norm(A::NfAbsOrdIdl)
  return isdefined(A, :norm)
end

function assure_has_norm(A::NfAbsOrdIdl)
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

@doc Markdown.doc"""
***
    norm(A::NfAbsOrdIdl) -> fmpz

> Returns the norm of $A$, that is, the cardinality of $\mathcal O/A$, where
> $\mathcal O$ is the order of $A$.
"""
function norm(A::NfAbsOrdIdl, copy::Type{Val{T}} = Val{true}) where T
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

@doc Markdown.doc"""
***
    has_basis_princ_gen(A::NfAbsOrdIdl) -> Bool

> Returns whether $A$ knows if it is generated by one element.
"""
function has_princ_gen(A::NfAbsOrdIdl)
  return isdefined(A, :princ_gen)
end

@doc Markdown.doc"""
***
    has_basis_princ_gen_special(A::NfAbsOrdIdl) -> Bool

> Returns whether $A$ knows if it is generated by a rational integer.
"""
function has_princ_gen_special(A::NfAbsOrdIdl)
  return isdefined(A, :princ_gen_special)
end

princ_gen_special(A::NfAbsOrdIdl) = A.princ_gen_special[A.princ_gen_special[1] + 1]

################################################################################
#
#  Equality
#
################################################################################

@doc Markdown.doc"""
***
    ==(x::NfAbsOrdIdl, y::NfAbsOrdIdl)

> Returns whether $x$ and $y$ are equal.
"""
function ==(x::NfAbsOrdIdl, y::NfAbsOrdIdl)
  return basis_mat(x, Val{false}) == basis_mat(y, Val{false})
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

@doc Markdown.doc"""
***
    in(x::NfOrdElem, y::NfAbsOrdIdl)
    in(x::nf_elem, y::NfAbsOrdIdl)
    in(x::fmpz, y::NfAbsOrdIdl)

> Returns whether $x$ is contained in $y$.
"""
function in(x::NfOrdElem, y::NfAbsOrdIdl)
  parent(x) !== order(y) && error("Order of element and ideal must be equal")
  v = matrix(FlintZZ, 1, degree(parent(x)), elem_in_basis(x))
  t = FakeFmpqMat(v, fmpz(1))*basis_mat_inv(y, Val{false})
  return isone(t.den) 
end

function in(x::nf_elem, y::NfAbsOrdIdl)
  parent(x) !== nf(order(y)) && error("Number field of element and ideal must be equal")
  return in(order(y)(x),y)
end

in(x::fmpz, y::NfAbsOrdIdl) = in(order(y)(x),y)

in(x::Integer, y::NfAbsOrdIdl) = in(order(y)(x),y)

################################################################################
#
#  Inverse
#
################################################################################

@doc Markdown.doc"""
***
    inv(A::NfAbsOrdIdl) -> NfOrdFracIdl

> Computes the inverse of A, that is, the fractional ideal $B$ such that
> $AB = \mathcal O_K$.
"""
function inv(A::NfAbsOrdIdl)
  @assert !iszero(A)
  if ismaximal_known(order(A)) && ismaximal(order(A))
    return inv_maximal(A)
  else
    return inv_generic(A)
  end
end

# If I is not coprime to the conductor of O in the maximal order, then this might
# not be an inverse.
function inv_generic(A::NfAbsOrdIdl)
  O = order(A)
  return colon(O(1)*O, A)
end

function inv_maximal(A::NfAbsOrdIdl)
  O = order(A)
  if isdefined(A, :princ_gen) && !has_2_elem_normal(A)
    return ideal(O, inv(A.princ_gen.elem_in_nf))
  elseif has_2_elem(A) && has_weakly_normal(A)
    assure_2_normal(A)
    O = order(A)
    if iszero(A.gen_two)
      return ideal(O, 1)//A.gen_one
    end
    m = A.gen_one
    if isone(m)
      return A//1
    end
    if true
      alpha = _invmod(m, A.gen_two)
    else  
      be = elem_in_nf(A.gen_two)
      d = denominator(be)
      f, e = ppio(d, m)
      be *= e
      be = mod(be*f, m^2*f)//f
      alpha = inv(elem_in_nf(be))
    end  
    _, d = ppio(denominator(alpha, O), m)
    Ai = NfAbsOrdIdl(order(A))
    #Ai = parent(A)()
    dn = denominator(d*alpha, O)
    @assert ppio(dn, m)[1] == dn
    Ai.gen_one = dn
    Ai.gen_two = O(d*alpha*dn, false)
    temp = dn^degree(order(A))//norm(A)
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

@doc Markdown.doc"""
***
    isinvertible(A::NfAbsOrdIdl) -> Bool, NfOrdFracIdl

> Returns true and an inverse of $A$ or false and an ideal $B$ such that
> $A*B \subsetneq order(A)$, if $A$ is not invertible.
"""
function isinvertible(A::NfAbsOrdIdl)
  if iszero(A)
    return false, A
  end

  if ismaximal_known(order(A)) && ismaximal(order(A))
    return true, inv(A)
  end

  i1 = gen_index(maximal_order(nf(order(A))))
  i2 = gen_index(order(A))
  i = i1*inv(i2)
  @assert isone(denominator(i))
  if isone(gcd(numerator(i), minimum(A, Val{false})))
    return true, inv(A)
  end
  B = inv(A)
  C = simplify(A*B)
  return isone(C), B
end

################################################################################
#
#  Simplification
#
################################################################################
#CF: missing a function to compute the gcd(...) for the minimum
#    without 1st computing the complete inv
# .../ enter rresx and rres!

function (A::Nemo.AnticNumberField)(a::Nemo.fmpz_poly)
  return A(FlintQQ["x"][1](a))
end

function _minmod(a::fmpz, b::NfOrdElem)
  if isone(a) 
    return a
  end
  Zk = parent(b)
  k = number_field(Zk)
  d = denominator(b.elem_in_nf)
  d, _ = ppio(d, a)
  e, _ = ppio(basis_mat(Zk, Val{false}).den, a) 
  S = ResidueRing(FlintZZ, a*d*e, cached = false)
  St = PolynomialRing(S, cached=false)[1]
  B = St(d*b.elem_in_nf)
  F = St(k.pol)
  m, u, v = rresx(B, F)  # u*B + v*F = m mod modulus(S)
  U = lift(FlintZZ["x"][1], u)
  # m can be zero...
  m1 = lift(m)
  if iszero(m1)
    m1 = a*d*e
  end
  bi = k(U)//m1*d # at this point, bi*d*b = m mod a*d*idx
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
  Zk = parent(b)
  k = nf(Zk)
  if isone(a)
    return one(k)
  end
  d = denominator(b.elem_in_nf)
  d, _ = ppio(d, a)
  e, _ = ppio(basis_mat(Zk, Val{false}).den, a) 
  S = ResidueRing(FlintZZ, a^2*d*e, cached=false)
  St = PolynomialRing(S, cached=false)[1]
  B = St(d*b.elem_in_nf)
  F = St(k.pol)
  m, u, v = rresx(B, F)  # u*B + v*F = m mod modulus(S)
  if iszero(m)
    m = a^2*d*e
    c = S(1)
  else
    c = inv(canonical_unit(m))
    m = lift(m*c)
  end
  U = lift(PolynomialRing(FlintZZ, "x", cached = false)[1], u*c)
  bi = k(U)//m*d # at this point, bi*d*b = m mod a*d*idx
  return bi
end


function _normmod(a::fmpz, b::NfOrdElem)
  if isone(a)
    return a
  end
  Zk = parent(b)
  k = number_field(Zk)
  d = denominator(b.elem_in_nf)
  S = ResidueRing(FlintZZ, a*d^degree(parent(b)), cached=false)
  St = PolynomialRing(S, cached=false)[1]
  B = St(d*b.elem_in_nf)
  F = St(k.pol)
  m = resultant_sircana(B, F)  # u*B + v*F = m mod modulus(S)
  m = gcd(modulus(m), lift(m))
  return divexact(m, d^degree(parent(b)))
end


function simplify(A::NfAbsOrdIdl)
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
    if true
      A.minimum = _minmod(A.gen_one, A.gen_two)
      @hassert :Rres 1 A.minimum == gcd(A.gen_one, denominator(inv(A.gen_two.elem_in_nf), order(A)))
    else  
      A.minimum = gcd(A.gen_one, denominator(inv(A.gen_two.elem_in_nf), order(A)))
    end  
    A.gen_one = A.minimum
    if false 
      #norm seems to be cheap, while inv is expensive
      #TODO: improve the odds further: currently, the 2nd gen has small coeffs in the
      #      order basis. For this it would better be small in the field basis....
      n = _normmod(A.gen_one^degree(order(A)), A.gen_two)
      @hassert :Rres 1 n == gcd(A.gen_one^degree(order(A)), FlintZZ(norm(A.gen_two)))
    else  
      n = gcd(A.gen_one^degree(order(A)), FlintZZ(norm(A.gen_two)))
    end  
    if isdefined(A, :norm)
      @assert n == A.norm
    end
    A.norm = n
    if true
      be = A.gen_two.elem_in_nf
      d = denominator(be)
      f, e = ppio(d, A.gen_one)
      be *= e
      be = mod(be*f, f*A.gen_one^2)//f
      A.gen_two = order(A)(be)
    else
      A.gen_two = mod(A.gen_two, A.gen_one^2)
    end
    A.gens_normal = A.gen_one
    return A
  end
  return A
end

################################################################################
#
#  Trace matrix
#
################################################################################

function trace_matrix(A::NfAbsOrdIdl)
  g = trace_matrix(order(A))
  b = basis_mat(A, Val{false})
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

@doc Markdown.doc"""
    ispower(I::NfAbsOrdIdl) -> Int, NfAbsOrdIdl
    ispower(a::NfOrdFracIdl) -> Int, NfOrdFracIdl
> Writes $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
"""
function ispower(I::NfAbsOrdIdl)
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

function ispower_unram(I::NfAbsOrdIdl)
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

@doc Markdown.doc"""
    ispower(A::NfAbsOrdIdl, n::Int) -> Bool, NfAbsOrdIdl
    ispower(A::NfOrdFracIdl, n::Int) -> Bool, NfOrdFracIdl
> Computes, if possible, an ideal $B$ s.th. $B^n==A$ holds. In this
> case, {{{true}}} and $B$ are returned.
"""
function ispower(A::NfAbsOrdIdl, n::Int)
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

function ispower_unram(I::NfAbsOrdIdl, n::Int)
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

function one(A::NfAbsOrdIdl)
  return ideal(order(A), 1)
end

@doc Markdown.doc"""
***
    isone(A::NfAbsOrdIdl) -> Bool
    isunit(A::NfAbsOrdIdl) -> Bool

> Tests if $A$ is the trivial ideal generated by $1$.
"""
function isone(I::NfAbsOrdIdl)
  if isdefined(I, :norm)
    return isone(norm(I))
  end
  return isone(minimum(I))
end

isunit(I::NfAbsOrdIdl) = isone(I)

iszero(I::NfAbsOrdIdl) = (I.iszero == 1)

################################################################################
#
#  Reduction of element modulo ideal
#
################################################################################

@doc Markdown.doc"""
***
    mod(x::NfOrdElem, I::NfAbsOrdIdl)

> Returns the unique element $y$ of the ambient order of $x$ with
> $x \equiv y \bmod I$ and the following property: If
> $a_1,\dotsc,a_d \in \Z_{\geq 1}$ are the diagonal entries of the unique HNF
> basis matrix of $I$ and $(b_1,\dotsc,b_d)$ is the coefficient vector of $y$,
> then $0 \leq b_i < a_i$ for $1 \leq i \leq d$.
"""
function mod(x::S, y::T) where { S <: Union{NfOrdElem, AlgAssAbsOrdElem}, T <: Union{NfAbsOrdIdl, AlgAssAbsOrdIdl} }
  parent(x) !== order(y) && error("Orders of element and ideal must be equal")
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape

  O = order(y)
  a = elem_in_basis(x)
  #a = deepcopy(b)
  
  #dump(y, maxdepth = 1)

  if isdefined(y, :princ_gen_special) && y.princ_gen_special[1] != 0
    for i in 1:length(a)
      a[i] = mod(a[i], y.princ_gen_special[1 + y.princ_gen_special[1]])
    end
    return O(a)
  end

  c = basis_mat(y, Val{false})
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

function mod(x::NfOrdElem, y::NfAbsOrdIdl, preinv::Array{fmpz_preinvn_struct, 1})
  parent(x) !== order(y) && error("Orders of element and ideal must be equal")
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
@doc Markdown.doc"""
    pradical(O::NfOrd, p::{fmpz|Integer}) -> NfAbsOrdIdl

> Given a prime number $p$, this function returns the $p$-radical
> $\sqrt{p\mathcal O}$ of $\mathcal O$, which is
> just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
> \in p\mathcal O \}$. It is not checked that $p$ is prime.
"""
function pradical(O::NfAbsOrd, p::Union{Integer, fmpz})
  if typeof(p) == fmpz && nbits(p) < 64
    return pradical(O, Int(p))
  end
  d = degree(O)
  
    #Trace method if the prime is large enough
  if p > degree(O)
    M = trace_matrix(O)
    W = MatrixSpace(ResidueRing(FlintZZ, p, cached=false), d, d, false)
    M1 = W(M)
    k, B = nullspace(M1)
    if k == 0
      return ideal(O, p)
    end
    M2 = zero_matrix(FlintZZ, d, d)
    for i=1:cols(B)
      for j=1:d
        M2[i,j] = FlintZZ(B[j, i].data)
      end
    end
    gens=[O(p)]
    for i=1:cols(B)
      if !iszero_row(M2,i)
        push!(gens, elem_from_mat_row(O, M2, i))
      end
    end
    M2 = _hnf_modular_eldiv(M2, fmpz(p), :lowerleft)
    I = NfAbsOrdIdl(O, M2)
    I.gens = gens
    return I
  end
  
  j = clog(fmpz(d), p)
  @assert p^(j-1) < d
  @assert d <= p^j

  R = GF(p, cached = false)
  A = zero_matrix(R, degree(O), degree(O))
  B = basis(O, Val{false})
  for i in 1:degree(O)
    t = powermod(B[i], p^j, p)
    ar = elem_in_basis(t)
    for k in 1:d
      A[i,k] = ar[k]
    end
  end
  X = kernel(A)
  gens = NfAbsOrdElem[O(p)]
  if length(X)==0
    I = ideal(O, p)
    I.gens = gens
    return I
  end
  #First, find the generators
  for i = 1:length(X)
    coords = Array{fmpz,1}(undef, d)
    for j=1:d
      coords[j] = lift(X[i][j])
    end
    push!(gens, O(coords))
  end
  #Then, construct the basis matrix of the ideal
  m = zero_matrix(FlintZZ, d, d)
  for i = 1:length(X)
    for j = 1:d
      m[i, j] = lift(X[i][j])
    end
  end
  mm = _hnf_modular_eldiv(m, fmpz(p), :lowerleft)
  I = NfAbsOrdIdl(O, mm)
  I.gens = gens
  return I
end

################################################################################
#
#  Ring of multipliers, colon, conductor: it's the same(?) method
#
################################################################################

@doc Markdown.doc"""
***
    ring_of_multipliers(I::NfAbsOrdIdl) -> NfOrd

> Computes the order $(I : I)$, which is the set of all $x \in K$
> with $xI \subseteq I$.
"""
function ring_of_multipliers(a::NfAbsOrdIdl)
  O = order(a) 
  n = degree(O)
  if isdefined(a, :gens) && length(a.gens) < n
    B = a.gens
  else
    B = basis(a, Val{false})
  end
  bmatinv = basis_mat_inv(a, Val{false})
  m = zero_matrix(FlintZZ, n*length(B), n)
  for i=1:length(B)
    M = representation_matrix(B[i])
    mul!(M, M, bmatinv.num)
    if bmatinv.den == 1
      for j=1:n
        for k=1:n
          m[j+(i-1)*n,k] = M[k,j]
        end
      end
    else
      for j=1:n
        for k=1:n
          m[j+(i-1)*n,k] = divexact(M[k,j], bmatinv.den)
        end
      end
    end
  end
  mhnf = hnf_modular_eldiv!(m, minimum(a))
  s = prod(mhnf[i,i] for i = 1:n)
  if isone(s)
    return O
  end
  # mhnf is upper right HNF
  # mhnftrans = transpose(view(mhnf, 1:n, 1:n))
  for i = 1:n
    for j = i+1:n
      mhnf[j, i] = mhnf[i, j]
      mhnf[i, j] = 0
    end
  end
  mhnftrans = view(mhnf, 1:n, 1:n)
  b = FakeFmpqMat(pseudo_inv(mhnftrans))
  mul!(b, b, basis_mat(O, Val{false}))
  @hassert :NfOrd 1 defines_order(nf(O), b)[1]
  O1 = Order(nf(O), b, false)
  if isdefined(O, :disc)
    O1.disc = divexact(O.disc, s^2)
  end
  if isdefined(O, :index)
    O1.index = s*O.index
  end
  if isdefined(O, :basis_mat_inv)
    O1.basis_mat_inv = O.basis_mat_inv * mhnftrans
  end
  return O1
end

@doc Markdown.doc"""
    colon(a::NfAbsOrdIdl, b::NfAbsOrdIdl) -> NfOrdFracIdl
> The ideal $(a:b) = \{x \in K | xb \subseteq a\} = \hom(b, a)$
> where $K$ is the number field.
"""
function colon(a::NfAbsOrdIdl, b::NfAbsOrdIdl, contains::Bool = false)
  
  O = order(a)
  n = degree(O)
  if isdefined(b, :gens)
    B = b.gens
  else
    B = basis(b)
  end

  bmatinv = basis_mat_inv(a, Val{false})

  if contains
    m = zero_matrix(FlintZZ, n*length(B), n)
    for i=1:length(B)
      M=representation_matrix(B[i])
      mul!(M, M, bmatinv.num)
      if bmatinv.den==1
        for j=1:n
          for k=1:n
            m[j+(i-1)*n,k]=M[k,j]
          end
        end
      else
        for j=1:n
          for k=1:n
            m[j+(i-1)*n,k]=divexact(M[k,j], bmatinv.den)
          end
        end
      end
    end
    m = hnf_modular_eldiv!(m, minimum(b))
    m = transpose(sub(m, 1:degree(O), 1:degree(O)))
    b, l = pseudo_inv(m)
    return NfAbsOrdIdl(O, b)//l
  else 
    n = FakeFmpqMat(representation_matrix(B[1]),FlintZZ(1))*bmatinv
    m = numerator(n)
    d = denominator(n)
    for i in 2:length(B)
      n = FakeFmpqMat(representation_matrix(B[i]),FlintZZ(1))*bmatinv
      l = lcm(denominator(n), d)
      if l==d
        m = hcat(m, n.num)
      else
        m = hcat(m*div(l, d), n.num*div(l, denominator(n)))
        d = l
      end
    end
    m = hnf(transpose(m))
    # n is upper right HNF
    m = transpose(sub(m, 1:degree(O), 1:degree(O)))
    b, l = pseudo_inv(m)
    return ideal(O, b)//l
  end
end

################################################################################
#
#  Conversion to different order
#
################################################################################

@doc Markdown.doc"""
    ideal(O::NfOrd, I::NfAbsOrdIdl) -> NfOrdFracIdl
> The fractional ideal of $O$ generated by a Z-basis of $I$.
"""
function ideal(O::NfOrd, I::NfAbsOrdIdl)
  k = nf(O)
  bI = basis(I)
  J = ideal(O, k(bI[1]))
  for j=2:degree(O)
    J += ideal(O, k(bI[j]))
  end
  return J
end

################################################################################
#
#  Two element generated ideals
#
################################################################################

@doc Markdown.doc"""
***
    has_2_elem(A::NfAbsOrdIdl) -> Bool

> Returns whether $A$ is generated by two elements.
"""
function has_2_elem(A::NfAbsOrdIdl)
  return isdefined(A, :gen_two)
end

@doc Markdown.doc"""
***
    has_weakly_normal(A::NfAbsOrdIdl) -> Bool

> Returns whether $A$ has weakly normal two element generators.
"""
function has_weakly_normal(A::NfAbsOrdIdl)
  return (isdefined(A, :gens_weakly_normal) &&
        A.gens_weakly_normal == true) || has_2_elem_normal(A)
end

@doc Markdown.doc"""
***
    has_2_elem_normal(A::NfAbsOrdIdl) -> Bool

> Returns whether $A$ has normal two element generators.
"""
function has_2_elem_normal(A::NfAbsOrdIdl)
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
function defines_2_normal(A::NfAbsOrdIdl)
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

function _assure_weakly_normal_presentation(A::NfAbsOrdIdl)
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
    if !isdefined(A, :norm)
      A.norm = abs(numerator(norm(b)))
    end
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

  if minimum(A) == 1
    A.gen_one = minimum(A)
    A.gen_two = one(O)
    A.gens_weakly_normal = 1
    A.gens_normal = fmpz(2)
    return nothing
  end


  M = MatrixSpace(FlintZZ, 1, degree(O), false)

  Amin2 = minimum(A)^2
  Amind = minimum(A)^degree(O)

  B = Array{fmpz}(undef, degree(O))

  gen = O()

  r = -Amin2:Amin2

  m = M()

  cnt = 0
  while true
    cnt += 1

    if cnt > 100 && is_2_normal_difficult(A)
      assure_2_normal_difficult(A)
      return
    end

    if cnt > 1000
      println("Having a hard time find weak generators for $A")
    end

    rand!(B, r)

    # Put the entries of B into the (1 x d)-Matrix m
    for i in 1:degree(O)
      s = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ref{fmpz_mat}, Int, Int), m, 0, i - 1)
      ccall((:fmpz_set, :libflint), Nothing, (Ptr{fmpz}, Ref{fmpz}), s, B[i])
    end

    if iszero(m)
      continue
    end

    mul!(m, m, basis_mat(A, Val{false}))
    d = denominator(basis_mat(O, Val{false}))
    mul!(m, m, basis_mat(O, Val{false}).num)
    gen = elem_from_mat_row(nf(O), m, 1, d)
    d = denominator(gen)
    f, e = ppio(d, minimum(A))
    gen *= e
    gen = mod(gen*f, f*minimum(A)^2)//f
    if iszero(gen)
      continue
    end

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
#
# Here some random guesses for the difficult 2-element generators
# degree  | d
#   < 7   | 1
#  8 - 12 | 2 * 3
# 13 - 20 | 2 * 3 * 5
#  >= 21  | 2 * 3 * 5 * 7

function is_2_normal_difficult(A::NfAbsOrdIdl)
  d = 2
  m = minimum(A)
  ZK = order(A)
  n = degree(ZK)

  if n < 7
    return false
  end

  if n < 12 && isone(gcd(m, 2 * 3))
    return false
  end

  if n < 20 && isone(gcd(m, 2 * 3 * 5))
    return false
  end

  if isone(gcd(m, 2 * 3 * 5 * 7))
    return false
  end

  return true
end

function assure_2_normal_difficult(A::NfAbsOrdIdl)
  m = minimum(A)
  ZK = order(A)
  n = degree(ZK)

  if !is_2_normal_difficult(A)
    assure_2_normal(A)
    return
  end

  if n < 12
    d = 2 * 3
  elseif n < 20
    d = 2 * 3 * 5
  else
    d = 2 * 3 * 5 * 7
  end

  m1, m2 = ppio(m, fmpz(d))
  A1 = gcd(A, m1)
  A2 = gcd(A, m2)
  assure_2_normal(A2)

  lp = append!(prime_decomposition(ZK, 2), prime_decomposition(ZK, 3))
  if n >= 13
    lp = append!(lp, prime_decomposition(ZK, 5))
  end
  if n >= 21
    lp = append!(lp, prime_decomposition(ZK, 7))
  end

  v = [valuation(A1, p[1]) for p = lp]

  B1 = prod(lp[i][1]^v[i] for i=1:length(v) if v[i] > 0)
  C = B1 * A2
  A.gen_one = C.gen_one
  A.gen_two = C.gen_two
  A.gens_normal = C.gens_normal
  A.gens_weakly_normal = C.gens_weakly_normal
  A.gens_short = C.gens_short

  return
end

function assure_2_normal(A::NfAbsOrdIdl)
  if has_2_elem(A) && has_2_elem_normal(A)
    return
  end
  O = order(A)
  K = nf(O)
  n = degree(K)

  if norm(A) == 1
    A.gen_one = fmpz(1)
    A.gen_two = one(O)
    A.gens_normal = fmpz(1)
    return
  end

  if has_2_elem(A)
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
      if cnt > 100 && is_2_normal_difficult(A)
        assure_2_normal_difficult(A)
        return  
      end
      if cnt > 1000
        error("Having a hard time making generators normal for $A")
      end
      rand!(s, O, r)
      mul!(s, s, A.gen_two)
      add!(gen, rand(r)*A.gen_one, gen)
      add!(gen, s, gen)
      gen = mod(gen, m^2)

      if iszero(gen)
        continue
      end

      mg = _minmod(m^2, gen)
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

  m = minimum(A)
  bas = basis(A, nf(order(A)))
  # Magic constants
  if m > 1000
    r = -500:500
  else
    r = -div(Int(m)+1,2):div(Int(m)+1,2)
  end
  cnt = 0
  while true
    cnt += 1
    if cnt > 100 && is_2_normal_difficult(A)
      assure_2_normal_difficult(A)
      return  
    end
    if cnt > 1000
      error("Having a hard time making generators normal for $A")
    end
    gen = O(rand(bas, r))
    gen = mod(gen, m^2)

    if iszero(gen)
      continue
    end

    mg = _minmod(m^2, gen)
#    @assert mg == gcd(m, denominator(inv(gen.elem_in_nf), O))
    if gcd(m, div(mg, gcd(mg, m))) == 1
      if gcd(m^n, norm(gen)) != norm(A)
        @vprint :NfOrd 1 "\n\noffending ideal $A \ngen is $gen\nWrong ideal\n"
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

function random_init(I::AbstractArray{T, 1}; reduce::Bool = true, ub::fmpz=fmpz(0), lb::fmpz=fmpz(1)) where {T}

  R = RandIdlCtx()
  R.base = collect(I)
  O = order(R.base[1])
  R.ibase = map(inv, R.base)
  R.exp = zeros(Int, length(R.base))
  R.lb = lb
  R.ub = ub
  R.last = Set{Array{Int, 1}}()
  R.rand = ideal(O, 1)
  while norm(R.rand) <= lb
    i = rand(1:length(R.base))
    R.rand = simplify(R.rand * R.base[i])
    R.exp[i] += 1
  end
  push!(R.last, copy(R.exp))
  return R
end

function random_extend(R::RandIdlCtx, I::T) where {T <:AbstractArray{NfOrdIdl, 1}}
  for i = I
    if i in R.base
      continue
    end
    push!(R.base, i)
    push!(R.ibase, inv(i))
  end
  z = zeros(Int, length(R.base) - length(R.exp))
  append!(R.exp, z)
  @assert length(R.exp) == length(R.base)
  for i = R.last
    append!(i, z)
  end
  nothing
end

function random_extend(R::RandIdlCtx, f::Float64)
  R.lb = ceil(fmpz, R.lb*f)
  R.ub = ceil(fmpz, R.lb*f)
  while norm(R.rand) < R.lb
    i = rand(1:length(R.base))
    R.rand = simplify(R.rand * R.base[i])
    R.exp[i] += 1
  end
  nothing
end

function random_extend(R::RandIdlCtx, f::fmpz)
  R.lb = R.lb*f
  R.ub = R.lb*f
  while norm(R.rand) < R.lb
    i = rand(1:length(R.base))
    R.rand = simplify(R.rand * R.base[i])
    R.exp[i] += 1
  end
  nothing
end


function random_get(R::RandIdlCtx; reduce::Bool = true, repeat::Int = 1)
  while repeat > 0
    repeat -= 1
    if norm(R.rand) >= R.ub
      delta = -1
    elseif norm(R.rand) <= R.lb
      delta = +1
    else
      delta = rand([-1,1])
    end
    i = 1
    while true
      if delta > 0
        i = rand(1:length(R.base))
      else
        j = findall(x -> x != 0, R.exp)
        if length(j) == 0
          return R.rand
        end
        i = rand(findall(x -> x != 0, R.exp))
      end
      R.exp[i] += delta
      if true || !(R.exp in R.last)
        break
      end
      R.exp[i] -= delta
    end  
    if delta > 0
      R.rand = simplify(R.rand * R.base[i])
    else
      R.rand = simplify(R.rand * R.ibase[i]).num
    end
  #  @show R.exp, R.exp in R.last
  end
  push!(R.last, copy(R.exp))
  return R.rand
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

@doc Markdown.doc"""
***
    iscoprime(I::NfAbsOrdIdl, J::NfAbsOrdIdl) -> Bool
> Test if ideals $I,J$ are coprime

"""

function iscoprime(I::NfAbsOrdIdl, J::NfAbsOrdIdl)
  
  @assert order(I) == order(J)
  
  if gcd(minimum(I), minimum(J)) == 1
    return true
  else 
    return isone(I+J)
  end

end 

one(I::NfAbsOrdIdlSet) = ideal(order(I), 1)

###############################################################################
#
#  Extending an ideal
#
###############################################################################

function (I_Zk::NfOrdIdlSet)(a::NfOrdIdl)
  if parent(a) == I_Zk
    return a
  end
  Zk = order(I_Zk)
  Zl = order(a)
  @assert has_2_elem(a)
  b = ideal(Zk, a.gen_one, Zk(Zk.nf(Zl.nf(a.gen_two))))
  for i in [:gens_normal, :gens_weakly_normal, :iszero, :minimum]
    if isdefined(a, i)
      setfield!(b, i, getfield(a, i))
    end
  end
  n = divexact(degree(Zk.nf), degree(Zl.nf))
  if isdefined(a, :norm)
    b.norm = a.norm^n
  end
  if isdefined(a, :princ_gen)
    b.princ_gen = Zk(Zk.nf(Zl.nf(a.princ_gen)))
  end
  if isdefined(a, :isprime) && Zk.nf == Zl.nf && Zk.ismaximal == 1 &&
    Zl.ismaximal == 1
    b.isprime = a.isprime
    if isdefined(a, :splitting_type)
      b.splitting_type = a.splitting_type
    end
  end
  return b
end

#############################################################################
@doc Markdown.doc"""
    eulerphi(A::NfOrdIdl) -> fmpz
> The ideal verision of the totient functionm returns the size of the unit group
> of the residue ring modulo the ideal.
"""
Hecke.eulerphi(A::NfOrdIdl) = Hecke.eulerphi(factor(A))
Hecke.eulerphi(A::FacElem{NfOrdIdl}) = Hecke.eulerphi(factor(A))
function Hecke.eulerphi(A::Dict{NfOrdIdl, Int})
  return prod((norm(p)-1)*norm(p)^(k-1) for (p,k) = A if k < 0 error("ideal not integral"))
end

#basically from
#http://people.math.gatech.edu/~ecroot/shparlinski_final.pdf
#Contini, Croot, Shparlinski: Complexity of inverting the Euler function
@doc Markdown.doc"""
    eulerphi_inv_fac_elem(n::fmpz, zk::NfAbsOrd{AnticNumberField, nf_elem})
> The inverse of the ideal totient funcction: all ideals $A$ s.th the unit group of the 
> residue ring has the required size. Here, the ideals are returned in factorisaed form.
"""
function eulerphi_inv_fac_elem(n::fmpz, zk::NfAbsOrd{AnticNumberField, nf_elem})
  lp = []
  for d = Divisors(n)
    k, p = ispower(d+1)
    if isprime(p)
      ll = prime_decomposition(zk, p)
      for P = ll
        if degree(P[1]) == k
           push!(lp, P[1])
         end
       end
    end
  end
#  println("possible primes: ", lp)

  E = []
  res = []
  for p = lp
    v = valuation(n, norm(p))
    for i=0:v
      push!(E, ((norm(p)-1)*norm(p)^i, [(p, i+1)]))
      if E[end][1] == n
        push!(res, FacElem(Dict(E[end][2])))
      end
    end
  end
  
  while true
    F = []
    for e = E
      nn = divexact(n, e[1])
      x = e[2]
      pm = x[end][1]
      start = true
      for p = lp
        start && p != pm && continue
        start = false
        p == pm && continue
        if nn % (norm(p)-1) == 0
          v = valuation(nn, norm(p))
          for i = 0:v
            push!(F, (e[1]*(norm(p)-1)*norm(p)^i, vcat(e[2], [(p, i+1)])))
            if F[end][1] == n
              push!(res, FacElem(Dict(F[end][2])))
            end
          end
        end
      end
    end
    if length(F) == 0
      return res
    end
    E = F
  end
end

@doc Markdown.doc"""
    eulerphi_inv(n::fmpz, zk::NfAbsOrd{AnticNumberField, nf_elem}) -> Array{NfOrdIdl, 1}
> The inverse of the ideal totient funcction: all ideals $A$ s.th the unit group of the 
> residue ring has the required size. 
"""
eulerphi_inv(n::fmpz, zk::NfAbsOrd) = [ numerator(evaluate(x)) for x = eulerphi_inv_fac_elem(n, zk)]
eulerphi_inv(n::Integer, zk::NfAbsOrd) = [ numerator(evaluate(x)) for x = eulerphi_inv_fac_elem(fmpz(n), zk)]

