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

export deepcopy, parent, order, basis, basis_matrix, basis_mat_inv, minimum, norm,
       ==, in, +, *, intersect, lcm, idempotents, mod, pradical

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

################################################################################
#
#  Basic type functions
#
################################################################################

elem_type(::Type{NfOrdIdlSet}) = NfOrdIdl

elem_type(::NfOrdIdlSet) = NfOrdIdl

parent_type(::Type{NfOrdIdl}) = NfOrdIdlSet

################################################################################
#
#  Comparison
#
################################################################################

==(x::NfAbsOrdIdlSet, y::NfAbsOrdIdlSet) = x.order === y.order

################################################################################
#
#  Hashing
#
################################################################################

# a (bad) hash function
# - slow (due to basis)
# - unless basis is in HNF it is also non-unique
function Base.hash(A::NfAbsOrdIdl, h::UInt)
  return Base.hash(basis_matrix(A, copy = false), h)
end

################################################################################
#
#  String I/O
#
################################################################################

function show(io::IO, a::NfAbsOrdIdlSet)
  print(io, "Set of ideals of ")
  show(Base.IOContext(io, :compact => true), order(a))
  print(io, "\n")
end

function show(io::IO, a::NfAbsOrdIdl)
  if ismaximal_known_and_maximal(order(a))
    return show_maximal(io, a)
  else
    return show_gen(io, a)
  end
end

function show_gen(io::IO, a::NfAbsOrdIdl)
  print(io, "Ideal of (")
  show(IOContext(io, :compact => true), order(a))
  print(io, ")\n")

  if has_2_elem(a)
      print(io, "generated by \n")
      print(io, "<", a.gen_one, ", ", a.gen_two, ">" )
  else
    print(io, "with basis matrix\n")
    print(io, basis_matrix(a, copy = false))
  end
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
    elseif isdefined(id, :basis_matrix)
        print(io, "\nbasis_matrix \n", id.basis_matrix)
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
     if isdefined(id, :basis_matrix)
       print(io, "\nbasis_matrix \n", id.basis_matrix)
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
    ideal(O::NfAbsOrd, v::Vector{NfAbsOrdElem}) -> NfAbsOrdIdl

Creates the ideal of $O$ generated by the elements contained in $v$.
"""
function ideal(O::NfAbsOrd, v::Vector{<:NfAbsOrdElem})
  if isempty(v)
    return ideal(O, 0)
  end
  for i = 1:length(v)
    @assert O === parent(v[i])
  end
  M = zero_matrix(FlintZZ, 2*degree(O), degree(O))
  M1 = representation_matrix(v[1])
  _hnf!(M1, :lowerleft)
  _copy_matrix_into_matrix(M, degree(O)+1, 1, M1)
  if isone(basis(O)[1])
    m = M1[1, 1]
  else
    m = prod(fmpz[M1[i, i] for i = 1:nrows(M1)])
  end
  for i = 2:length(v)
    M1 = representation_matrix_mod(v[i], m)
    _copy_matrix_into_matrix(M, 1, 1, M1)
    hnf_modular_eldiv!(M, m, :lowerleft)
    if isone(basis(O)[1])
      m = M[degree(O)+1, 1]
    else
      m = prod(fmpz[M[i+degree(O), i] for i = 1:ncols(M)])
    end
    if isone(m)
      return ideal(O, 1)
    end
  end
  return _ideal(O, sub(M, degree(O)+1:2*degree(O), 1:degree(O)))::ideal_type(O)
end

@doc Markdown.doc"""
    ideal(O::NfOrd, x::NfOrdElem) -> NfAbsOrdIdl

Creates the principal ideal $(x)$ of $\mathcal O$.
"""
function ideal(O::NfAbsOrd, x::NfAbsOrdElem)
  return NfAbsOrdIdl(deepcopy(x))
end

@doc Markdown.doc"""
    ideal(O::NfOrd, x::fmpz_mat, check::Bool = false, x_in_hnf::Bool = false) -> NfAbsOrdIdl

Creates the ideal of $\mathcal O$ with basis matrix $x$. If `check` is set, then it is
checked whether $x$ defines an ideal (expensive). If `x_in_hnf` is set, then it is assumed
that $x$ is already in lower left HNF.
"""
function ideal(O::NfAbsOrd, x::fmpz_mat, check::Bool = false, x_in_hnf::Bool = false)
  !x_in_hnf ? x = _hnf(x, :lowerleft) : nothing #sub-optimal, but == relies on the basis being thus
  #_trace_call(;print = true)
  I = NfAbsOrdIdl(O, x)
  # The compiler stopped liking this recursion??
  # if check
  #   J = ideal(O, basis(I))
  #   @assert J == I
  # end

  return I
end

function _ideal(O::NfAbsOrd, x::fmpz_mat, x_in_hnf::Bool = false)
  !x_in_hnf ? x = _hnf(x, :lowerleft) : nothing #sub-optimal, but == relies on the basis being thus
  #_trace_call(;print = true)
  I = NfAbsOrdIdl(O, x)

  return I
end

@doc Markdown.doc"""
    ideal(O::NfOrd, x::fmpz, y::NfOrdElem) -> NfAbsOrdIdl
    ideal(O::NfOrd, x::Integer, y::NfOrdElem) -> NfAbsOrdIdl

Creates the ideal $(x, y)$ of $\mathcal O$.
"""
function ideal(O::NfAbsOrd, x::fmpz, y::NfAbsOrdElem)
  @assert parent(y) === O
  return NfAbsOrdIdl(deepcopy(x), deepcopy(y))
end

function ideal(O::NfAbsOrd, x::Integer, y::NfAbsOrdElem)
  @assert parent(y) === O
  return NfAbsOrdIdl(fmpz(x), deepcopy(y))
end

function ideal(O::NfAbsOrd)
  return NfAbsOrdIdl(O)
end

function (S::NfAbsOrdIdlSet)()
   return NfAbsOrdIdl(order(S))
end

@doc Markdown.doc"""
    ideal(O::NfOrd, a::fmpz) -> NfAbsOrdIdl
    ideal(O::NfOrd, a::Integer) -> NfAbsOrdIdl

Returns the ideal of $\mathcal O$ which is generated by $a$.
"""
ideal(O::NfAbsOrd, a::fmpz)  = NfAbsOrdIdl(O, deepcopy(a))
ideal(O::NfAbsOrd, a::Int) = NfAbsOrdIdl(O, a)
ideal(O::NfAbsOrd, a::Integer) = NfAbsOrdIdl(O, fmpz(a))

function ideal_from_z_gens(O::NfOrd, b::Vector{NfOrdElem}, check::Bool = false)
  for i = 1:length(b)
    @assert parent(b[i]) === O
  end
  d = degree(O)
  @assert length(b) >= d

  M = zero_matrix(FlintZZ, length(b), d)
  for i = 1:length(b)
    el = coordinates(b[i])
    for j = 1:d
      M[i, j] = el[j]
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
    order(x::NfAbsOrdIdl) -> NfAbsOrd

Returns the order, of which $x$ is an ideal.
"""
order(a::NfAbsOrdIdlSet) = a.order

################################################################################
#
#  Principal ideal creation
#
################################################################################

@doc Markdown.doc"""
    *(O::NfOrd, x::NfOrdElem) -> NfAbsOrdIdl
    *(x::NfAbsOrdElem, O::NfAbsOrd) -> NfAbsOrdIdl

Returns the principal ideal $(x)$ of $\mathcal O$.
"""
function *(O::NfAbsOrd, x::NfAbsOrdElem)
  parent(x) !== O && error("Order of element does not coincide with order")
  return ideal(O, x)
end

*(x::NfAbsOrdElem, O::NfAbsOrd) = O*x
*(x::Int, O::NfAbsOrd) = ideal(O, x)
*(x::BigInt, O::NfAbsOrd) = ideal(O, fmpz(x))
*(x::fmpz, O::NfAbsOrd) = ideal(O, x)

###########################################################################################
#
#   Basis
#
###########################################################################################

@doc Markdown.doc"""
    has_basis(A::NfAbsOrdIdl) -> Bool

Returns whether $A$ has a basis already computed.
"""
@inline has_basis(A::NfAbsOrdIdl) = isdefined(A, :basis)

function assure_has_basis(A::NfAbsOrdIdl)
  if isdefined(A, :basis)
    return nothing
  else
    assure_has_basis_matrix(A)
    O = order(A)
    M = A.basis_matrix
    Ob = basis(O, copy = false)
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
    basis(A::NfAbsOrdIdl) -> Vector{NfOrdElem}

Returns the basis of $A$.
"""
@inline function basis(A::NfAbsOrdIdl; copy::Bool = true)
  assure_has_basis(A)
  if copy
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
    has_basis_matrix(A::NfAbsOrdIdl) -> Bool

Returns whether $A$ knows its basis matrix.
"""
@inline has_basis_matrix(A::NfAbsOrdIdl) = isdefined(A, :basis_matrix)

@doc Markdown.doc"""
    basis_matrix(A::NfAbsOrdIdl) -> fmpz_mat

Returns the basis matrix of $A$.
"""
function basis_matrix(A::NfAbsOrdIdl; copy::Bool = true)
  assure_has_basis_matrix(A)
  if copy
    return deepcopy(A.basis_matrix)
  else
    return A.basis_matrix
  end
end

function assure_has_basis_matrix(A::NfAbsOrdIdl)
  if isdefined(A, :basis_matrix)
    return nothing
  end
  OK = order(A)
  n = degree(OK)

  if iszero(A)
    A.basis_matrix = zero_matrix(FlintZZ, n, n)
    return nothing
  end

  if has_princ_gen_special(A)
    A.basis_matrix = scalar_matrix(FlintZZ, n, princ_gen_special(A))
    return nothing
  end

  if !issimple(nf(OK)) || !isdefining_polynomial_nice(nf(OK))
    c = hnf_modular_eldiv!(representation_matrix(A.gen_two), A.gen_one, :lowerleft)
    A.basis_matrix = c
    return nothing
  end

  if !issimple(nf(OK)) && isdefined(A, :is_prime) && A.is_prime == 1 &&
         A.norm == A.minimum && !isindex_divisor(OK, A.minimum)
    # A is a prime ideal of degree 1
    A.basis_matrix = basis_mat_prime_deg_1(A)
    return nothing
  end

  if has_princ_gen(A)
    A.basis_matrix = hnf_modular_eldiv!(representation_matrix_mod(A.princ_gen, minimum(A)), minimum(A), :lowerleft)
    return nothing
  end

  @hassert :NfOrd 1 has_2_elem(A)

  m = abs(A.gen_one)
  if has_minimum(A)
    m = minimum(A, copy = false)
  end
  be = elem_in_nf(A.gen_two)
  if contains_equation_order(OK)
    be = mod(be, m)
  end
  rm = representation_matrix_mod(OK(be, false), m)
  hnf_modular_eldiv!(rm, m, :lowerleft)
  A.basis_matrix = rm
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
  bas = basis(O, copy = false)
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

# For compatibility with AlgAssAbsOrdIdl
function integral_basis_matrix_wrt(A::NfAbsOrdIdl, O::NfAbsOrd; copy::Bool = true)
  @assert O === order(A)
  return basis_matrix(A, copy = copy)
end

################################################################################
#
#  Basis matrix inverse
#
################################################################################

@doc Markdown.doc"""
    has_basis_mat_inv(A::NfAbsOrdIdl) -> Bool

Returns whether $A$ knows its inverse basis matrix.
"""
@inline has_basis_mat_inv(A::NfAbsOrdIdl) = isdefined(A, :basis_mat_inv)

@doc Markdown.doc"""
    basis_mat_inv(A::NfAbsOrdIdl) -> fmpz_mat

Returns the inverse basis matrix of $A$.
"""
function basis_mat_inv(A::NfAbsOrdIdl; copy::Bool = true) where T
  assure_has_basis_mat_inv(A)
  if copy
    return deepcopy(A.basis_mat_inv)
  else
    return A.basis_mat_inv
  end
end

@doc Markdown.doc"""
    basis_mat_inv(A::NfAbsOrdIdl) -> FakeFmpqMat

Returns the inverse of the basis matrix of $A$.
"""
function assure_has_basis_mat_inv(A::NfAbsOrdIdl)
  if isdefined(A, :basis_mat_inv)
    return nothing
  else
    if degree(order(A)) == 1
      # This will be fixed in flint 2.7
      A.basis_mat_inv = FakeFmpqMat(identity_matrix(FlintZZ, 1), basis_matrix(A, copy = false)[1, 1])
    else
      A.basis_mat_inv = FakeFmpqMat(pseudo_inv(basis_matrix(A, copy = false)))
    end
    return nothing
  end
end

################################################################################
#
#  Minimum
#
################################################################################

@doc Markdown.doc"""
    has_minimum(A::NfAbsOrdIdl) -> Bool

Returns whether $A$ knows its mininum.
"""
function has_minimum(A::NfAbsOrdIdl)
  return isdefined(A, :minimum)
end

@doc Markdown.doc"""
    minimum(A::NfAbsOrdIdl) -> fmpz

Returns the smallest nonnegative element in $A \cap \mathbf Z$.
"""
function minimum(A::NfAbsOrdIdl; copy::Bool = true)
  assure_has_minimum(A)
  if copy
    return deepcopy(A.minimum)
  else
    return A.minimum
  end
end

function assure_has_minimum(A::NfAbsOrdIdl)
  if has_minimum(A)
    return nothing
  end

  if degree(order(A)) == 1
    if has_2_elem(A)
      # I want A.gen_two.elem_in_nf as an element of Q,
      # but there is no method for this.
      # Since the degree is 1, we just cheat :)
      A.minimum = gcd(A.gen_one, numerator(trace(A.gen_two.elem_in_nf)))
    else
      A.minimum = deepcopy(A.basis_matrix[1, 1])
    end
    return nothing
  end

  if isdefined(A, :basis_matrix) && isone(basis(order(A), copy = false)[1])
    A.minimum = basis_matrix(A, copy = false)[1, 1]
    return nothing
  end

  if has_princ_gen(A)
    b = A.princ_gen.elem_in_nf
    if iszero(b)
      A.minimum = fmpz(0)
      A.iszero = 1
    else
      if issimple(nf(order(A))) && isdefining_polynomial_nice(nf(order(A))) && order(A).ismaximal == 1
        A.minimum = _minmod(A.gen_one, A.gen_two)
        @hassert :Rres 1 A.minimum == denominator(inv(b), order(A))
      else
        bi = inv(b)
        A.minimum = denominator(bi, order(A))
      end
    end
    return nothing
  end


  if has_2_elem(A)
    K = nf(order(A))
    if iszero(A.gen_two)
      # A = (A.gen_one, 0) = (A.gen_one)
      d = abs(A.gen_one)
      A.minimum = d
      return nothing
    elseif issimple(nf(order(A))) && isdefining_polynomial_nice(nf(order(A))) && order(A).ismaximal == 1
      d = _minmod(A.gen_one, A.gen_two)
      @hassert :Rres 1 d == gcd(A.gen_one, denominator(inv(A.gen_two.elem_in_nf), order(A)))
      A.minimum = d
      return nothing
    end
  end


  if has_weakly_normal(A)
    d = denominator(inv(K(A.gen_two)), order(A))
    d = gcd(d, FlintZZ(A.gen_one))
    A.minimum = d
    return nothing
  end

  if isone(basis(order(A), copy = false)[1])
    A.minimum = basis_matrix(A, copy = false)[1, 1]
  else
    M = basis_matrix(A, copy = false)
    d = prod(fmpz[M[i, i] for i = 1:nrows(M)])
    v = matrix(FlintZZ, 1, nrows(M), coordinates(order(A)(d)))
    fl, s = can_solve_with_solution(M, v, side = :left)
    @assert fl
    den = denominator(s[1]//d)
    for i = 2:ncols(s)
      den = lcm(den, denominator(s[i]//d))
    end
    A.minimum = den
  end
  return nothing
end

################################################################################
#
#  Norm
#
################################################################################

@doc Markdown.doc"""
    has_norm(A::NfAbsOrdIdl) -> Bool

Returns whether $A$ knows its norm.
"""
function has_norm(A::NfAbsOrdIdl)
  return isdefined(A, :norm)
end

function assure_has_norm(A::NfAbsOrdIdl)
  if has_norm(A)
    return nothing
  end

  if isdefined(A, :basis_matrix)
    A.norm = abs(det(basis_matrix(A, copy = false)))
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
    #if new
      A.norm = _normmod(A.gen_one^degree(order(A)), A.gen_two)
      @hassert :Rres 1 A.norm == gcd(norm(order(A)(A.gen_one)), norm(A.gen_two))
    #else
    #  A.norm = gcd(norm(order(A)(A.gen_one)), norm(A.gen_two))
    #end
    return nothing
  end

  assure_has_basis_matrix(A)
  A.norm = abs(det(basis_matrix(A, copy = false)))
  return nothing
end

@doc Markdown.doc"""
    norm(A::NfAbsOrdIdl) -> fmpz

Returns the norm of $A$, that is, the cardinality of $\mathcal O/A$, where
$\mathcal O$ is the order of $A$.
"""
function norm(A::NfAbsOrdIdl; copy::Bool = true)
  assure_has_norm(A)
  if copy
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
    has_princ_gen(A::NfAbsOrdIdl) -> Bool

Returns whether $A$ knows if it is generated by one element.
"""
function has_princ_gen(A::NfAbsOrdIdl)
  return isdefined(A, :princ_gen)
end

@doc Markdown.doc"""
    has_princ_gen_special(A::NfAbsOrdIdl) -> Bool

Returns whether $A$ knows if it is generated by a rational integer.
"""
function has_princ_gen_special(A::NfAbsOrdIdl)
  if isdefined(A, :princ_gen_special)
    return true
  end
  if has_norm(A) && has_minimum(A) && norm(A, copy = false) == minimum(A, copy = false)^degree(order(A))
    if fits(Int, minimum(A, copy = false))
      A.princ_gen_special = (1, Int(minimum(A, copy = false)), 0)
    else
      A.princ_gen_special = (2, 0, minimum(A, copy = false))
    end
    return true
  end
  return false
end

princ_gen_special(A::NfAbsOrdIdl) = A.princ_gen_special[A.princ_gen_special[1] + 1]

################################################################################
#
#  Equality
#
################################################################################

function ==(x::NfAbsOrdIdl, y::NfAbsOrdIdl)
  @assert order(x) === order(y)
  if x === y
    return true
  end
  if has_2_elem(x) && has_2_elem(y)
    if x.gen_one == y.gen_one && x.gen_two == y.gen_two
      return true
    end
  end
  if isdefined(x, :norm) && isdefined(y, :norm)
    if x.norm != y.norm
      return false
    end
  end
  if isdefined(x, :minimum) && isdefined(y, :minimum)
    if x.minimum != y.minimum
      return false
    end
  end
  if isprime_known(x) && isprime_known(y)
    if is_prime(x) != is_prime(y)
      return false
    end
  end
  if isdefined(x, :basis_matrix) && isdefined(y, :basis_matrix)
    if is_hnf(basis_matrix(x, copy = false), :lowerleft) && is_hnf(basis_matrix(y, copy = false), :lowerleft)
      return basis_matrix(x, copy = false) == basis_matrix(y, copy = false)
    end
  end
  if isprime_known(x) && is_prime(x) && isprime_known(y) && is_prime(y)
    px = minimum(x, copy = false)
    py = minimum(y, copy = false)
    if px != py
      return false
    end
    OK = order(x)
    if contains_equation_order(OK) && !isindex_divisor(OK, px) && has_2_elem(x) && has_2_elem(y)
      R = ResidueRing(FlintZZ, px, cached = false)
      Rx = PolynomialRing(R, "x", cached = false)[1]
      f1 = Rx(elem_in_nf(x.gen_two))
      f2 = Rx(elem_in_nf(y.gen_two))
      return !iscoprime(f1, f2)
    end
  end
  if isdefined(x, :basis_matrix) && has_2_elem(y)
    if !divisible(y.gen_one, minimum(x, copy = false))
      return false
    end
    if !(y.gen_two in x)
      return false
    end
    return norm(x) == norm(y)
  end
  if isdefined(y, :basis_matrix) && has_2_elem(y)
    if !divisible(x.gen_one, minimum(y, copy = false))
      return false
    end
    if !(x.gen_two in y)
      return false
    end
    return norm(x) == norm(y)
  end


  return _hnf(basis_matrix(x, copy = false), :lowerleft) == _hnf(basis_matrix(y, copy = false), :lowerleft)
end

################################################################################
#
#  Inclusion of elements in ideals
#
################################################################################

@doc Markdown.doc"""
    in(x::NumFieldOrdElem, y::NumFieldOrdIdl)
    in(x::NumFieldElem, y::NumFieldOrdIdl)
    in(x::fmpz, y::NumFieldOrdIdl)

Returns whether $x$ is contained in $y$.
"""
function in(x::NfAbsOrdElem, y::NfAbsOrdIdl)
  OK = order(y)
  parent(x) !== order(y) && error("Order of element and ideal must be equal")
  if ismaximal_known_and_maximal(OK) && y.is_prime == 1 && has_2_elem(y) && has_2_elem_normal(y)
    ant = anti_uniformizer(y)
    return (elem_in_nf(x) * ant) in OK
  end
  return containment_by_matrices(x, y)
end

function containment_by_matrices(x::NfAbsOrdElem, y::NfAbsOrdIdl)
  R = ResidueRing(FlintZZ, basis_mat_inv(y, copy = false).den, cached = false)
  M = map_entries(R, basis_mat_inv(y, copy = false).num)
  v = matrix(R, 1, degree(parent(x)), coordinates(x, copy = false))
  mul!(v, v, M)
  return iszero(v)
end

function in(x::nf_elem, y::NfAbsOrdIdl)
  parent(x) !== nf(order(y)) && error("Number field of element and ideal must be equal")
  return in(order(y)(x),y)
end

in(x::fmpz, y::NfAbsOrdIdl) = in(order(y)(x),y)

in(x::Integer, y::NfAbsOrdIdl) = in(order(y)(x), y)

################################################################################
#
#  Inverse
#
################################################################################

@doc Markdown.doc"""
    inv(A::NfAbsOrdIdl) -> NfOrdFracIdl

Computes the inverse of $A$, that is, the fractional ideal $B$ such that
$AB = \mathcal O_K$.
"""
function inv(A::NfAbsOrdIdl)
  @assert !iszero(A)
  if ismaximal_known_and_maximal(order(A))
    return inv_maximal(A)
  end
  if has_2_elem(A)
    m = A.gen_one
    if has_minimum(A)
      m = minimum(A)
    end
    if iscoprime(m, discriminant(order(A)))
      return inv_maximal(A)
    end
  end
  return inv_generic(A)
end

# If I is not coprime to the conductor of O in the maximal order, then this might
# not be an inverse.
function inv_generic(A::NfAbsOrdIdl)
  O = order(A)
  return colon(O(1)*O, A)
end

function inv_maximal(A::NfAbsOrdIdl)
  O = order(A)
  if has_princ_gen_special(A)
    return fractional_ideal(O, ideal(O, 1), princ_gen_special(A))
  elseif isdefined(A, :princ_gen) && !has_2_elem_normal(A)
    res =  ideal(O, inv(A.princ_gen.elem_in_nf))
  elseif has_2_elem(A) && has_weakly_normal(A)
    assure_2_normal(A)
    O = order(A)
    if iszero(A.gen_two)
      return fractional_ideal(O, ideal(O, 1), A.gen_one)
    end
    m = A.gen_one
    if has_minimum(A)
      m = minimum(A, copy = false)
    end
    if isone(m)
      return fractional_ideal(O, A)
    end
    alpha = _invmod(m, A.gen_two)
    _, d = ppio(denominator(alpha, O), m)
    Ai = NfAbsOrdIdl(order(A))
    dn = denominator(d*alpha, O)
    @hassert :NfOrd 1 ppio(dn, m)[1] == dn
    Ai.gen_one = dn
    Ai.gen_two = O(d*alpha*dn, false)
    temp = dn^degree(order(A))//norm(A)
    @hassert :NfOrd 1 denominator(temp) == 1
    Ai.norm = numerator(temp)
    Ai.gens_normal = A.gens_normal
    AAi = fractional_ideal(O, Ai, dn)
    return AAi
  else
    # I don't know if this is a good idea
    _assure_weakly_normal_presentation(A)
    assure_2_normal(A)
    return inv(A)
  end
end

@doc Markdown.doc"""
    is_invertible(A::NfAbsOrdIdl) -> Bool, NfOrdFracIdl

Returns `true` and an inverse of $A$ or `false` and an ideal $B$ such that
$A*B \subsetneq order(A)$, if $A$ is not invertible.
"""
function is_invertible(A::NfAbsOrdIdl)
  if iszero(A)
    return false, A
  end

  if ismaximal_known_and_maximal(order(A))
    return true, inv(A)
  end

  i1 = gen_index(maximal_order(nf(order(A))))
  i2 = gen_index(order(A))
  i = i1*inv(i2)
  @assert isone(denominator(i))
  if isone(gcd(numerator(i), minimum(A, copy = false)))
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

function _minmod(a::fmpz, b::NfAbsOrdElem)
  return mod(denominator(inv(b.elem_in_nf), parent(b)), a)
end

function _minmod_easy(a::fmpz, b::NfOrdElem)
  Zk = parent(b)
  k = number_field(Zk)
  if fits(Int, a)
    S = ResidueRing(FlintZZ, Int(a), cached = false)
    St = PolynomialRing(S, cached=false)[1]
    B = St(b.elem_in_nf)
    F = St(k.pol)
    m = data(rres(B, F))
    return gcd(a, m)
  else
    S1 = ResidueRing(FlintZZ, a, cached = false)
    St1 = PolynomialRing(S1, cached=false)[1]
    B1 = St1(b.elem_in_nf)
    F1 = St1(k.pol)
    m1 = data(rres(B1, F1))
    return gcd(a, m1)
  end
end

function _minmod_easy_pp(a::fmpz, b::NfOrdElem)
  Zk = parent(b)
  k = number_field(Zk)
  if fits(Int, a)
    S = ResidueRing(FlintZZ, Int(a), cached = false)
    St = PolynomialRing(S, cached=false)[1]
    B = St(b.elem_in_nf)
    F = St(k.pol)
    m = lift(rres_sircana_pp(B, F))
    return gcd(a, m)
  else
    S1 = ResidueRing(FlintZZ, a, cached = false)
    St1 = PolynomialRing(S1, cached=false)[1]
    B1 = St1(b.elem_in_nf)
    F1 = St1(k.pol)
    m1 = lift(rres_sircana_pp(B1, F1))
    return gcd(a, m1)
  end
end

function _minmod(a::fmpz, b::NfOrdElem)
  if isone(a)
    return a
  end
  if iszero(a)
    return fmpz(0)
  end

  if !isdefining_polynomial_nice(nf(parent(b)))
    return gcd(denominator(inv(b.elem_in_nf), parent(b)), a)
  end
  lf, ar = _factors_trial_division(a, 10^2)
  min = fmpz(1)
  for p in lf
    ap = p^valuation(a, p)
    mul!(min, min, _minmod_comp_pp(ap, b))
  end
  if isone(ar)
    return min
  end
  mul!(min, min, _minmod_comp(ar, b))
  @hassert :NfOrd 1 min == gcd(denominator(inv(b.elem_in_nf), parent(b)), a)
  return min
end

function _minmod_comp_pp(a::fmpz, b::NfOrdElem)
  #a is a prime power
  Zk = parent(b)
  k = number_field(Zk)
  acom, auncom = ppio(a, index(Zk))
  @assert acom == a || auncom == a
  min_uncom = _minmod_easy_pp(auncom, b)
  if isone(acom)
    return min_uncom
  end
  e, _ = ppio(denominator(basis_matrix(Zk, copy = false)), acom)
  d = denominator(b.elem_in_nf)
  d, _ = ppio(d, acom)
  mod = acom*d*e
  if fits(Int, mod)
    S1 = ResidueRing(FlintZZ, Int(mod), cached = false)
    St1 = PolynomialRing(S1, cached=false)[1]
    B1 = St1(d*b.elem_in_nf)
    F1 = St1(k.pol)
    m1, u1, v1 = rresx_sircana_pp(B1, F1)  # u*B + v*F = m mod modulus(S)
    U1 = lift(FlintZZ["x"][1], u1)
    # m can be zero...
    m2 = lift(m1)
    if iszero(m2)
      m2 = mod
    end
    bi = k(U1)//m2*d # at this point, bi*d*b = m mod a*d*idx
    d = denominator(bi, Zk)
    return min_uncom*gcd(d, acom)
  else
    S = ResidueRing(FlintZZ, mod, cached = false)
    St = PolynomialRing(S, cached=false)[1]
    B = St(d*b.elem_in_nf)
    F = St(k.pol)
    m, u, v = rresx_sircana_pp(B, F)  # u*B + v*F = m mod modulus(S)
    U = lift(FlintZZ["x"][1], u)
    # m can be zero...
    m3 = lift(m)
    if iszero(m3)
      m3 = mod
    end
    bi = k(U)//m3*d # at this point, bi*d*b = m mod a*d*idx
    d = denominator(bi, Zk)
    return min_uncom*gcd(d, acom)
  end

end


function _minmod_comp(a::fmpz, b::NfOrdElem)

  Zk = parent(b)
  k = number_field(Zk)
  acom, auncom = ppio(a, index(Zk))
  min_uncom = _minmod_easy(auncom, b)
  if isone(acom)
    return min_uncom
  end
  e, _ = ppio(denominator(basis_matrix(Zk, copy = false)), acom)
  d = denominator(b.elem_in_nf)
  d, _ = ppio(d, acom)
  mod = acom*d*e
  if fits(Int, mod)
    S1 = ResidueRing(FlintZZ, Int(mod), cached = false)
    St1 = PolynomialRing(S1, cached=false)[1]
    B1 = St1(d*b.elem_in_nf)
    F1 = St1(k.pol)
    m1, u1, v1 = rresx(B1, F1)  # u*B + v*F = m mod modulus(S)
    U1 = lift(FlintZZ["x"][1], u1)
    # m can be zero...
    m2 = lift(m1)
    if iszero(m2)
      m2 = mod
    end
    bi = k(U1)//m2*d # at this point, bi*d*b = m mod a*d*idx
    d = denominator(bi, Zk)
    return min_uncom*gcd(d, acom)
  else
    S = ResidueRing(FlintZZ, mod, cached = false)
    St = PolynomialRing(S, cached=false)[1]
    B = St(d*b.elem_in_nf)
    F = St(k.pol)
    m, u, v = rresx(B, F)  # u*B + v*F = m mod modulus(S)
    U = lift(FlintZZ["x"][1], u)
    # m can be zero...
    m3 = lift(m)
    if iszero(m3)
      m3 = mod
    end
    bi = k(U)//m3*d # at this point, bi*d*b = m mod a*d*idx
    d = denominator(bi, Zk)
    return min_uncom*gcd(d, acom)
  end
  # min(<a, b>) = min(<ad, bd>)/d and bd is in the equation order, hence max as well
  # min(a, b) = gcd(a, denominator(b))
  # rres(b, f) = <b, f> meet Z = <r> and
  # ub + vf = r
  # so u/r is the inverse and r is the den in the field
  # we want gcd(r, a). so we use rres
  #at this point, min(<a, b*d>) SHOULD be
end

function _invmod(a::fmpz, b::NfAbsOrdElem)
  return inv(b.elem_in_nf)
end

function _invmod(a::fmpz, b::NfOrdElem)
  Zk = parent(b)
  k = nf(Zk)
  if isone(a)
    return one(k)
  end
  if !isdefining_polynomial_nice(nf(parent(b)))
    return inv(k(b))
  end
  return __invmod(a, b)
end



function __invmod(a::fmpz, b::NfOrdElem)
  Zk = parent(b)
  k = nf(Zk)
  d = denominator(b.elem_in_nf)
  d, _ = ppio(d, a)
   e, _ = ppio(basis_matrix(Zk, copy = false).den, a)
  mod_r = a^2*d*e
  if fits(Int, mod_r)
    S1 = ResidueRing(FlintZZ, Int(mod_r), cached=false)
    S1t = PolynomialRing(S1, cached=false)[1]
    B1 = S1t(d*b.elem_in_nf)
    F1 = S1t(k.pol)
    m1, u1, v1 = rresx(B1, F1)  # u*B + v*F = m mod modulus(S)
    if iszero(m1)
      m1 = mod_r
      c1 = S1(1)
    else
      c1 = inv(canonical_unit(m1))
      m1 = lift(m1*c1)
    end
    U1 = lift(PolynomialRing(FlintZZ, "x", cached = false)[1], u1*c1)
    bi1 = k(U1)//m1*d # at this point, bi*d*b = m mod a*d*idx
    return bi1
  else
    S = ResidueRing(FlintZZ, mod_r, cached=false)
    St = PolynomialRing(S, cached=false)[1]
    B = St(d*b.elem_in_nf)
    F = St(k.pol)

    m, u, v = rresx(B, F)  # u*B + v*F = m mod modulus(S)
    if iszero(m)
      m = mod_r
      c = S(1)
    else
      c = inv(canonical_unit(m))
      m = lift(m*c)
    end
    U = lift(PolynomialRing(FlintZZ, "x", cached = false)[1], u*c)
    bi = k(U)//m*d # at this point, bi*d*b = m mod a*d*idx
    return bi
  end
  end

function _normmod(a::fmpz, b::NfAbsOrdElem)
  return gcd(norm(b), a)
end

function _normmod(a::fmpz, b::NfOrdElem)
  if isone(a)
    return a
  end

  if !isdefining_polynomial_nice(nf(parent(b)))
    return gcd(norm(b), a)
  end

  mods = fmpz[]
  resp = fmpz[]
  a2, ar = ppio(a, fmpz(2))
  if !isone(a2)
    push!(mods, a2)
    push!(resp, _normmod_comp(a2, b))
  end
  a3, ar = ppio(ar, fmpz(3))
  if !isone(a3)
    push!(mods, a3)
    push!(resp, _normmod_comp(a3, b))
  end
  a5, ar = ppio(ar, fmpz(5))
  if !isone(a5)
    push!(mods, a5)
    push!(resp, _normmod_comp(a5, b))
  end
  a7, ar = ppio(ar, fmpz(7))
  if !isone(a7)
    push!(mods, a7)
    push!(resp, _normmod_comp(a7, b))
  end
  if !isone(ar)
    push!(mods, ar)
    push!(resp, _normmod_comp(ar, b))
  end
  if isone(length(mods))
    @hassert :NfOrd 1 gcd(norm(b), a) == resp[1]
    return resp[1]
  else
    res = gcd(crt(resp, mods), a)
    @hassert :NfOrd 1 gcd(norm(b), a) == res
    return res
  end

end

function _normmod_comp(a::fmpz, b::NfOrdElem)
  if isone(a)
    return a
  end

  Zk = parent(b)
  k = number_field(Zk)
  d = denominator(b.elem_in_nf)
  com, uncom = ppio(d, a)
  mod = a*com^degree(k)
  if fits(Int, mod)
    R = ResidueRing(FlintZZ, Int(mod), cached=false)
    Rt = PolynomialRing(R, cached=false)[1]
    B1 = Rt(d*b.elem_in_nf)
    F1 = Rt(k.pol)
    m2 = resultant_ideal(B1, F1)  # u*B + v*F = m mod modulus(S)
    m3 = gcd(modulus(R), lift(m2))
    return divexact(m3, com^degree(parent(b)))
  else
    S = ResidueRing(FlintZZ, mod, cached=false)
    St = PolynomialRing(S, cached=false)[1]
    B = St(d*b.elem_in_nf)
    F = St(k.pol)
    m = resultant_ideal(B, F)  # u*B + v*F = m mod modulus(S)
    m1 = gcd(modulus(S), lift(m))
    return divexact(m1, com^degree(parent(b)))
  end

end

function simplify(A::NfAbsOrdIdl)
  if iszero(A)
    return A
  end
  if isone(A)
    A.gen_one = fmpz(1)
    A.gen_two = order(A)(1)
    A.minimum = fmpz(1)
    A.norm = fmpz(1)
    A.gens_normal = fmpz(2)
    @hassert :NfOrd 1 isconsistent(A)
    return A
  end
  @hassert :NfOrd 1 isconsistent(A)
  if has_2_elem(A) && has_weakly_normal(A)
    #if maximum(element_to_sequence(A.gen_two)) > A.gen_one^2
    #  A.gen_two = element_reduce_mod(A.gen_two, A.parent.order, A.gen_one^2)
    #end
    if !has_minimum(A)
      if isdefined(A, :norm)
        d = gcd(A.norm, A.gen_one)
        A.minimum = _minmod(d, A.gen_two)
      else
        A.minimum = _minmod(A.gen_one, A.gen_two)
      end
      @hassert :Rres 1 A.minimum == gcd(A.gen_one, denominator(inv(A.gen_two.elem_in_nf), order(A)))
    end
    A.gen_one = A.minimum
    if !isdefined(A, :norm)
      if false
        #norm seems to be cheap, while inv is expensive
        #TODO: improve the odds further: currently, the 2nd gen has small coeffs in the
        #      order basis. For this it would better be small in the field basis....
        n = _normmod(A.gen_one^degree(order(A)), A.gen_two)
        @hassert :Rres 1 n == gcd(A.gen_one^degree(order(A)), FlintZZ(norm(A.gen_two)))
      else
        n = gcd(A.gen_one^degree(order(A)), FlintZZ(norm(A.gen_two)))
      end
      A.norm = n
    end
    be = mod(A.gen_two.elem_in_nf, A.gen_one^2)
    A.gen_two = order(A)(be, false)


    if isdefined(A, :gens_normal)
      A.gens_normal = A.gen_one
    end

    @hassert :NfOrd 1 isconsistent(A)
    return A
  end
  @hassert :NfOrd 1 isconsistent(A)
  return A
end

################################################################################
#
#  Trace matrix
#
################################################################################

function trace_matrix(A::NfAbsOrdIdl)
  g = trace_matrix(order(A))
  b = basis_matrix(A, copy = false)
#  mul!(b, b, g)   #b*g*b' is what we want.
#                  #g should not be changed? b is a copy.
#  mul!(b, b, b')  #TODO: find a spare tmp-mat and use transpose
  return b*g*transpose(b)
end

################################################################################
#
#  Power detection
#
################################################################################

@doc Markdown.doc"""
    is_power(I::NfAbsOrdIdl) -> Int, NfAbsOrdIdl
    is_power(a::NfOrdFracIdl) -> Int, NfOrdFracIdl

Writes $a = r^e$ with $e$ maximal. Note: $1 = 1^0$.
"""
function is_power(I::NfAbsOrdIdl)
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

  e, ra = is_power(m)
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

function is_power(I::NfOrdFracIdl)
  num, den = integral_split(I)
  e, r = is_power(num)
  if e == 1
    return e, I
  end
  f, s = is_power(den)
  g = gcd(e, f)
  return g, r^div(e, g)//s^div(f, g)
end

@doc Markdown.doc"""
    is_power(A::NfAbsOrdIdl, n::Int) -> Bool, NfAbsOrdIdl
    is_power(A::NfOrdFracIdl, n::Int) -> Bool, NfOrdFracIdl

Computes, if possible, an ideal $B$ s.th. $B^n==A$ holds. In this
case, `true` and $B$ are returned.
"""
function is_power(A::NfAbsOrdIdl, n::Int)
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

  fl, ra = is_power(m, n)
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
function is_power(A::NfOrdFracIdl, n::Int)
  nu, de = integral_split(A)
  fl, nu = is_power(nu, n)
  if !fl
    return fl, A
  end
  fl, de = is_power(de, n)
  return fl, nu//de
end

function one(A::NfAbsOrdIdl)
  return ideal(order(A), 1)
end

@doc Markdown.doc"""
    isone(A::NfAbsOrdIdl) -> Bool
    is_unit(A::NfAbsOrdIdl) -> Bool

Tests if $A$ is the trivial ideal generated by $1$.
"""
function isone(I::NfAbsOrdIdl)
  if isdefined(I, :gen_one) && isone(I.gen_one)
    return true
  end
  if isdefined(I, :norm)
    return isone(norm(I, copy = false))
  end
  return isone(minimum(I, copy = false))
end

is_unit(I::NfAbsOrdIdl) = isone(I)

iszero(I::NfAbsOrdIdl) = (I.iszero == 1)

################################################################################
#
#  Reduction of element modulo ideal
#
################################################################################

@doc Markdown.doc"""
    mod(x::NfOrdElem, I::NfAbsOrdIdl)

Returns the unique element $y$ of the ambient order of $x$ with
$x \equiv y \bmod I$ and the following property: If
$a_1,\dotsc,a_d \in \mathbf{Z}_{\geq 1}$ are the diagonal entries of the unique HNF
basis matrix of $I$ and $(b_1,\dotsc,b_d)$ is the coefficient vector of $y$,
then $0 \leq b_i < a_i$ for $1 \leq i \leq d$.
"""
function mod(x::S, y::T) where { S <: Union{NfAbsOrdElem, AlgAssAbsOrdElem}, T <: Union{NfAbsOrdIdl, AlgAssAbsOrdIdl} }
  parent(x) !== order(y) && error("Orders of element and ideal must be equal")
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape

  O = order(y)
  a = coordinates(x)

  if isdefined(y, :princ_gen_special) && y.princ_gen_special[1] != 0
    for i in 1:length(a)
      a[i] = mod(a[i], y.princ_gen_special[1 + y.princ_gen_special[1]])
    end
    return O(a)
  end

  c = integral_basis_matrix_wrt(y, O, copy = false)
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

function mod(x::NfOrdElem, y::NfAbsOrdIdl, preinv::Vector{fmpz_preinvn_struct})
  parent(x) !== order(y) && error("Orders of element and ideal must be equal")
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape

  O = order(y)
  a = coordinates(x) # this is already a copy

  if isdefined(y, :princ_gen_special) && y.princ_gen_special[1] != 0
    for i in 1:length(a)
      a[i] = mod(a[i], y.princ_gen_special[1 + y.princ_gen_special[1]])
    end
    return O(a)
  else
    return mod(x, basis_matrix(y, copy = false), preinv)
  end
end

function mod(x::Union{NfOrdElem, AlgAssAbsOrdElem}, c::Union{fmpz_mat, Matrix{fmpz}}, preinv::Vector{fmpz_preinvn_struct})
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape

  O = parent(x)
  a = coordinates(x) # this is already a copy

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

function mod!(x::NfOrdElem, c::Union{fmpz_mat, Matrix{fmpz}}, preinv::Vector{fmpz_preinvn_struct})
  # this function assumes that HNF is lower left
  # !!! This must be changed as soon as HNF has a different shape

  O = parent(x)
  a = coordinates(x, copy = false) # this is already a copy

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

function mod!(x::AlgAssAbsOrdElem, c::Union{fmpz_mat, Matrix{fmpz}}, preinv::Vector{fmpz_preinvn_struct})

  O = parent(x)
  a = coordinates(x, copy = false)

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
  # We need to adjust the underlying algebra element
  t = algebra(O)()
  B = O.basis_alg
  x.elem_in_algebra = zero!(elem_in_algebra(x, copy = false))
  for i in 1:degree(O)
    t = mul!(t, B[i], a[i])
    x.elem_in_algebra = add!(elem_in_algebra(x, copy = false), elem_in_algebra(x, copy = false), t)
  end

  return x
end

function mod(x::Union{NfOrdElem, AlgAssAbsOrdElem}, Q::AbsOrdQuoRing)
  O = parent(x)

  y = ideal(Q)
  if isdefined(y, :princ_gen_special) && y.princ_gen_special[1] != 0
    a = coordinates(x) # this is already a copy
    for i in 1:length(a)
      a[i] = mod(a[i], y.princ_gen_special[1 + y.princ_gen_special[1]])
    end
    return O(a)
  end

  return mod(x, Q.basis_mat_array, Q.preinvn)
end

function mod!(x::Union{NfOrdElem, AlgAssAbsOrdElem}, Q::AbsOrdQuoRing)
  O = parent(x)
  y = ideal(Q)

  if isdefined(y, :princ_gen_special) && y.princ_gen_special[1] != 0
    a = coordinates(x, copy = false) # this is already a copy
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

function mod(x::FacElem{S, T}, Q::AbsOrdQuoRing{NfAbsOrd{T, S}, NfAbsOrdIdl{T, S}}) where { S, T }
  O = base_ring(Q)
  K = nf(O)
  D = Dict{elem_type(O), fmpz}()
  # First step: Make all factors integral
  for (b, e) in x.fac
    d = denominator(b, O)
    b = O(d*b)
    if haskey(D, b)
      D[b] += e
    else
      D[b] = e
    end
    if isone(d)
      continue
    end
    Od = O(d)
    if haskey(D, Od)
      D[Od] -= e
    else
      D[Od] = -e
    end
  end
  bases = Vector{elem_type(O)}()
  exps = Vector{fmpz}()
  for (b, e) in D
    push!(bases, b)
    push!(exps, e)
  end

  # Second step: Make sure everything has non-negative valuation at primes
  # dividing ideal(Q)
  primes = collect(keys(factor(Q)))
  vals = zeros(Int, length(primes))
  for i = 1:length(primes)
    p = primes[i]
    val_elt = one(K) # Going to be an element with valuation -1 at p and valuation
                     # 0 at all other elements of primes. I only want to compute
                     # it, if it is needed.
    val_elt_computed = false
    # Find the factors with non-zero valuation at p and negative exponent
    n = fmpz(0) # Counts how often we multiplied by val_elt
    for j = 1:length(bases)
      if exps[j] >= 0
        continue
      end
      v = valuation(bases[j], p)
      if iszero(v)
        continue
      end
      if !val_elt_computed
        vals[i] = -1
        val_elt = approximate(vals, primes)
        vals[i] = 0
        val_elt_computed = true
      end
      b = bases[j]*val_elt^v
      bases[j] = O(b)
      n -= v*exps[j]
    end
    if iszero(n)
      continue
    end
    # Multiply the factors with non-zero valuation at p and positive exponent
    # by val_elt to compensate for the ones we multiplied above.
    for j = 1:length(bases)
      if exps[j] <= 0
        continue
      end
      v = valuation(bases[j], p)
      if iszero(v)
        continue
      end
      n2 = n - v*exps[j]
      if n2 >= 0
        b = bases[j]*val_elt^v
        bases[j] = O(b)
        n = n2
        if n == 0
          break
        end
      else
        q, r = divrem(n, exps[j])
        @assert q < v
        b = bases[j]
        push!(bases, O(b*val_elt^q))
        push!(exps, exps[j] - r)
        bases[j] = O(b*val_elt^(q + 1))
        exps[j] = r
        n = 0
        break
      end
    end
    @assert n == 0 "Element not integral"
  end

  # Now we can evaluate (modulo ideal(Q) of course)
  z = one(Q)
  for i = 1:length(bases)
    z *= Q(bases[i])^exps[i]
  end
  return z
end

################################################################################
#
#  p-radical
#
################################################################################

function pradical_trace(O::NfAbsOrd, p::IntegerUnion)
  d = degree(O)
  M = trace_matrix(O)
  F = GF(p, cached = false)
  M1 = map_entries(F, M)
  k, B = nullspace(M1)
  if iszero(k)
    return ideal(O, p)
  end
  M2 = zero_matrix(FlintZZ, d, d)
  for i = 1:ncols(B)
    for j = 1:d
      M2[i, j] = FlintZZ(B[j, i].data)
    end
  end
  gens = elem_type(O)[O(p)]
  for i=1:ncols(B)
    if !is_zero_row(M2,i)
      push!(gens, elem_from_mat_row(O, M2, i))
    end
  end
  M2 = hnf_modular_eldiv!(M2, fmpz(p), :lowerleft)
  I = ideal(O, M2)
  I.minimum = p
  I.gens = gens
  return I
end

function pradical_frobenius(O::NfAbsOrd, p::IntegerUnion)

  #First, I need an exponent for the maximum of the nilpotency indices.
  R = GF(p, cached = false)
  d = degree(O)
  K = nf(O)
  j = clog(fmpz(d), p)
  @assert p^(j-1) < d
  @assert d <= p^j

  A = zero_matrix(R, degree(O), degree(O))
  B = basis(O, copy = false)
  for i in 1:d
    t = powermod(B[i], p^j, p)
    if iszero(t)
      continue
    end
    ar = coordinates(t)
    for k in 1:d
      A[k, i] = ar[k]
    end
  end
  X = right_kernel_basis(A)
  gens = elem_type(O)[O(p)]
  if isempty(X)
    I = ideal(O, p)
    I.gens = gens
    return I
  end
  #First, find the generators
  for i = 1:length(X)
    coords = Vector{fmpz}(undef, d)
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
  mm = hnf_modular_eldiv!(m, fmpz(p), :lowerleft)
  I = NfAbsOrdIdl(O, mm)
  I.minimum = p
  I.gens = gens
  return I
end

@doc Markdown.doc"""
    pradical(O::NfOrd, p::{fmpz|Integer}) -> NfAbsOrdIdl

Given a prime number $p$, this function returns the $p$-radical
$\sqrt{p\mathcal O}$ of $\mathcal O$, which is
just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
\in p\mathcal O \}$. It is not checked that $p$ is prime.
"""
function pradical(O::NfAbsOrd, p::IntegerUnion)
  if p isa fmpz
    if fits(Int, p)
      return pradical(O, Int(p))
    end
  end
  #Trace method if the prime is large enough
  if p > degree(O)
    return pradical_trace(O, p)
  else
    return pradical_frobenius(O, p)
  end
end

################################################################################
#
#  Colon, conductor: it's the same(?) method
#
################################################################################

@doc Markdown.doc"""
    colon(a::NfAbsOrdIdl, b::NfAbsOrdIdl) -> NfOrdFracIdl

The ideal $(a:b) = \{x \in K | xb \subseteq a\} = \hom(b, a)$
where $K$ is the number field.
"""
function colon(a::NfAbsOrdIdl, b::NfAbsOrdIdl, contains::Bool = false)

  O = order(a)
  n = degree(O)
  if isdefined(b, :gens)
    B = b.gens
  else
    B = basis(b)
  end

  bmatinv = basis_mat_inv(a, copy = false)

  if contains
    m = zero_matrix(FlintZZ, n*length(B), n)
    id_gen = zero_matrix(FlintZZ, 2*n, n)
    ind = 1
    modu = minimum(a)*bmatinv.den
    for i = 1:length(B)
      if i != 1
        c = matrix(FlintZZ, 1, n, coordinates(B[i]))
        reduce_mod_hnf_ll!(c, id_gen)
        if iszero(c)
          continue
        end
      end
      M = representation_matrix_mod(B[i], modu)
      _copy_matrix_into_matrix(id_gen, 1, 1, M)
      hnf_modular_eldiv!(id_gen, minimum(a), :lowerleft)
      mod!(M, minimum(a)*bmatinv.den)
      mul!(M, M, bmatinv.num)
      M = transpose(M)
      _copy_matrix_into_matrix(m, n*(ind-1)+1, 1, M)
      if view(id_gen, n+1:2*n, 1:n) == basis_matrix(a, copy = false)
        m = view(m, 1:n*ind, 1:n)
        break
      end
      ind += 1
    end
    if !isone(bmatinv.den)
      divexact!(m, m, bmatinv.den)
    end
    hnf_modular_eldiv!(m, minimum(a))
    m = transpose(view(m, 1:n, 1:n))
    b, l = pseudo_inv(m)
    return NfAbsOrdIdl(O, b)//l
  else
    n = representation_matrix(B[1])*bmatinv
    m = numerator(n)
    d = denominator(n)
    for i in 2:length(B)
      n = representation_matrix(B[i])*bmatinv
      mm = n.num
      dd = n.den
      l = lcm(dd, d)
      if l == d && l == dd
        m = hcat(m, mm)
      elseif l == d
        m = hcat(m, div(d, dd)*mm)
      elseif l == dd
        m = hcat(div(dd, d)*m, mm)
        d = dd
      else
        m = hcat(m*div(l, d), mm*div(l, dd))
        d = l
      end
    end
    m = transpose(m)
    hnf!(m)
    # m is upper right HNF
    m = transpose(sub(m, 1:degree(O), 1:degree(O)))
    b = inv(FakeFmpqMat(m, d))
    return fractional_ideal(O, b)
  end
end

################################################################################
#
#  Conversion to different order
#
################################################################################

@doc Markdown.doc"""
    fractional_ideal(O::NfOrd, I::NfAbsOrdIdl) -> NfOrdFracIdl

The fractional ideal of $O$ generated by a $Z$-basis of $I$.
"""
function fractional_ideal(O::NfOrd, I::NfAbsOrdIdl)
  k = nf(O)
  bI = basis(I)
  J = ideal(O, k(bI[1]))
  for j=2:degree(O)
    J += ideal(O, k(bI[j]))
  end
  return J
end


function random_init(I::AbstractVector{T}; reduce::Bool = true, ub::fmpz=fmpz(0), lb::fmpz=fmpz(1)) where {T}

  R = RandIdlCtx()
  R.base = collect(I)
  O = order(R.base[1])
  R.ibase = map(inv, R.base)
  R.exp = zeros(Int, length(R.base))
  R.lb = lb
  R.ub = ub
  R.last = Set{Vector{Int}}()
  R.rand = ideal(O, 1)
  while norm(R.rand) <= lb
    i = rand(1:length(R.base))
    R.rand = simplify(R.rand * R.base[i])
    R.exp[i] += 1
  end
  push!(R.last, copy(R.exp))
  return R
end

function random_extend(R::RandIdlCtx, I::T) where {T <:AbstractVector{NfOrdIdl}}
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
  end
  push!(R.last, copy(R.exp))
  return R.rand
end



################################################################################
#
#  Conversion to Magma
#
################################################################################

function to_magma(f::IOStream, clg::NfOrdIdl, order::String = "M")
  print(f, "ideal<$(order)| ", clg.gen_one, ", ",
                    elem_in_nf(clg.gen_two), ">")
end

function to_magma(s::String, c::NfOrdIdl, order::String = "M")
  f = open(s, "w")
  to_magma(f, c, order)
  close(f)
end

###################################################################################
#
#  Coprimality between ideals
#
###################################################################################


@doc Markdown.doc"""
    iscoprime(I::NfAbsOrdIdl, J::NfAbsOrdIdl) -> Bool

Test if ideals $I,J$ are coprime.
"""
function iscoprime(I::NfAbsOrdIdl, J::NfAbsOrdIdl)
  @assert order(I) === order(J)
  if isdefined(I, :norm) && isdefined(J, :norm)
    if isone(gcd(norm(I, copy = false), norm(J, copy = false)))
      return true
    end
  end
  if isdefined(I, :gen_one) && isdefined(J, :gen_one)
    if isone(gcd(I.gen_one, J.gen_one))
      return true
    end
  end
  if gcd(minimum(I, copy = false), minimum(J, copy = false)) == 1
    return true
  end
  if isprime_known(I) && is_prime(I)
    return iszero(valuation(J, I))
  end
  if isprime_known(J) && is_prime(J)
    return iszero(valuation(I, J))
  end
  #Lemma: Let R be a (commutative) artinian ring, let I be an ideal of R and
  #let x be a nilpotent element. Then I = 1 if and only if I + x = 1
  m = gcd(minimum(I, copy = false), minimum(J, copy = false))
  m = is_power(m)[2]
  if has_2_elem(I) && has_2_elem(J)
    K = nf(order(I))
    if gcd(m, index(order(I))) == 1
      if fits(Int, m)
        RI = ResidueRing(FlintZZ, Int(m), cached = false)
        RIx = PolynomialRing(RI, "x", cached = false)[1]
        fI1 = RIx(I.gen_two.elem_in_nf)
        fI2 = RIx(J.gen_two.elem_in_nf)
        fI3 = RIx(K.pol)
        fl = _coprimality_test(fI1, fI2, fI3)
      else
        R = ResidueRing(FlintZZ, m, cached = false)
        Rx = PolynomialRing(R, "x", cached = false)[1]
        f1 = Rx(I.gen_two.elem_in_nf)
        f2 = Rx(J.gen_two.elem_in_nf)
        f3 = Rx(K.pol)
        fl = _coprimality_test(f1, f2, f3)
      end
      @hassert :NfOrd 1 fl == isone(I+J)
      return fl
    end
  end
  return isone(gcd(I, m)+J)
end

function iscoprime(I::NfAbsOrdIdl, a::fmpz)
  return iscoprime(minimum(I, copy = false), a)
end

one(I::NfAbsOrdIdlSet) = ideal(order(I), 1)

###############################################################################
#
#  Extending an ideal
#
###############################################################################

function (I_Zk::NfOrdIdlSet)(a::NfOrdIdl)
  if parent(a) === I_Zk
    return a
  end
  Zk = order(I_Zk)
  Zl = order(a)
  @assert ismaximal_known_and_maximal(Zk)

  has_2_elem(a) || _assure_weakly_normal_presentation(a)
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
  if isdefined(a, :is_prime) && Zk.nf == Zl.nf && Zk.ismaximal == 1 &&
    Zl.ismaximal == 1
    b.is_prime = a.is_prime
    if isdefined(a, :splitting_type)
      b.splitting_type = a.splitting_type
    end
  end
  return b
end

#############################################################################
@doc Markdown.doc"""
    euler_phi(A::NfOrdIdl) -> fmpz

The ideal version of the totient function returns the size of the unit group
of the residue ring modulo the ideal.
"""
Hecke.euler_phi(A::NfOrdIdl) = Hecke.euler_phi(factor(A))
Hecke.euler_phi(A::FacElem{NfOrdIdl}) = Hecke.euler_phi(factor(A))
function Hecke.euler_phi(A::Dict{NfOrdIdl, Int})
  return prod((norm(p)-1)*norm(p)^(k-1) for (p,k) = A if k > 0 || error("Ideal not integral"))
end

#basically from
#http://people.math.gatech.edu/~ecroot/shparlinski_final.pdf
#Contini, Croot, Shparlinski: Complexity of inverting the Euler function
@doc Markdown.doc"""
    euler_phi_inv_fac_elem(n::fmpz, zk::NfAbsOrd{AnticNumberField, nf_elem})

The inverse of the ideal totient function: all ideals $A$ s.th. the unit group of the
residue ring has the required size. Here, the ideals are returned in factorised form.
"""
function euler_phi_inv_fac_elem(n::fmpz, zk::NfAbsOrd{AnticNumberField, nf_elem})
  lp = []
  for d = Divisors(n)
    k, p = is_power(d+1)
    if is_prime(p)
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
    euler_phi_inv(n::fmpz, zk::NfAbsOrd{AnticNumberField, nf_elem}) -> Vector{NfOrdIdl}

The inverse of the ideal totient function: all ideals $A$ s.th. the unit group of the
residue ring has the required size.
"""
euler_phi_inv(n::fmpz, zk::NfAbsOrd) = [ numerator(evaluate(x)) for x = euler_phi_inv_fac_elem(n, zk)]
euler_phi_inv(n::Integer, zk::NfAbsOrd) = [ numerator(evaluate(x)) for x = euler_phi_inv_fac_elem(fmpz(n), zk)]

################################################################################
#
#  Ideals with bounded norm
#
################################################################################

function _squarefree_ideals_with_bounded_norm(O::NfAbsOrd, lp::Vector{NfOrdIdl}, bound::fmpz)
  #@assert issorted(lp, by = x -> norm(x))
  lf = Vector{Tuple{NfOrdIdl, fmpz}}()
  for P in lp
    push!(lf, (P, norm(P)))
  end
  #Now, I have to merge them.
  conds = Vector{Tuple{Dict{NfOrdIdl, Int}, fmpz}}()
  push!(conds, (Dict{NfOrdIdl, Int}(), fmpz(1)))
  if isempty(lf)
    return conds
  end
  for i = 1:length(lf)
    P = lf[i][1]
    dP = lf[i][2]
    indj = length(conds)
    new_conds = Vector{Tuple{Dict{NfOrdIdl, Int}, fmpz}}()
    for j = 1:indj
      Dd = dP*conds[j][2]
      if Dd > bound
        break
      end
      D = copy(conds[j][1])
      D[P] = 1
      push!(new_conds, (D, Dd))
      #push!(conds, (D, Dd))
    end
    for j = 1:length(new_conds)
      insert!(conds, searchsortedfirst(conds, new_conds[j], by = x -> x[2]), new_conds[j])
    end
    #sort!(conds, by = x -> x[2])
  end
  return conds
end

function _squarefree_ideals_with_bounded_norm(O::NfAbsOrd, bound::fmpz; coprime::fmpz = fmpz(0))
  lp = prime_ideals_up_to(O, Int(bound))
  if !iszero(coprime)
    filter!(x -> iscoprime(norm(x), coprime), lp)
  end
  return _squarefree_ideals_with_bounded_norm(O, lp, bound)
end
