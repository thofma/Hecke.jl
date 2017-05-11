################################################################################
#
#          NfOrd/Ideal.jl : Ideals of orders of number fields
#
# This file is part of hecke.
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
#  Copyright (C) 2015, 2016 Tommy Hofmann
#
################################################################################

export NfOrdGenIdl

export deepcopy, parent, order, basis, basis_mat, basis_mat_inv, minimum, norm,
       ==, in, +, *, intersection, lcm, idempotents, mod, pradical

################################################################################
#
#  Hashing
#
################################################################################

# a (bad) hash function
# - slow (due to basis)
# - unless basis matrix is in HNF it is also non-unique
function hash(A::NfOrdIdl)
  return hash(basis_mat(A))
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
      if i == :basis
        setfield!(B, i, NfOrdElem{typeof(order(A))}[ deepcopy(x) for x in A.basis])
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

################################################################################
#
#  Order
#
################################################################################

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
#  Basis
#
################################################################################

doc"""
***
    basis(I::NfOrdIdl) -> Array{NfOrdElem, 1}

> Returns the $\mathbf Z$-basis of $I$.
"""
function basis(a::NfOrdIdl)
  O = order(a)
  if isdefined(a, :basis)
    return a.basis
  end
  B = Array{elem_type(O)}(degree(order(a)))
  for i in 1:degree(O)
    t = zero(O)
    v = Array{fmpz}(degree(O))
    for j in 1:degree(O)
      t += basis(O)[j]*basis_mat(a)[i,j]
      #v[j] = basis_mat(a)[i,j]
    end
    B[i] = t
    #B[i].elem_in_basis = v
  end
  a.basis = B
  return elem_type(O)[ deepcopy(b) for b in a.basis]
end

################################################################################
#
#  (Inverse) basis matrix
#
################################################################################

doc"""
***
    basis_mat(I::NfOrdIdl) -> fmpz_mat

> Returns the basis matrix of $I$ with respect to the basis of the order.
"""
function basis_mat(a::NfOrdIdl)
  return deepcopy(a.basis_mat)
end

doc"""
***
    basis_mat_inv(I::NfOrdIdl) -> FakeFmpqMat

> Returns the inverse of the basis matrix of $I$.
"""
function basis_mat_inv(a::NfOrdGenIdl)
  if isdefined(a, :basis_mat_inv)
    return deepcopy(a.basis_mat_inv)
  else
    m,d = pseudo_inv(a.basis_mat)
    a.basis_mat_inv = FakeFmpqMat(m,d)
    return deepcopy(a.basis_mat_inv)
  end
end

################################################################################
#
#  Minimum
#
################################################################################

doc"""
***
    minimum(I::NfOrdIdl) -> fmpz

> Returns the minimum of $I$, that is, the minimum of
> $I \cap \mathbf Z_{\geq 0}$, where $\mathcal O$ is the order of $I$.
"""
function minimum(a::NfOrdIdl)
  if isdefined(a, :minimum)
    return deepcopy(a.minimum)
  else
    @hassert :NfOrd 2 isone(basis(order(a))[1])
    a.minimum = basis_mat(a)[1, 1]
    return deepcopy(a.minimum)
  end
end

################################################################################
#
#  Norm
#
################################################################################

doc"""
***
    norm(I::NfOrdIdl) -> fmpz

> Returns the norm of $I$, that is, the cardinality of $\mathcal O/I$, where
> $\mathcal O$ is the order of $I$.
"""
function norm(a::NfOrdIdl)
  if isdefined(a, :norm)
    return deepcopy(a.norm)
  else
    a.norm = det(basis_mat(a))
    return deepcopy(a.norm)
  end
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
  return _mul(x, y)
end

function _mul(x::NfOrdIdl, y::NfOrdIdl)
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

################################################################################
#
#  Ad hoc binary operations
#
################################################################################

function *(x::NfOrdElem, y::NfOrdIdl)
  parent(x) != order(y) && error("Orders of element and ideal must be equal")
  return ideal(parent(x), x) * y
end

*(x::NfOrdIdl, y::NfOrdElem) = y * x

function *(x::NfOrdIdl, y::fmpz)
  z = ideal(order(x), basis_mat(x)*y)
  if isdefined(x, :princ_gen)
    z.princ_gen = x.princ_gen * y
  end
  if isdefined(x, :princ_gen_special)
    z.princ_gen_special = (2, 0, x.princ_gen_special[x.princ_gen_special[1] + 1] * y)
  end
  return z
end

*(x::fmpz, y::NfOrdIdl) = y * x

*(x::NfOrdIdl, y::Integer) = x * fmpz(y)

*(x::Integer, y::NfOrdIdl) = y * x

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

doc"""
***
    pradical(O::NfOrd, p::fmpz) -> NfOrdIdl

> Given a prime number $p$, this function returns the $p$-radical
> $\sqrt{p\mathcal O}$ of $\mathcal O$, which is 
> just $\{ x \in \mathcal O \mid \exists k \in \mathbf Z_{\geq 0} \colon x^k
> \in p\mathcal O \}$. It is not checked that $p$ is prime.
"""
function pradical(O::NfOrd, p::fmpz)
  j = clog(fmpz(degree(O)),p)

  @assert p^(j-1) < degree(O)
  @assert degree(O) <= p^j

  R = ResidueRing(ZZ,p)
  A = MatrixSpace(R, degree(O), degree(O))()
  for i in 1:degree(O)
    t = powermod(basis(O)[i], p^j, p)
    ar = elem_in_basis(t)
    for k in 1:degree(O)
      A[i,k] = ar[k]
    end
  end
  X = kernel(A)
  Mat = MatrixSpace(ZZ, 1, degree(O))
  MMat = MatrixSpace(R, 1, degree(O))
  if length(X) != 0
    m = lift(MMat(X[1]))
    for x in 2:length(X)
      m = vcat(m,lift(MMat(X[x])))
    end
    m = vcat(m,MatrixSpace(ZZ, degree(O), degree(O))(p))
  else
    m = MatrixSpace(ZZ, degree(O), degree(O))(p)
  end
  r = sub(_hnf(m, :lowerleft), rows(m) - degree(O) + 1:rows(m), 1:degree(O))
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
    ring_of_multipliers(I::NfOrdIdl) -> NfOrdGen

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


