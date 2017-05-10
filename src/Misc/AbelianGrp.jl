################################################################################
#
#             GrpAb.jl : Finitely generated abelian groups
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
#  Copyright (C) 2015, 2016 Tommy Hofmann, Claus Fieker
#
################################################################################

export FinGenGrpAb, FinGenGrpAbElem, parent, isfinite, isinfinite, rank,
       getindex, show, +, *, ngens, snf_with_transform, nrels,
       -, ==, istrivial, order, exponent, AbelianGroup, DiagonalGroup,
       quo, sub, rels, hasimage, haspreimage

import Base.+, Nemo.snf, Nemo.parent, Base.rand


################################################################################
#
#  Parent and element types IO, types are in HeckeTypes
#
################################################################################

function show(io::IO, A::FinGenGrpAbGen)
  print(io, "(General) abelian group with relation matrix\n$(A.rels)")
  if isdefined(A, :snf_map)
    println(io, "\nwith structure of ", codomain(A.snf_map))
  end
end

function show(io::IO, A::FinGenGrpAbSnf)
  len = length(A.snf)

  println(io, "Abelian group")

  if len == 0
    print(io, "Z/1")
    return
  end

  if A.snf[1] == 0
    if len == 1
      print(io, "Z")
    else
      print(io, "Z^$(len)")
    end
    return
  end

  print(io, "Z/$(A.snf[1])")
  i = 2
  while i <= len && A.snf[i] != 0
    print(io, " x Z/$(A.snf[i])")
    i += 1
  end
  if i == len
    print(io, " x Z")
  elseif i < len
    print(io, " x Z^$(len-i+1)")
  end
end

function show(io::IO, a::FinGenGrpAbElem)
  print(io, "Element of\n$(a.parent)\n with components\n$(a.coeff)")
end

################################################################################
#
#  Field access
#
################################################################################

doc"""
***
    parent(x::FinGenGrpAbElem ) -> FinGenGrpAb

> Returns the parent of $x$.
"""
function parent(x::FinGenGrpAbElem)
  return x.parent
end

doc"""
***
    ngens(G::FinGenGrpAbSnf ) -> Int

> Returns the number of generators of G in the current representation.
"""
function ngens(A::FinGenGrpAbGen)
  return cols(A.rels)
end

function ngens(A::FinGenGrpAbSnf)
  return length(A.snf)
end

doc"""
***
    nrels(G::FinGenGrpAb) -> Int

> Returns the number of relations of G in the current representation.
"""
function nrels(A::FinGenGrpAbGen)
  return rows(A.rels)
end

function nrels(A::FinGenGrpAbSnf)
  return length(A.snf)
end

doc"""
***
    getindex(x::FinGenGrpAbElem, i::Int) -> fmpz

> Returns the $i$-th component of the element $x$.
"""
function getindex(x::FinGenGrpAbElem, i::Int)
  return x.coeff[1,i]
end

doc"""
***
    rels(A::FinGenGrpAb) -> fmpz_mat
> The currently used relations as a single matrix.
"""
function rels(A::Hecke.FinGenGrpAbGen)
  return A.rels
end

function rels(A::Hecke.FinGenGrpAbSnf)
  M = MatrixSpace(FlintZZ, ngens(A), ngens(A))()
  for i=1:ngens(A)
    M[i,i] = A.snf[i]
  end
  return M
end

################################################################################
# Map support 
#TODO: put elsewhere and make generic
################################################################################
function haspreimage{S, T}(M::Hecke.FinGenGrpAbMap{S, T}, a::Hecke.FinGenGrpAbElem{T})
  if isdefined(M, :imap)
    return preimage(M, a)
  end

  m = vcat(M.map, rels(codomain(M)))
  fl, p = cansolve(m', a.coeff')
  if fl
    return true, domain(M)(sub(p', 1:1, 1:ngens(domain(M))))
  else
    return false, domain(M)[1]
  end
end

function hasimage{S, T}(M::Hecke.FinGenGrpAbMap{S, T}, a::Hecke.FinGenGrpAbElem{S})
  if isdefined(M, :map)
    return image(M, a)
  end
  m = vcat(M.imap, rels(domain(M)))
  fl, p = cansolve(m, a.coeff)
  if fl
    return true, codomain(M)(sub(p, 1:1, 1:ngens(codomain(M))))
  else
    return false, codomain(M)[1]
  end
end

################################################################################
################################################################################
################################################################################
function assert_hnf(A::FinGenGrpAbGen)
  isdefined(A, :hnf) && return
  A.hnf = hnf(A.rels)
end

function reduce_mod_hnf!(a::fmpz_mat, H::fmpz_mat)
  j = 1
  for i=1:min(rows(H), cols(H))
    while j <= cols(H) && H[i,j] == 0
      j+=1
    end
    if j > cols(H)
      return
    end
    q = fdiv(a[1, j], H[i,j])
    for k=j:cols(a)
      a[1,k] =  a[1, k] -q*H[i,k]
    end
  end
end

function FinGenGrpAbElemCreate(A::FinGenGrpAbGen, a::fmpz_mat)
  assert_hnf(A::FinGenGrpAbGen)
  reduce_mod_hnf!(a, A.hnf)
  return FinGenGrpAbElem{FinGenGrpAbGen}(A, a)
  # reduce mod hnf
end

function FinGenGrpAbElemCreate(A::FinGenGrpAbSnf, a::fmpz_mat)
  for i=1:ngens(A)
    if A.snf[i] != 0
      a[1,i] = mod(a[1,i], A.snf[i])
    end
  end
  return FinGenGrpAbElem{FinGenGrpAbSnf}(A, a)
end
################################################################################
#
# Arithmetic
#
################################################################################

function ==(a::FinGenGrpAbElem, b::FinGenGrpAbElem)
  a.parent == b.parent || error("elements must belong to the same group")
  return a.coeff == b.coeff
end

doc"""
***
    +(x::FinGenGrpAbElem, y::FinGenGrpAbElem) -> FinGenGrpAbElem

> Computes $x + y$.
"""
function +(x::FinGenGrpAbElem, y::FinGenGrpAbElem)
  x.parent == y.parent || error("elements must belong to the same group")
  n = FinGenGrpAbElemCreate(x.parent, x.coeff + y.coeff)
  return n
end

doc"""
***
    -(x::FinGenGrpAbElem, y::FinGenGrpAbElem) -> FinGenGrpAbElem

> Computes $x - y$.
"""
function -(x::FinGenGrpAbElem, y::FinGenGrpAbElem)
  x.parent == y.parent || error("elements must belong to the same group")
  n = FinGenGrpAbElemCreate(x.parent, x.coeff - y.coeff)
  return n
end

doc"""
***
    -(x::FinGenGrpAbElem) -> FinGenGrpAbElem

> Computes $-x$.
"""
function -(x::FinGenGrpAbElem)
  n = FinGenGrpAbElemCreate(x.parent, -x.coeff)
  return n
end

doc"""
***
    *(x::fmpz, y::FinGenGrpAbElem) -> FinGenGrpAbElem

> Computes $x \cdot y$.
"""
function *(x::fmpz, y::FinGenGrpAbElem)
  n = x*y.coeff
  return FinGenGrpAbElemCreate(y.parent, n)
end

doc"""
***
    *(x::Integer, y::FinGenGrpAbElem) -> FinGenGrpAbElem

> Computes $x \cdot y$.
"""
function *(x::Integer, y::FinGenGrpAbElem)
  n = x*y.coeff
  return FinGenGrpAbElemCreate(y.parent, n)
end

################################################################################
#
#  Parent object overloading
#
################################################################################

doc"""
***
    (A::FinGenGrpAbSnf)(x::Array{fmpz, 1}) -> FinGenGrpAbElem

> Given an array of elements of type `fmpz` of the same length as ngens($A$),
> this function returns the element of $A$ with components `x`.
"""
function (A::FinGenGrpAbSnf)(x::Array{fmpz, 1})
  ngens(A) != length(x) && error("Lengths do not coincide")
  y = MatrixSpace(ZZ, 1, ngens(A))(x)
  z = FinGenGrpAbElemCreate(A, y)
  return z
end

doc"""
***
    (A::FinGenGrpAbSnf)(x::Array{Integer, 1}) -> FinGenGrpAbElem

> Given an array of elements of type `Integer` of the same length as ngens($A$),
> this function returns the element of $A$ with components `x`.
"""
function (A::FinGenGrpAbSnf){T <: Integer}(x::Array{T, 1})
  ngens(A) != length(x) && error("Lengths do not coincide")
  z = A(map(fmpz, x))
  return z
end

doc"""
***
    (A::FinGenGrpAbSnf)(x::fmpz_mat) -> FinGenGrpAbElem

> Given a 1 x ngens(A) fmpz_mat,
> this function returns the element of $A$ with components `x`.
"""
function (A::FinGenGrpAbSnf)(x::fmpz_mat)
  ngens(A) != cols(x) && error("Lengths do not coincide")
  rows(x) != 1 && error("Matrix should have only one row")
  z = FinGenGrpAbElemCreate(A, x)
  return z
end

doc"""
***
    (A::FinGenGrpAbGen)(x::Array{fmpz, 1}) -> FinGenGrpAbElem

> Given an array of elements of type `fmpz` of the same length as ngens($A$),
> this function returns the element of $A$ with components `x`.
"""
function (A::FinGenGrpAbGen)(x::Array{fmpz, 1})
  ngens(A) != length(x) && error("Lengths do not coincide")
  y = MatrixSpace(ZZ, 1, ngens(A))(x)
  z = FinGenGrpAbElemCreate(A, y)
  return z
end

doc"""
***
    (A::FinGenGrpAbGen, x::Array{Integer, 1}) -> FinGenGrpAbElem

> Given an array of elements of type `Integer` of the same length as ngens($A$),
> this function returns the element of $A$ with components `x`.
"""
function (A::FinGenGrpAbGen){T <: Integer}(x::Array{T, 1})
  ngens(A) != length(x) && error("Lengths do not coincide")
  z = A(map(fmpz, x))
  return z
end

doc"""
***
    (A::FinGenGrpAbGen)(x::fmpz_mat) -> FinGenGrpAbElem

> Given a 1 x ngens(A) fmpz_mat,
> this function returns the element of $A$ with components `x`.
"""
function (A::FinGenGrpAbGen)(x::fmpz_mat)
  ngens(A) != cols(x) && error("Lengths do not coincide")
  rows(x) != 1 && error("Matrix should have only one row")
  z = FinGenGrpAbElemCreate(A, x)
  return z
end


doc"""
***
    getindex(A::FinGenGrpAbSnf, i::Int) -> FinGenGrpAbElem

> Returns the element of $A$ with components $(0,\dotsc,0,1,0,\dotsc,0)$,
> where the $1$ is at the $i$-th position.
"""
function getindex(A::FinGenGrpAb, i::Int)
  (i<1 || i > ngens(A)) && error("Index out of range")
  z = MatrixSpace(ZZ, 1, ngens(A))()
  for j in 1:ngens(A)
    z[1,j] = fmpz()
  end
  z[1,i] = fmpz(1)
  return A(z)
end

elem_type(G::FinGenGrpAbSnf) = FinGenGrpAbElem{FinGenGrpAbSnf}
elem_type(G::FinGenGrpAbGen) = FinGenGrpAbElem{FinGenGrpAbGen}
elem_type(::Type{FinGenGrpAbGen}) = FinGenGrpAbElem{FinGenGrpAbGen}
elem_type(::Type{FinGenGrpAbSnf}) = FinGenGrpAbElem{FinGenGrpAbSnf}
elem_type(::Type{FinGenGrpAb}) = FinGenGrpAbElem # I have no idea what this
                                    # does, but it appears to be important
                                    # U, m = UnitGroup(ResidueRing(ZZ, 2^10))
                                    # m(U[2])
                                    # preimage(m, ans)
                                    # fails without...

doc"""
***
  snf(A::FinGenGrpAbSnf) -> FinGenGrpAb, Map

> Given some abelian group, return the "same" group in canonical form,
> i.e. as the direct product of cyclic groups with dividing orders.
> The second return value is the map to translate between the new and old
> groups.
"""
function snf(G::FinGenGrpAbSnf)
  return G, IdentityMap(G)
end

doc"""
***
  isdiag(A::fmpz_mat)

> Tests if A is diagonal.
"""
function isdiag(A::fmpz_mat)
  for i = 1:cols(A)
    for j= 1:rows(A)
      if i != j && A[j,i]!=0
        return false
      end
    end
  end
  return true
end

#=
g, e,f = gcdx(a, b)
U = [1 0 ; -divexact(b, g)*f 1]*[1 1; 0 1];
V = [e -divexact(b, g) ; f divexact(a, g)];

then U*[ a 0; 0 b] * V = [g 0 ; 0 l]
=#
doc"""
***
  snf_with_transform(A::fmpz_mat; l::Bool = true, r::Bool = true) -> fmpz_mat [, fmpz_mat [, fmpz_mat]]

> Given some integer matrix A, compute the Smith normal form (elementary
> divisor normal form) of A. If l and/ or r are true, then the corresponding
> left and/ or right transformation matrices are computed as well.
"""
function snf_with_transform(A::fmpz_mat; l::Bool = true, r::Bool = true)
  if r
    R = MatrixSpace(ZZ, cols(A), cols(A))(1)
  end

  if l
    L = MatrixSpace(ZZ, rows(A), rows(A))(1)
  end
  # TODO: if only one trafo is required, start with the HNF that does not
  #       compute the trafo
  #       Rationale: most of the work is on the 1st HNF..
  #
  S = deepcopy(A)
  while !isdiag(S)
    if l
      S, T = hnf_with_transform(S)
      L = T*L
    else
      S = hnf(S)
    end

    if isdiag(S)
      break
    end
    if r
      S, T = hnf_with_transform(S')
      R = T*R
    else
      S = hnf(S')
    end
    S = S'
  end
  #this is probably not really optimal...
  for i=1:min(rows(S), cols(S))
    if S[i,i] == 1
      continue
    end
    for j=i+1:min(rows(S), cols(S))
      if S[j,j] == 0
        continue
      end
      if S[i,i] != 0 && S[j,j] % S[i,i] == 0
        continue
      end
      g, e,f = gcdx(S[i,i], S[j,j])
      a = divexact(S[i,i], g)
      S[i,i] = g
      b = divexact(S[j,j], g)
      S[j,j] *= a
      if l
        # U = [1 0; -b*f 1] * [ 1 1; 0 1] = [1 1; -b*f -b*f+1]
        # so row i and j of L will be transformed. We do it naively
        # those 2x2 transformations of 2 rows should be a c-primitive
        # or at least a Nemo/Hecke primitive
        for k=1:cols(L)
          x = -b*f
#          L[i,k], L[j,k] = L[i,k]+L[j,k], x*L[i,k]+(x+1)*L[j,k]
          L[i,k], L[j,k] = L[i,k]+L[j,k], x*(L[i,k]+L[j,k])+L[j,k]
        end
      end
      if r
        # V = [e -b ; f a];
        # so col i and j of R will be transformed. We do it naively
        # careful: at this point, R is still transposed
        for k=1:rows(R)
          R[i, k], R[j, k] = e*R[i,k]+f*R[j,k], -b*R[i,k]+a*R[j,k]
        end
      end
    end
  end

  if l
    if r
      return S, L, R'
    else
      return S, L
    end
  elseif r
    return S, R'
  else
    return S
  end
end

function snf(G::FinGenGrpAbGen)
  if isdefined(G, :snf_map)
    return codomain(G.snf_map), G.snf_map
  end
  S, T = snf_with_transform(G.rels, l=false, r=true)
  d = fmpz[S[i,i] for i=1:min(rows(S), cols(S))]
  while length(d) < ngens(G)
    push!(d, 0)
  end
  s = Array{fmpz, 1}()
  for i=1:length(d)
    if d[i] != 1
      push!(s, d[i])
    end
  end
  TT = MatrixSpace(ZZ, rows(T), length(s))()
  j = 1
  for i=1:length(d)
    if d[i] != 1
      for k=1:rows(T)
        TT[k, j] = T[k, i]
      end
      j += 1
    end
  end
  TTi = MatrixSpace(ZZ, length(s), rows(T))()
  Ti = inv(T)

  j = 1
  for i=1:length(d)
    if d[i] != 1
      for k=1:rows(T)
        TTi[j, k] = Ti[i, k]
      end
      j += 1
    end
  end
  H = FinGenGrpAbSnf(s)
  mp = FinGenGrpAbMap(G, H, TT, TTi)
  G.snf_map = mp
  return H, mp
end

################################################################################
#
#  Predicates and basic invariants
#
################################################################################

doc"""
***
    isfinite(A::FinGenGrpAbSnf) -> Bool

> Returns whether $A$ is finite.
"""
isfinite(A::FinGenGrpAbSnf) = length(A.snf) == 0 || A.snf[end] != 0
isfinite(A::FinGenGrpAbGen) = isfinite(snf(A)[1])

doc"""
***
    isinfinite(A::FinGenGrpAbSnf) -> Bool
    isinfinite(A::FinGenGrpAbGen) -> Bool

> Returns whether $A$ is infinite.
"""
isinfinite(A::FinGenGrpAbSnf) = !isfinite(A)
isinfinite(A::FinGenGrpAbGen) = !isfinite(A)

doc"""
***
    rank(A::FinGenGrpAbSnf) -> Int
    rank(A::FinGenGrpAbGen) -> Int

> Returns the rank of $A$, that is, the dimension of the
> $\mathbf{Q}$-vectorspace $A \otimes_{\mathbf Z} \mathbf Q$.
"""
rank(A::FinGenGrpAbSnf) = length(find(x->x==0, A.snf))
rank(A::FinGenGrpAbGen) = rank(snf(A)[1])

doc"""
***
    order(A::FinGenGrpAbElem, i::Int) -> fmpz

> Returns the order of $A$. It is assumed that the order is finite.
"""
function order(a::FinGenGrpAbElem)
  G, m = snf(a.parent)
  b = m(a)
  o = fmpz(1)
  for i=1:ngens(G)
    if G.snf[i] == 0 && b[i] != 0
      error("element has inifinite order")
    end
    o = lcm(o, divexact(G.snf[i], gcd(G.snf[i], b[i])))
  end
  return o
end

doc"""
***
    order(A::FinGenGrpAbSnf) -> fmpz
    order(A::FinGenGrpAbGen) -> fmpz

> Returns the order of $A$. It is assumed that $A$ is not infinite.
"""
function order(A::FinGenGrpAbSnf)
  isinfinite(A) && error("Group must be finite")
  return prod(A.snf)
end
order(A::FinGenGrpAbGen) = order(snf(A)[1])

doc"""
***
    exponent(A::FinGenGrpAbSnf) -> fmpz
    exponent(A::FinGenGrpAbGen) -> fmpz

> Returns the exponent of $A$. It is assumed that $A$ is not infinite.
"""
function exponent(A::FinGenGrpAbSnf)
  isinfinite(A) && error("Group must be finite")
  return A.snf[end]
end
exponent(A::FinGenGrpAbGen) = exponent(snf(A)[1])

doc"""
***
    istrivial(A::FinGenGrpAbSnf, i::Int) -> bool
    istrivial(A::FinGenGrpAbGen, i::Int) -> bool

> Checks if A is the trivial group.
"""
istrivial(A::FinGenGrpAbSnf) = order(A)==1
istrivial(A::FinGenGrpAbGen) = order(A)==1


doc"""
***
    isisomorphic(G::FinGenGrpAb, H::FinGenGrpAb) -> bool

> Checks if G and H are isomorphic.
"""
function isisomorphic(G::FinGenGrpAb, H::FinGenGrpAb)
  return filter(x->x!=1,snf(G)[1].snf) == filter(x->x!=1,snf(H)[1].snf)
end


##############################################################################
#
#  Creation
#
##############################################################################

doc"""
***
  AbelianGroup(M::fmpz_mat) -> FinGenGrpAb
  AbelianGroup(M::Array{fmpz, 2}) -> FinGenGrpAb
  AbelianGroup(M::Array{Integer, 2}) -> FinGenGrpAb
  AbelianGroup(M::Array{fmpz, 1}) -> FinGenGrpAb
  AbelianGroup(M::Array{Integer, 1}) -> FinGenGrpAb

> Creates the abelian group with M as relation matrix. That is, the group will
> have cols(M) generators and each row describes one relation.
"""
function AbelianGroup(M::fmpz_mat)
  return FinGenGrpAbGen(M)
end

function AbelianGroup(M::Array{fmpz, 2})
  return AbelianGroup(MatrixSpace(FlintZZ, size(M)[1], size(M)[2])(M))
end

function AbelianGroup{T <: Integer}(M::Array{T, 2})
  return AbelianGroup(MatrixSpace(FlintZZ, size(M)[1], size(M)[2])(M))
end

function AbelianGroup(M::Array{fmpz, 1})
  return AbelianGroup(MatrixSpace(FlintZZ, 1, length(M))(M'))
end

function AbelianGroup{T <: Integer}(M::Array{T, 1})
  return AbelianGroup(MatrixSpace(FlintZZ, 1, length(M))(M'))
end

doc"""
***
  DiagonalGroup(M::fmpz_mat) -> FinGenGrpAb
  DiagonalGroup(M::Array{fmpz, 1}) -> FinGenGrpAb
  DiagonalGroup(M::Array{Integer, 1}) -> FinGenGrpAb

> Creates the abelian group as the product of cyclic groups Z/M[i].
"""
function DiagonalGroup(M::fmpz_mat)
  if rows(M) != 1
    error("The argument must have only one row")
  end

  N = MatrixSpace(FlintZZ, cols(M), cols(M))()
  for i=1:cols(M)
    N[i,i] = M[1,i]
  end
  if issnf(N)
    return FinGenGrpAbSnf(fmpz[M[1,i] for i=1:cols(M)])
  else
    return FinGenGrpAbGen(N)
  end
end

function DiagonalGroup{T <: Union{Integer, fmpz}}(M::Array{T, 1})
  N = MatrixSpace(FlintZZ, length(M), length(M))()
  for i=1:length(M)
    N[i,i] = M[i]
  end
  if issnf(N)
    return FinGenGrpAbSnf(M)
  else
    return FinGenGrpAbGen(N)
  end
end


# missing:
# is_torsion, torsion_subgroup, subgroups, ...

##############################################################################
#
##############################################################################

doc"""
***
  rand(G::FinGenGrpAbSnf) -> FinGenGrpAbElem
  rand(G::FinGenGrpAbGen) -> FinGenGrpAbElem

> For a finite abelian group G, return an element chosen uniformly at random.
"""
function rand(G::FinGenGrpAbSnf)
  if !isfinite(G)
    error("Group is not finite")
  end
  return G([rand(1:G.snf[i]) for i in 1:ngens(G)])
end

function rand(G::FinGenGrpAbGen)
  S, mS = snf(G)
  return preimage(mS, rand(S))
end

doc"""
***
  rand(G::FinGenGrpAbSnf, B::fmpz) -> FinGenGrpAbElem
  rand(G::FinGenGrpAbSnf, B::Integer) -> FinGenGrpAbElem
  rand(G::FinGenGrpAbGen, B::fmpz) -> FinGenGrpAbElem
  rand(G::FinGenGrpAbGen, B::Integer) -> FinGenGrpAbElem

> For a (potentially infinite) abelian group G, return an element
> chosen uniformly at random with coefficients bounded by B.
"""
function rand(G::FinGenGrpAbSnf, B::fmpz)
  return G([rand(1:(G.snf[i]==0 ? B : min(B, G.snf[i]))) for i in 1:ngens(G)])
end

function rand(G::FinGenGrpAbSnf, B::Integer)
  return rand(G, fmpz(B))
end

function rand(G::FinGenGrpAbGen, B::fmpz)
  S, mS = snf(G)
  return preimage(mS, rand(S, fmpz(B)))
end

function rand(G::FinGenGrpAbGen, B::Integer)
  return rand(G, fmpz(B))
end

##############################################################################
#
##############################################################################

doc"""
***
  sub(G::FinGenGrpAb, s::Array{FinGenGrpAbElem, 1}) -> FinGenGrpAb, Map

> Create the subgroup of G generated by the elements in s.
"""
function sub{T <: FinGenGrpAb}(s::Array{FinGenGrpAbElem{T}, 1})
  return sub(parent(s[1]), s)
end
function sub{T <: FinGenGrpAb}(G::T, s::Array{FinGenGrpAbElem{T}, 1})

  if length(s) == 0
    S = FinGenGrpAbSnf(fmpz[1])
    I = MatrixSpace(FlintZZ, ngens(S), ngens(G))()
    m = FinGenGrpAbMap(S, G, I)
    return S, m
  end

  p = s[1].parent
  @assert G == p
  m = MatrixSpace(FlintZZ, length(s)+nrels(p), ngens(p)+length(s))()
  for i=1:length(s)
    for j=1:ngens(p)
      m[i + nrels(p),j] = s[i][j]
    end
    m[i + nrels(p), i+ngens(p)] = 1
  end
  if typeof(p) == FinGenGrpAbSnf
    for i=1:ngens(p)
      m[i, i] = p.snf[i]
    end
  else
    for i=1:nrels(p)
      for j=1:ngens(p)
        m[i, j] = p.rels[i,j]
      end
    end
  end
  h = hnf(m)
  fstWithoutOldGens = 1
  for i in rows(h):-1:1, j in ngens(p):-1:1
    if h[i,j] != 0
      fstWithoutOldGens = i+1
      break
    end
  end
  r = sub(h, fstWithoutOldGens:rows(h), ngens(p)+1:cols(h))
  S = AbelianGroup(r)
  return S, FinGenGrpAbMap(S, p, sub(m, nrels(p)+1:rows(h), 1:ngens(p)))
end


doc"""
***
  quo(G::FinGenGrpAb, s::Array{FinGenGrpAbElem, 1}) -> FinGenGrpAb, Map

> Create the quotient of G by the elements in s.
"""
function quo{T <: FinGenGrpAb}(G::FinGenGrpAb, s::Array{FinGenGrpAbElem{T}, 1})
  if length(s) == 0
    I = MatrixSpace(FlintZZ, ngens(G), ngens(G))(1)
    m = FinGenGrpAbMap(G, G, I, I)
    return G, m
  end

  p = s[1].parent
  @assert G == p
  m = MatrixSpace(FlintZZ, length(s)+nrels(p), ngens(p))()
  for i=1:length(s)
    for j=1:ngens(p)
      m[i + nrels(p),j] = s[i][j]
    end
  end
  if typeof(p) == FinGenGrpAbSnf
    for i=1:ngens(p)
      m[i, i] = p.snf[i]
    end
  else
    for i=1:nrels(p)
      for j=1:ngens(p)
        m[i, j] = p.rels[i,j]
      end
    end
  end

  Q = AbelianGroup(m)
  I = MatrixSpace(FlintZZ, ngens(p), ngens(p))(1)
  m = FinGenGrpAbMap(p, Q, I, I)
  return Q, m
end

doc"""
***
  quo(G::FinGenGrpAb, n::Integer}) -> FinGenGrpAb, Map
  quo(G::FinGenGrpAb, n::fmpz}) -> FinGenGrpAb, Map

> Create the quotient of G by n*G
"""
function quo(G::FinGenGrpAbSnf, n::Union{fmpz, Integer})
  r = [gcd(x, n) for x = G.snf]
  I = MatrixSpace(FlintZZ, ngens(G), ngens(G))(1)
  Q = DiagonalGroup(r)
  m = FinGenGrpAbMap(G, Q, I, I)
  return Q, m
end

function quo(G::FinGenGrpAbGen, n::Union{fmpz, Integer})
  m = vcat(G.rels, MatrixSpace(FlintZZ, ngens(G), ngens(G))(n))
  Q = AbelianGroup(m)
  I = MatrixSpace(FlintZZ, ngens(G), ngens(G))(1)
  m = FinGenGrpAbMap(G, Q, I, I)
  return Q, m
end



#TODO: rename - and move elsewhere.
doc"""
***
    multgrp_of_cyclic_grp(n::fmpz) -> FinGenGrpAb

> Returns the multiplicative group of the cyclic group with $n$ elements.
"""
function multgrp_of_cyclic_grp(n::fmpz)
  composition = Array{fmpz,1}()
  for (p,mp) in factor(n)
    if (p == 2) && (mp >= 2)
      push!(composition,2)
      push!(composition,fmpz(2)^(mp-2))
    else
      push!(composition,(p-1)*p^(mp-1))
    end
  end
  return DiagonalGroup(composition)
end
multgrp_of_cyclic_grp(n::Integer) = multgrp_of_cyclic_grp(fmpz(n))

#=  <example>
M = MatrixSpace(ZZ, 2, 3)([1 2 3; 4 5 6])
G = Hecke.FinGenGrpAbGen(M)
a = Hecke.FinGenGrpAbElemCreate(G, MatrixSpace(ZZ, 1, 3)([1 2 3]))
100*a
200*a
300*a
H, mp = snf(G)
mp(a)




G = Hecke.FinGenGrpAbSnf(fmpz[2,3,4])
=#

