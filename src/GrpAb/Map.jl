################################################################################
#
#       GrpAb/Map.jl : Functions for maps between
#                      finitely generated abelian groups
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016, 2017: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2015, 2016, 2017 Tommy Hofmann, Claus Fieker
#
################################################################################

export haspreimage, hasimage, hom, kernel, cokernel, image, isinjective, issurjective,
       isbijective

################################################################################
#
#  Check for existence of (pre)image
#
################################################################################

@doc Markdown.doc"""
    haspreimage(M::GrpAbFinGenMap, a::GrpAbFinGenElem) -> Bool, GrpAbFinGenElem

Returns whether $a$ is in the image of $M$. If so, the second return value is
an element $b$ with $M(b) = a$.
"""
function haspreimage(M::GrpAbFinGenMap, a::GrpAbFinGenElem)
  if isdefined(M, :imap)
    return true, preimage(M, a)
  end

  m = vcat(M.map, rels(codomain(M)))
  fl, p = can_solve(m, a.coeff, side = :left)
  if fl
    return true, domain(M)(view(p, 1:1, 1:ngens(domain(M))))
  else
    return false, domain(M)[1]
  end
end

# Note that a map can be a partial function. The following function
# checks if an element is in the domain of definition.
#
# Here is an example:
# S, mS = sub(...), so ms: S -> G
# h = pseudo_inv(mS)
# Now h is a partial function on G with domain of definition the image of mS.
# Then hasimage(h, x) would check if x is in the image of mS.
function hasimage(M::GrpAbFinGenMap, a::GrpAbFinGenElem)
  if isdefined(M, :map)
    return true, image(M, a)
  end

  m = vcat(M.imap, rels(domain(M)))
  fl, p = can_solve(m, a.coeff, side = :left)
  if fl
    return true, codomain(M)(view(p, 1:1, 1:ngens(codomain(M))))
  else
    return false, codomain(M)[1]
  end
end

################################################################################
#
#  Homomorphisms specified on arbitrary sets of generators
#
################################################################################

id_hom(G::GrpAbFinGen) = hom(G, G, identity_matrix(FlintZZ, ngens(G)), identity_matrix(FlintZZ, ngens(G)), check = false)

@doc Markdown.doc"""
    hom(A::Array{GrpAbFinGenElem, 1}, B::Array{GrpAbFinGenElem, 1}) -> Map
Creates the homomorphism $A[i] \mapsto B[i]$
"""
function hom(A::Array{GrpAbFinGenElem, 1}, B::Array{GrpAbFinGenElem, 1}; check::Bool = true)
  GA = parent(A[1])
  GB = parent(B[1])
  @assert length(B) == length(A)
  @assert length(A) > 0
  if (check)
    m = vcat([x.coeff for x in A])
    m = vcat(m, rels(parent(A[1])))
    i, T = nullspace(m')
    T = T'
    T = sub(T, 1:nrows(T), 1:length(A))
    n = vcat([x.coeff for x in B])
    n = T*n
    if !can_solve(rels(parent(B[1])), n, side = :left)[1]
      error("Data does not define a homomorphism")
    end
  end

  M = vcat([hcat(A[i].coeff, B[i].coeff) for i = 1:length(A)])
  RA = rels(GA)
  M = vcat(M, hcat(RA, zero_matrix(FlintZZ, nrows(RA), ncols(B[1].coeff))))
  H = hnf(M)
  if ngens(GB) == 0
    return hom(GA, GB, matrix(FlintZZ, ngens(GA), 0, fmpz[]), check = check)
  end
  H = sub(H, 1:ngens(GA), ngens(GA)+1:ngens(GA)+ngens(GB))
  h = hom(GA, GB, H, check = check)
  return h
end

@doc Markdown.doc"""
    hom(G::GrpAbFinGen, B::Array{GrpAbFinGenElem, 1}) -> Map

Creates the homomorphism which maps `G[i]` to `B[i]`.
"""
function hom(G::GrpAbFinGen, B::Array{GrpAbFinGenElem, 1}; check::Bool = true)
  GB = parent(B[1])
  @assert length(B) == ngens(G)
  M = vcat([B[i].coeff for i = 1:length(B)])
  h = hom(G, GB, M, check = check)
  return h
end

function hom(G::GrpAbFinGen, H::GrpAbFinGen, B::Array{GrpAbFinGenElem, 1}; check::Bool = true)
  @assert length(B) == ngens(G)
  @assert all(i -> parent(i) == H, B)
  M = zero_matrix(FlintZZ, ngens(G), ngens(H))
  for i = 1:ngens(G)
    for j = 1:ngens(H)
      M[i, j] = B[i][j]
    end
  end
  h = hom(G, H, M, check = check)
  return h
end

function check_mat(A::GrpAbFinGen, B::GrpAbFinGen, M::fmpz_mat)
  #we have A = X/Y  and B = U/V (generators and relations)
  #        M defines a map (hom) from X -> U
  #        Y -> X is the canonical embedding
  #        V -> U dito
  #                          M
  # need to check if Y -> X --> U lands in V
  # if Y -> X -> B is zero.
  R = rels(A) * M
  return all(x -> iszero(B(R[x, :])), 1:nrows(R))
end

function hom(A::GrpAbFinGen, B::GrpAbFinGen, M::fmpz_mat; check::Bool = true)
  if check 
    check_mat(A, B, M) || error("Matrix does not define a morphism of abelian groups")
  end

  return GrpAbFinGenMap(A, B, M)::GrpAbFinGenMap
end

function hom(A::GrpAbFinGen, B::GrpAbFinGen, M::fmpz_mat, Minv; check::Bool = true)
  if check
    check_mat(A, B, M) || error("Matrix does not define a morphism of abelian groups")
    check_mat(B, A, Minv) || error("Matrix does not define a morphism of abelian groups")
    h = GrpAbFinGenMap(A, B, M, Minv)
    ph = pseudo_inv(h)
    all(x -> x == ph(h(x)), gens(A)) || error("Matrix does not define a morphism of abelian groups")
    return h::GrpAbFinGenMap
  end

  return GrpAbFinGenMap(A, B, M, Minv)::GrpAbFinGenMap
end

################################################################################
#
#  Kernel, image, cokernel
#
################################################################################

#TODO: store and reuse on map. Maybe need to change map

@doc Markdown.doc"""
    kernel(h::GrpAbFinGenMap) -> GrpAbFinGen, Map

Let $G$ be the domain of $h$. This functions returns an abelian group $A$ and an
injective morphism $f \colon A \to G$, such that the image of $f$ is the kernel
of $h$.
"""
function kernel(h::GrpAbFinGenMap, add_to_lattice::Bool = true)
  G = domain(h)
  H = codomain(h)
  m=zero_matrix(FlintZZ, nrows(h.map)+nrows(rels(H)), ncols(h.map))
  for i=1:nrows(h.map)
    for j=1:ncols(h.map)
      m[i,j]=h.map[i,j]
    end
  end
  if !issnf(H)
    for i=1:nrels(H)
      for j=1:ngens(H)
        m[nrows(h.map)+i,j]=H.rels[i,j]
      end
    end
  else
    for i=1:length(H.snf)
      m[nrows(h.map)+i,i]=H.snf[i]
    end
  end
  hn, t = hnf_with_transform(m)
  for i = 1:nrows(hn)
    if iszero_row(hn, i)
      return sub(G, sub(t, i:nrows(t), 1:ngens(G)), add_to_lattice)
    end
  end
  if nrows(hn) == 0
    return sub(G, elem_type(G)[], add_to_lattice)
  end
  error("Something went terribly wrong in kernel computation")
end

@doc Markdown.doc"""
    image(h::GrpAbFinGenMap) -> GrpAbFinGen, Map

Let $G$ be the codomain of $h$. This functions returns an abelian group $A$ and
an injective morphism $f \colon A \to G$, such that the image of $f$ is the
image of $h$.
"""
function image(h::GrpAbFinGenMap, add_to_lattice::Bool = true)
  G = domain(h)
  H = codomain(h)
  hn = hnf(vcat(h.map, rels(H)))
  im = GrpAbFinGenElem[]
  for i = 1:nrows(hn)
    if !iszero_row(hn, i)
      push!(im, H(sub(hn, i:i, 1:ngens(H))))
    else
      break
    end
  end
  return sub(H, im, add_to_lattice)  # too much, this is sub in hnf....
end

@doc Markdown.doc"""
    cokernel(h::GrpAbFinGenMap) -> GrpAbFinGen, Map

Let $G$ be the codomain of $h$. This functions returns an abelian group $A$ and
a morphism $f \colon G \to A$, such that $A$ is the quotient of $G$ with 
respect to the image of $h$.
"""
function cokernel(h::GrpAbFinGenMap, add_to_lattice::Bool = true)
  S, mS = image(h, false)
  return quo(codomain(h), GrpAbFinGenElem[mS(g) for g in gens(S)], add_to_lattice)
end

################################################################################
#
#  Surjectivity
#
################################################################################

@doc Markdown.doc"""
    issurjective(h::GrpAbFinGenMap) -> Bool

Returns whether $h$ is surjective.
"""
function issurjective(A::GrpAbFinGenMap)  
  if isfinite(codomain(A))
    H, mH = image(A)
    return (order(codomain(A)) == order(H))::Bool
  else
    return (order(cokernel(A)) == 1)::Bool
  end
end

################################################################################
#
#  Injectivity
#
################################################################################

@doc Markdown.doc"""
    isinjective(h::GrpAbFinGenMap) -> Bool

Returns whether $h$ is injective.
"""
function isinjective(A::GrpAbFinGenMap)
  K = kernel(A)[1]
  return isfinite(K) && isone(order(K))
end

################################################################################
#
#  Bijectivity
#
################################################################################

@doc Markdown.doc"""
    isbijective(h::GrpAbFinGenMap) -> Bool

Returns whether $h$ is bijective.
"""
function isbijective(A::GrpAbFinGenMap)
  return isinjective(A) && issurjective(A)
end

###############################################################################
#
#  Compose and Squash for abelian group maps
#
###############################################################################

function compose(f::GrpAbFinGenMap, g::GrpAbFinGenMap)
  @assert domain(g)==codomain(f)
  
  M=f.map*g.map
  return GrpAbFinGenMap(domain(f), codomain(g), M)

end

###############################################################################
mutable struct MapParent
  dom
  codom
  typ::String
end

elem_type(::Type{MapParent}) = Map 

function show(io::IO, MP::MapParent)
  print(io, "Set of all $(MP.typ) from $(MP.dom) to $(MP.codom)")
end

function cyclic_hom(a::fmpz, b::fmpz)
  #hom from Z/a -> Z/b
  if iszero(a) 
    return (b, fmpz(1))
  end
  if iszero(b)
    return (fmpz(1), fmpz(1))
  end
  g = gcd(a, b)
  return (g, divexact(b, g))
end


@doc Markdown.doc"""
    hom(G::GrpAbFinGen, H::GrpAbFinGen; task::Symbol = :map) -> GrpAbFinGen, Map
Computes the group of all homomorpisms from $G$ to $H$ as an abstract group.
If {{{task}}} is ":map", then a map $\phi$ is computed that can be used
to obtain actual homomorphisms. This map also allows preimages.
Set {{{task}}} to ":none" to not compute the map.
"""
function hom(G::GrpAbFinGen, H::GrpAbFinGen; task::Symbol = :map)
  @assert task in [:map, :none]
  sG, mG = snf(G)  # mG : sG -> G
  sH, mH = snf(H)  # mH : sH -> G
  n = ngens(sG)
  m = ngens(sH)
  r = [cyclic_hom(x, y) for x = sG.snf for y = sH.snf]
  R = GrpAbFinGen([x[1] for x = r])
  set_special(R, :hom=>(G, H), :show => show_hom)
  if task == :none
    return R
  end

  c = [x[2] for x = r]

  function phi(r::GrpAbFinGenElem)
    return GrpAbFinGenMap(inv(mG) * hom(sG, sH, matrix(FlintZZ, n, m, [r[i]*c[i] for i=1:ngens(R)]), check = true) * mH)
  end

  function ihp(r::GrpAbFinGenMap)
    #transpose is due to linear indexing being wrong order
    if ngens(sG) == 0
      return R[0]
    end
    local m = vcat([preimage(mH, r(mG(sG[i]))).coeff for i = 1:ngens(sG)])'
    return R([divexact(m[i], c[i]) for i = 1:ngens(R)])
  end
  return R, MapFromFunc(phi, ihp, R, MapParent(G, H, "homomorphisms"))
end

######################################################################
# Dual
######################################################################

struct QmodZ <: GrpAb
end

function show(io::IO, G::QmodZ)
  print(io, "Q mod Z")
end

struct QmodZElem <: GrpAbElem
  elt::fmpq
  function QmodZElem(a::fmpq)
    return new(fmpq(mod(numerator(a), denominator(a)), denominator(a)))
  end
end

function show(io::IO, a::QmodZElem)
  print(io, "$(a.elt) + Z")
end

function +(a::QmodZElem, b::QmodZElem)
  return QmodZElem(a.elt + b.elt)
end

function *(a::fmpz, b::QmodZElem)
  return QmodZElem(a*b.elt)
end

function *(a::Integer, b::QmodZElem)
  return QmodZElem(a*b.elt)
end

function divexact(a::QmodZElem, b::fmpz)
  iszero(b) && throw(DivideError())
  return QmodZElem(a.elt // b)
end

function divexact(a::QmodZElem, b::Integer)
  iszero(b) && throw(DivideError())
  return QmodZElem(a.elt // b)
end

function root_of_one(::Type{QmodZ}, n::fmpz)
  return QmodZElem(fmpq(1, n))
end

function inv(a::QmodZElem)
  return QmodZElem(-(a.elt))
end

function parent(::QmodZElem)
  return QmodZ()
end

elem_type(::Type{QmodZ}) = QmodZElem

function order(a::QmodZElem)
  return denominator(a.elt)
end

(::QmodZ)(a::fmpz) = QmodZ(fmpq(a))
(::QmodZ)(a::Integer) = QmodZ(fmpq(a))
(::QmodZ)(a::fmpq) = QmodZ(a)
(::QmodZ)(a::Rational) = QmodZ(fmpq(a))

#TODO: technically, dual Z could be Q/Z ...
@doc Markdown.doc"""
    dual(G::GrpAbFinGen) -> GrpAbFinGen, Map
Computes the dual group, ie. $hom(G, Q/Z)$ as an
abstract group. The map can be used to obtain actual homomorphisms.
"""
function dual(G::GrpAbFinGen)
  T, mT = torsion_subgroup(G)
  u = root_of_one(QmodZ, order(T))
  return dual(G, u)
end

function dual(G::GrpAbFinGen, u::QmodZElem)
  o = order(u)
  H = GrpAbFinGen([o])
  R, phi = hom(G, H)
  ex = MapFromFunc(x -> x[1]*u, y -> H([numerator(y.elt) * div(o, denominator(y.elt))]), H, parent(u))
  function mu(r::GrpAbFinGenElem)
    f = phi(r)
    return f*ex
  end
  function nu(f::Map)
    g = GrpAbFinGenMap(f*inv(ex))
    return preimage(phi, g)
  end
  return R, MapFromFunc(mu, nu, R, MapParent(R, parent(u), "homomorphisms"))
end

