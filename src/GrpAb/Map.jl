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

export haspreimage, hasimage, hom, kernel, image, isinjective, issurjective,
       isbijective

################################################################################
#
#  Check for existence of (pre)image
#
################################################################################

doc"""
***
    haspreimage(M::GrpAbFinGenMap, a::GrpAbFinGenElem) -> Bool, GrpAbFinGenElem

> Returns whether $a$ is in the image of $M$. If so, the second return value is
> an element $b$ with $M(b) = a$.
"""
function haspreimage(M::GrpAbFinGenMap, a::GrpAbFinGenElem)
  if isdefined(M, :imap)
    return true, preimage(M, a)
  end

  m = vcat(M.map, rels(codomain(M)))
  fl, p = cansolve(m', a.coeff')
  if fl
    return true, domain(M)(sub(p', 1:1, 1:ngens(domain(M))))
  else
    return false, domain(M)[1]
  end
end

# Note that a map can be a partial function. The following function
# checks if an element is in the domain of definition.
#
# Here is an example:
# S, mS = sub(...), so ms: S -> G
# h = inv(mS)
# Now h is a partial function on G with domain of definition the image of mS.
# Then hasimage(h, x) would check if x is in the image of mS.
function hasimage(M::GrpAbFinGenMap, a::GrpAbFinGenElem)
  if isdefined(M, :map)
    return true, image(M, a)
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
#
#  Homomorphisms specified on arbitrary sets of generators
#
################################################################################

#TODO: Should check consistency
doc"""
    hom(A::Array{GrpAbFinGenElem, 1}, B::Array{GrpAbFinGenElem, 1}) -> Map
> Creates the homomorphism $A[i] \mapsto B[i]$
"""
function hom(A::Array{GrpAbFinGenElem, 1}, B::Array{GrpAbFinGenElem, 1}; check::Bool = false)
  GA = parent(A[1])
  GB = parent(B[1])
  @assert length(B)==length(A)
  @assert length(A)>0
  if (check)
    m = vcat([x.coeff for x in A])
    m = vcat(m, rels(parent(A[1])))
    T, i = nullspace(m')
    T = T'
    T = sub(T, 1:rows(T), 1:length(A))
    n = vcat([x.coeff for x in B])
    n = T*n
    if !cansolve(rels(parent(B[1]))', n')[1]
      error("Data does not define a homomorphism")
    end
  end

  M = vcat([hcat(A[i].coeff, B[i].coeff) for i = 1:length(A)])
  RA = rels(GA)
  M = vcat(M, hcat(RA, zero_matrix(FlintZZ, rows(RA), cols(B[1].coeff))))
  H = hnf(M)
  H = sub(H, 1:ngens(GA), ngens(GA)+1:ngens(GA)+ngens(GB))
  h = GrpAbFinGenMap(GA, GB, H)
  return h
end

doc"""
    hom(G::GrpAbFinGen, B::Array{GrpAbFinGenElem, 1}) -> Map

> Creates the homomorphism which maps `G[i]` to `B[i]`.
"""
function hom(G::GrpAbFinGen, B::Array{GrpAbFinGenElem, 1})
  GB = parent(B[1])
  M = vcat([B[i].coeff for i = 1:length(B)])
  h = GrpAbFinGenMap(G, GB, M)
  return h
end

# TODO: Extend the check to non-endomorphisms
function hom(A::GrpAbFinGen, B::GrpAbFinGen, M::fmpz_mat, check::Bool = true)
  if check #totally wrong if A != B
    if A == B
      G = A
      images = [ G([M[i, j] for j in 1:ngens(G)]) for i in 1:ngens(G) ]
      a = 0 * G[1]
      for i in 1:nrels(G)
        for j in 1:ngens(G)
          a = a + rels(G)[i, j] * images[j]
        end
        if !iszero(a)
          error("Matrix does not define a morphism of abelian groups")
        end
      end
    end
  end

  return GrpAbFinGenMap(A, B, M)
end

function hom(A::GrpAbFinGen, B::GrpAbFinGen, M::fmpz_mat, Minv, check::Bool = true)
  if check
    if A == B
      G = A
      images = [ G([M[i, j] for j in 1:ngens(G)]) for i in 1:ngens(G) ]
      a = 0 * G[1]
      for i in 1:nrels(G)
        for j in 1:ngens(G)
          a = a + G.rels[i, j] * images[j]
        end
        if !iszero(a)
          error("Matrix does not define a morphism of abelian groups")
        end
      end
    end
  end

  return GrpAbFinGenMap(A, B, M, Minv)
end

################################################################################
#
#  Kernel
#
################################################################################

#TODO: store and reuse on map. Maybe need to change map

doc"""
    kernel(h::GrpAbFinGenMap) -> GrpAbFinGen, Map

Let $G$ be the domain of $h$. This functions returns an abelian group $A$ and an
injective morphism $f \colon A \to G$, such that the image of $f$ is the kernel
of $h$.
"""

function kernel(h::GrpAbFinGenMap)
  G = domain(h)
  H = codomain(h)
  hn, t = hnf_with_transform(vcat(h.map, rels(H)))
  for i = 1:rows(hn)
    if iszero_row(hn, i)
      k = elem_type(G)[]
      for j = i:rows(t)
        push!(k, G(sub(t, j:j, 1:ngens(G))))
      end
      return sub(G, k, false)
    end
  end
  error("Something went terribly wrong in kernel computation")
end

doc"""
    image(h::GrpAbFinGenMap) -> GrpAbFinGen, Map

Let $G$ be the codomain of $h$. This functions returns an abelian group $A$ and
an injective morphism $f \colon A \to G$, such that the image of $f$ is the
image of $h$.
"""
function image(h::GrpAbFinGenMap)
  G = domain(h)
  H = codomain(h)
  hn = hnf(vcat(h.map, rels(H)))
  im = GrpAbFinGenElem[]
  for i = 1:rows(hn)
    if !iszero_row(hn, i)
      push!(im, H(sub(hn, i:i, 1:ngens(H))))
    else
      break
    end
  end
  return sub(H, im, false)  # too much, this is sub in hnf....
end

################################################################################
#
#  Surjectivity
#
################################################################################

# TODO: Make this work for infinite groups
# Is this the right way of doing it? (Carlo)
doc"""
    issurjective(h::GrpAbFinGenMap) -> Bool

Returns whether $h$ is surjective.
"""
function issurjective(A::GrpAbFinGenMap)
  H, mH = image(A)
  if isfinite(codomain(A)) && isfinite(H)
    return order(codomain(A)) == order(H)
  else
    Q, mQ = quo(codomain(A), GrpAbFinGenElem[mH(g) for g in gens(H)], false)
    S,mS=snf(Q)
    return prod(S.snf)==1
  end
end

################################################################################
#
#  Injectivity
#
################################################################################

doc"""
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

doc"""
    isbijective(h::GrpAbFinGenMap) -> Bool

Returns whether $h$ is bijective.
"""
function isbijective(A::GrpAbFinGenMap)
  return isinjective(A) && issurjective(A)
end
