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

export haspreimage, has_image, hom, kernel, cokernel, image, is_injective, is_surjective,
       is_bijective

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
  fl, p = can_solve_with_solution(m, a.coeff, side = :left)

  if fl
    return true, GrpAbFinGenElem(domain(M), view(p, 1:1, 1:ngens(domain(M))))
  else
    return false, id(domain(M))
  end
end

function haspreimage(M::GrpAbFinGenMap, a::Vector{GrpAbFinGenElem})
  if isdefined(M, :imap)
    return true, map(x->preimage(M, x), a)
  end

  m = vcat(M.map, rels(codomain(M)))
  G = domain(M)
  if isdefined(G, :exponent) && fits(Int, G.exponent) && is_prime(G.exponent)
    e = G.exponent
    RR = GF(Int(e))
    fl, p = can_solve_with_solution(map_entries(RR, m), map_entries(RR, vcat([x.coeff for x = a])), side = :left)
    p = map_entries(lift, p)
  else
    fl, p = can_solve_with_solution(m, vcat([x.coeff for x = a]), side = :left)
  end

  if fl
    s = [GrpAbFinGenElem(domain(M), p[i, 1:ngens(domain(M))]) for i=1:length(a)]
    # @assert all(i->M(s[i]) == a[i], 1:length(a))
    return fl, s
  else
    return false, GrpAbFinGenElem[id(domain(M))]
  end
end



# Note that a map can be a partial function. The following function
# checks if an element is in the domain of definition.
#
# Here is an example:
# S, mS = sub(...), so ms: S -> G
# h = pseudo_inv(mS)
# Now h is a partial function on G with domain of definition the image of mS.
# Then has_image(h, x) would check if x is in the image of mS.
function has_image(M::GrpAbFinGenMap, a::GrpAbFinGenElem)
  if isdefined(M, :map)
    return true, image(M, a)
  end

  m = vcat(M.imap, rels(domain(M)))
  fl, p = can_solve_with_solution(m, a.coeff, side = :left)
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
    hom(A::Vector{GrpAbFinGenElem}, B::Vector{GrpAbFinGenElem}) -> Map

Creates the homomorphism $A[i] \mapsto B[i]$.
"""
function hom(A::Vector{GrpAbFinGenElem}, B::Vector{GrpAbFinGenElem}; check::Bool = true)
  GA = parent(A[1])
  GB = parent(B[1])
  @assert length(B) == length(A)
  @assert length(A) > 0
  #=
  if (check)
    m = vcat(fmpz_mat[x.coeff for x in A])
    m = vcat(m, rels(parent(A[1])))
    i, T = nullspace(transpose(m))
    T = transpose(T)
    T = sub(T, 1:nrows(T), 1:length(A))
    n = vcat(fmpz_mat[x.coeff for x in B])
    n = T*n
    if !can_solve_with_solution(rels(parent(B[1])), n, side = :left)[1]
      error("Data does not define a homomorphism")
    end
  end
  =#
  if ngens(GB) == 0
    return hom(GA, GB, matrix(FlintZZ, ngens(GA), 0, fmpz[]), check = check)
  end

  M = vcat([hcat(A[i].coeff, B[i].coeff) for i = 1:length(A)])
  RA = rels(GA)
  M = vcat(M, hcat(RA, zero_matrix(FlintZZ, nrows(RA), ncols(B[1].coeff))))
  if isdefined(GB, :exponent) && nrows(M) >= ncols(M)
    H = hnf_modular_eldiv(M, exponent(GB))
  else
    H = hnf(M)
  end
  H = sub(H, 1:ngens(GA), ngens(GA)+1:ngens(GA)+ngens(GB))
  h = hom(GA, GB, H, check = check)
  return h
end

@doc Markdown.doc"""
    hom(G::GrpAbFinGen, B::Vector{GrpAbFinGenElem}) -> Map

Creates the homomorphism which maps $G[i]$ to $B[i]$.
"""
function hom(G::GrpAbFinGen, B::Vector{GrpAbFinGenElem}; check::Bool = true)
  GB = parent(B[1])
  @assert length(B) == ngens(G)
  M = vcat([B[i].coeff for i = 1:length(B)])
  h = hom(G, GB, M, check = check)
  return h
end

function hom(G::GrpAbFinGen, H::GrpAbFinGen, B::Vector{GrpAbFinGenElem}; check::Bool = true)
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
  return all(x -> iszero(GrpAbFinGenElem(B, R[x, :])), 1:nrows(R))
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


==(f::GrpAbFinGenMap, g::GrpAbFinGenMap) = domain(f) === domain(g) && codomain(f) === codomain(g) && all(x -> f(x) == g(x), gens(domain(f)))
################################################################################
#
#  Inverse of a map
#
################################################################################

function inv(f::GrpAbFinGenMap)
  if isdefined(f, :imap)
    return hom(codomain(f), domain(f), f.imap, f.map, check = false)
  end
  if !is_injective(f)
    error("The map is not invertible")
  end
  gB = gens(codomain(f))
  imgs = Vector{GrpAbFinGenElem}(undef, length(gB))
  for i = 1:length(imgs)
    fl, el = haspreimage(f, gB[i])
    if !fl
      error("The map is not invertible")
    end
    imgs[i] = el
  end
  return hom(codomain(f),domain(f), imgs, check = false)
end

################################################################################
#
#  Kernel, image, cokernel
#
################################################################################

#TODO: store and reuse on map. Maybe need to change map

@doc Markdown.doc"""
    kernel(h::GrpAbFinGenMap) -> GrpAbFinGen, Map

Let $G$ be the domain of $h$. This function returns an abelian group $A$ and an
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
  if !is_snf(H)
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
    if is_zero_row(hn, i)
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
    if !is_zero_row(hn, i)
      push!(im, GrpAbFinGenElem(H, sub(hn, i:i, 1:ngens(H))))
    else
      break
    end
  end
  return sub(H, im, add_to_lattice)  # too much, this is sub in hnf....
end

@doc Markdown.doc"""
    cokernel(h::GrpAbFinGenMap) -> GrpAbFinGen, Map

Let $G$ be the codomain of $h$. This function returns an abelian group $A$ and
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
    is_surjective(h::GrpAbFinGenMap) -> Bool

Returns whether $h$ is surjective.
"""
function is_surjective(A::GrpAbFinGenMap)
  if isfinite(codomain(A))
    H, mH = image(A)
    return (order(codomain(A)) == order(H))::Bool
  else
    return (order(cokernel(A)[1]) == 1)::Bool
  end
end

################################################################################
#
#  Is zero, Is identity
#
################################################################################

function iszero(h::T) where T <: Map{<:GrpAbFinGen, <:GrpAbFinGen}
  return all(x -> iszero(h(x)), gens(domain(h)))
end

function is_identity(h::T) where T <: Map{<:GrpAbFinGen, <:GrpAbFinGen}
  @assert domain(h) === codomain(h)
  return all(x -> iszero(h(x)-x), gens(domain(h)))
end
################################################################################
#
#  Injectivity
#
################################################################################

#TODO: Improve in the finite case
@doc Markdown.doc"""
    is_injective(h::GrpAbFinGenMap) -> Bool

Returns whether $h$ is injective.
"""
function is_injective(A::GrpAbFinGenMap)
  K = kernel(A, false)[1]
  return isfinite(K) && isone(order(K))
end

################################################################################
#
#  Bijectivity
#
################################################################################

#TODO: Improve in the finite case
@doc Markdown.doc"""
    is_bijective(h::GrpAbFinGenMap) -> Bool

Returns whether $h$ is bijective.
"""
function is_bijective(A::GrpAbFinGenMap)
  return is_injective(A) && is_surjective(A)
end

###############################################################################
#
#  Compose and Squash for abelian group maps
#
###############################################################################

function compose(f::GrpAbFinGenMap, g::GrpAbFinGenMap)
  @assert domain(g) == codomain(f)
  C = codomain(g)
  if isdefined(C, :exponent)
    if fits(Int, C.exponent)
      RR = ResidueRing(FlintZZ, Int(C.exponent), cached = false)
      fRR = map_entries(RR, f.map)
      gRR = map_entries(RR, g.map)
      MRR = fRR*gRR
      M = lift(MRR)
    else
      R = ResidueRing(FlintZZ, C.exponent, cached = false)
      fR = map_entries(R, f.map)
      gR = map_entries(R, g.map)
      MR = fR*gR
      M = map_entries(lift, MR)
    end
  else
    M = f.map*g.map
  end
  if is_snf(C)
    reduce_mod_snf!(M, C.snf)
  else
    assure_has_hnf(C)
    reduce_mod_hnf_ur!(M, C.hnf)
  end
  return hom(domain(f), codomain(g), M, check = false)

end

###############################################################################
struct MapParent
  dom
  codom
  typ::String
end

elem_type(::Type{MapParent}) = Map

function show(io::IO, MP::MapParent)
  print(io, "Set of all $(MP.typ) from $(MP.dom) to $(MP.codom)")
end

parent(f::GrpAbFinGenMap) = MapParent(domain(f), codomain(f), "homomorphisms")

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
If `task` is ":map", then a map $\phi$ is computed that can be used
to obtain actual homomorphisms. This map also allows preimages.
Set `task` to ":none" to not compute the map.
"""
function hom(G::GrpAbFinGen, H::GrpAbFinGen; task::Symbol = :map)
  @assert task in [:map, :none]
  sG, mG = snf(G)  # mG : sG -> G
  sH, mH = snf(H)  # mH : sH -> G
  n = ngens(sG)
  m = ngens(sH)
  r = [cyclic_hom(x, y) for x = sG.snf for y = sH.snf]
  R = GrpAbFinGen([x[1] for x = r])
  set_attribute!(R, :hom=>(G, H), :show => show_hom)
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
    local m = transpose(vcat([preimage(mH, r(mG(sG[i]))).coeff for i = 1:ngens(sG)]))
    return R([divexact(m[i], c[i]) for i = 1:ngens(R)])
  end
  return R, MapFromFunc(phi, ihp, R, MapParent(G, H, "homomorphisms"))
end
