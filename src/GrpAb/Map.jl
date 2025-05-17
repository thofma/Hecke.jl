################################################################################
#
#       GrpAb/Map.jl : Functions for maps between
#                      finitely generated abelian groups
#
################################################################################

################################################################################
#
#  Check for existence of (pre)image
#
################################################################################

@doc raw"""
    has_preimage_with_preimage(M::FinGenAbGroupHom, a::FinGenAbGroupElem)
                                                       -> Bool, FinGenAbGroupElem

Returns whether $a$ is in the image of $M$. If so, the second return value is
an element $b$ with $M(b) = a$.
"""
function has_preimage_with_preimage(M::FinGenAbGroupHom, a::FinGenAbGroupElem)
  if isdefined(M, :imap)
    return true, preimage(M, a)
  end

  m = _preimage_ctx(M)
  fl, p = can_solve_with_solution(m, a.coeff, side = :left)

  if fl
    return true, FinGenAbGroupElem(domain(M), view(p, 1:1, 1:ngens(domain(M))))
  else
    return false, id(domain(M))
  end
end

@attr AbstractAlgebra.Solve.SolveCtx{ZZRingElem, AbstractAlgebra.Solve.HermiteFormTrait, ZZMatrix, ZZMatrix, ZZMatrix} function _preimage_ctx(M::FinGenAbGroupHom)
  return solve_init(vcat(M.map, rels(codomain(M))))
end

function has_preimage_with_preimage(M::FinGenAbGroupHom, a::Vector{FinGenAbGroupElem})
  if isdefined(M, :imap)
    return true, map(x->preimage(M, x), a)
  end

  if length(a) == 0
    return true, a
  end

  m = vcat(M.map, rels(codomain(M)))
  G = domain(M)
  H = codomain(M)
  #CF: problem
  # f:U = C_2 -> G = C_4: x -> 2*x
  #want pre-image of 2*C_4[1], as matrix x*[2] = [2]
  #(with obvious solution [1])
  #but mod 2 this collapses to x[0] = [0]
  #with solution 0
  #the map is no longer injective....
  if isdefined(G, :exponent) && fits(Int, G.exponent) && is_prime(G.exponent) &&
    isdefined(H, :exponent) && G.exponent == H.exponent
    e = G.exponent
    RR = Native.GF(Int(e))
    fl, p = can_solve_with_solution(map_entries(RR, m), map_entries(RR, reduce(vcat, [x.coeff for x = a])), side = :left)
    p = map_entries(x -> lift(x), p)
  else
    fl, p = can_solve_with_solution(m, reduce(vcat, [x.coeff for x = a]), side = :left)
  end

  if fl
    s = [FinGenAbGroupElem(domain(M), p[i:i, 1:ngens(domain(M))]) for i=1:length(a)]
    # @assert all(i->M(s[i]) == a[i], 1:length(a))
    return fl, s
  else
    return false, FinGenAbGroupElem[id(domain(M))]
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
function has_image_with_image(M::FinGenAbGroupHom, a::FinGenAbGroupElem)
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

@doc raw"""
    id_hom(G::FinGenAbGroup) -> FinGenAbGroupHom

Return the identity homomorphism of `G`.
"""
function id_hom(G::FinGenAbGroup)
  I = identity_matrix(ZZ, ngens(G))
  return FinGenAbGroupHom(G, G, I, I)::FinGenAbGroupHom
end

@doc raw"""
    hom(
      G::FinGenAbGroup,
      H::FinGenAbGroup,
      A::Vector,
      B::Vector;
      check::Bool=true,
    ) -> FinGenAbGroupHom

Return the group homomorphism $G\to H$ that sends `A[i]` to `B[i]` for all `i`.
If `check` is set to `true`, the function checks whether the inputs indeed
define a morphism of finitely generated abelian groups.
"""
function hom(
    G::FinGenAbGroup,
    H::FinGenAbGroup,
    A::Vector,
    B::Vector;
    check::Bool=true
  )
  @req length(B) == length(A) "Lists of elements in input must have the same size"
  @req all(a -> parent(a) === G, A) "Wrong parent for first input list"
  @req all(b -> parent(b) === H, B) "Wrong parent for second input list"
  if ngens(H) == 0
    return hom(G, H, matrix(ZZ, ngens(G), 0, ZZRingElem[]); check)
  elseif ngens(G) == 0
    return hom(G, H, matrix(ZZ, 0, ngens(H), ZZRingElem[]); check)
  end

  @req length(A) >= 1 "For maps between nontrivial groups, lists of elements must be nonempty"

  if check
    m = reduce(vcat, ZZMatrix[x.coeff for x in A])
    m = reduce(vcat, ZZMatrix[m, rels(G)])
    T = kernel(transpose(m); side=:right)
    i = ncols(T)
    T = transpose(T)
    T = sub(T, 1:nrows(T), 1:length(A))
    n = reduce(vcat, ZZMatrix[x.coeff for x in B])
    n = T*n
    @req can_solve(rels(H), n; side=:left) "Data does not define a homomorphism"
  end

  _M = reduce(vcat, ZZMatrix[hcat(A[i].coeff, B[i].coeff) for i = 1:length(A)])
  RA = rels(G)
  _M = vcat(_M, hcat(RA, zero_matrix(ZZ, nrows(RA), ncols(B[1].coeff))))
  if isdefined(H, :exponent) && nrows(_M) >= ncols(_M)
    M = hnf_modular_eldiv(_M, exponent(H))
  else
    M = hnf(_M)
  end
  M = sub(M, 1:ngens(G), ngens(G)+1:ngens(G)+ngens(H))
  h = hom(G, H, M; check)
  return h
end

@doc raw"""
    hom(
      G::FinGenAbGroup,
      H::FinGenAbGroup,
      B::Vector;
      check::Bool=true,
    ) -> FinGenAbGroupHom

Return the group homomorphism $G\to H$ that sends `G[i]` to `B[i]` for all `i`.
If `check` is set to `true`, the function checks whether the inputs indeed
define a morphism of finitely generated abelian groups.
"""
function hom(
    G::FinGenAbGroup,
    H::FinGenAbGroup,
    B::Vector;
    check::Bool=true
  )
  @req length(B) == ngens(G) "Number of elements in input list should be the same as the number of generators of the source"
  @req all(b -> parent(b) == H, B) "Wrong parent for input list"
  if length(B) == 0
    M = zero_matrix(ZZ, ngens(G), ngens(H))
  else
    M = reduce(vcat, ZZMatrix[x.coeff for x in B])
  end
  h = hom(G, H, M; check)
  return h
end

function check_mat(A::FinGenAbGroup, B::FinGenAbGroup, M::ZZMatrix)
  #we have A = X/Y  and B = U/V (generators and relations)
  #        M defines a map (hom) from X -> U
  #        Y -> X is the canonical embedding
  #        V -> U dito
  #                          M
  # need to check if Y -> X --> U lands in V
  # if Y -> X -> B is zero.
  R = rels(A) * M
  return all(x -> iszero(FinGenAbGroupElem(B, R[x:x, :])), 1:nrows(R))
end

@doc raw"""
    hom(
      G::FinGenAbGroup,
      H::FinGenAbGroup,
      M::ZZMatrix;
      check::Bool=true,
    ) -> FinGenAbGroupHom

Return the group homomorphism $G\to H$ defined by the integer matrix
$M = (m_{ij})$, by sending the $i$th generator of $G$ to
$\sum_{j=1}^nm_{ij}h_j$ where $h_1,\ldots, h_n$ are the generators of $H$.
If `check` is set to `true`, the function checks whether `M` indeed
defines a morphism of finitely generated abelian groups.
"""
function hom(
    G::FinGenAbGroup,
    H::FinGenAbGroup,
    M::ZZMatrix;
    check::Bool=true,
  )
  if check
    @req check_mat(G, H, M) "Matrix does not define a morphism of abelian groups"
  end
  return FinGenAbGroupHom(G, H, M)::FinGenAbGroupHom
end

@doc raw"""
    hom(
      G::FinGenAbGroup,
      H::FinGenAbGroup,
      M::ZZMatrix,
      Minv::ZZMatrix;
      check::Bool=true,
    ) -> FinGenAbGroupHom

Return the group homomorphism $G\to H$ defined by the integer matrix
$M = (m_{ij})$ (by sending the $i$th generator of $G$ to
$\sum_{j=1}^nm_{ij}h_j$ where $h_1,\ldots, h_n$ are the generators of $H$)
and with pseudo-inverse $H\to G$ (or right inverse) defined by `Minv`.
If `check` is set to `true`, the function checks whether `M` and `Minv` indeed
define morphisms of finitely generated abelian groups, and whether `Minv`
defines a right inverse to `M`.
"""
function hom(
    G::FinGenAbGroup,
    H::FinGenAbGroup,
    M::ZZMatrix,
    Minv::ZZMatrix;
    check::Bool=true,
  )
  if check
    @req check_mat(G, H, M) "First matrix does not define a morphism of abelian groups"
    @req check_mat(H, G, Minv) "Second matrix does not define a morphism of abelian groups"
    h = FinGenAbGroupHom(G, H, M, Minv)
    ph = pseudo_inv(h)
    @req all(x -> x == ph(h(x)), gens(G)) "Second matrix does not define a right inverse of the first matrix"
    return h::FinGenAbGroupHom
  end

  return FinGenAbGroupHom(G, H, M, Minv)::FinGenAbGroupHom
end

==(f::FinGenAbGroupHom, g::FinGenAbGroupHom) = domain(f) === domain(g) && codomain(f) === codomain(g) && all(x -> f(x) == g(x), gens(domain(f)))

Base.hash(f::FinGenAbGroupHom, h::UInt) = h

################################################################################
#
#  Inverse of a map
#
################################################################################

function inv(f::FinGenAbGroupHom)
  if isdefined(f, :imap)
    return hom(codomain(f), domain(f), f.imap, f.map, check = false)
  end
  if !is_injective(f)
    error("The map is not invertible")
  end
  gB = gens(codomain(f))
  fl, imgs = has_preimage_with_preimage(f, gB)
  if !fl
    error("The map is not invertible")
  end
  return hom(codomain(f),domain(f), imgs, check = false)
end

################################################################################
#
#  Kernel, image, cokernel
#
################################################################################

#TODO: store and reuse on map. Maybe need to change map

@doc raw"""
    kernel(h::FinGenAbGroupHom) -> FinGenAbGroup, Map

Let $G$ be the domain of $h$. This function returns an abelian group $A$ and an
injective morphism $f \colon A \to G$, such that the image of $f$ is the kernel
of $h$.
"""
function kernel(h::FinGenAbGroupHom, add_to_lattice::Bool = true)
  G = domain(h)
  H = codomain(h)
  m = zero_matrix(ZZ, nrows(h.map)+nrows(rels(H)),
                           ncols(h.map))
  for i=1:nrows(h.map)
    for j=1:ncols(h.map)
      m[i,j]=h.map[i,j]
    end
  end
  if !is_snf(H)
    for i=1:nrels(H)
      for j=1:ngens(H)
        m[nrows(h.map) + i, j] = H.rels[i, j]
      end
    end
  else
    for i=1:length(H.snf)
      m[nrows(h.map) + i, i] = H.snf[i]
    end
  end
  hn, t = hnf_with_transform(m)
  for i = 1:nrows(hn)
    if is_zero_row(hn, i)
      return sub(G, sub(t, i:nrows(t), 1:ngens(G)), add_to_lattice)
    end
  end
  # if the Hermite form has no zero-row, there is no
  # non-trivial kernel element
  return sub(G, elem_type(G)[], add_to_lattice)
end

@doc raw"""
    image(h::FinGenAbGroupHom) -> FinGenAbGroup, Map

Let $G$ be the codomain of $h$. This functions returns an abelian group $A$ and
an injective morphism $f \colon A \to G$, such that the image of $f$ is the
image of $h$.
"""
function image(h::FinGenAbGroupHom, add_to_lattice::Bool = true)
  G = domain(h)
  H = codomain(h)
  hn = hnf(vcat(h.map, rels(H)))
  im = FinGenAbGroupElem[]
  for i = 1:nrows(hn)
    if !is_zero_row(hn, i)
      push!(im, FinGenAbGroupElem(H, sub(hn, i:i, 1:ngens(H))))
    else
      break
    end
  end
  return sub(H, im, add_to_lattice)  # too much, this is sub in hnf....
end

@doc raw"""
    cokernel(h::FinGenAbGroupHom) -> FinGenAbGroup, Map

Let $G$ be the codomain of $h$. This function returns an abelian group $A$ and
a morphism $f \colon G \to A$, such that $A$ is the quotient of $G$ with
respect to the image of $h$.
"""
function cokernel(h::FinGenAbGroupHom, add_to_lattice::Bool = true)
  S, mS = image(h, false)
  return quo(codomain(h), FinGenAbGroupElem[mS(g) for g in gens(S)], add_to_lattice)
end

################################################################################
#
#  Surjectivity
#
################################################################################

@doc raw"""
    is_surjective(h::FinGenAbGroupHom) -> Bool

Returns whether $h$ is surjective.
"""
@attr Bool function is_surjective(A::FinGenAbGroupHom)
  if isfinite(codomain(A))
    H, mH = image(A, false)
    return (order(codomain(A)) == order(H))::Bool
  else
    KK = cokernel(A)[1]
    return is_finite(KK) && isone(order(KK))
  end
end

################################################################################
#
#  Is zero, Is identity
#
################################################################################

function iszero(h::T) where T <: Map{<:FinGenAbGroup, <:FinGenAbGroup}
  return all(x -> iszero(h(x)), gens(domain(h)))
end

function is_identity(h::T) where T <: Map{<:FinGenAbGroup, <:FinGenAbGroup}
  @assert domain(h) === codomain(h)
  return all(x -> iszero(h(x)-x), gens(domain(h)))
end
################################################################################
#
#  Injectivity
#
################################################################################

#TODO: Improve in the finite case
@doc raw"""
    is_injective(h::FinGenAbGroupHom) -> Bool

Returns whether $h$ is injective.
"""
@attr Bool function is_injective(A::FinGenAbGroupHom)
  K = kernel(A, false)[1]
  return isfinite(K) && isone(order(K))
end

################################################################################
#
#  Bijectivity
#
################################################################################

#TODO: Improve in the finite case
@doc raw"""
    is_bijective(h::FinGenAbGroupHom) -> Bool

Returns whether $h$ is bijective.
"""
@attr Bool function is_bijective(A::FinGenAbGroupHom)
  return is_injective(A) && is_surjective(A)
end

is_isomorphism(A::FinGenAbGroupHom) = is_bijective(A)

###############################################################################
#
#  Compose and Squash for abelian group maps
#
###############################################################################

function compose(f::FinGenAbGroupHom, g::FinGenAbGroupHom)
  @assert domain(g) == codomain(f)
  C = codomain(g)
  if isdefined(C, :exponent)
    if fits(Int, C.exponent)
      RR = residue_ring(ZZ, Int(C.exponent), cached = false)[1]
      fRR = map_entries(RR, f.map)
      gRR = map_entries(RR, g.map)
      MRR = fRR*gRR
      M = lift(MRR)
    else
      R = residue_ring(ZZ, C.exponent, cached = false)[1]
      fR = map_entries(R, f.map)
      gR = map_entries(R, g.map)
      MR = fR*gR
      M = map_entries(lift, MR)
    end
  else
    M = f.map*g.map
  end
  assure_reduced!(C, M)
  return hom(domain(f), codomain(g), M, check = false)
end

function +(f::FinGenAbGroupHom, g::FinGenAbGroupHom)
  @assert domain(f) == domain(g)
  @assert codomain(f) == codomain(g)
  M = f.map + g.map
  C = codomain(f)
  assure_reduced!(C, M)

  return hom(domain(f), codomain(f), M, check = false)
end

function -(f::FinGenAbGroupHom, g::FinGenAbGroupHom)
  @assert domain(f) == domain(g)
  @assert codomain(f) == codomain(g)
  M = f.map - g.map
  C = codomain(f)
  assure_reduced!(C, M)

  return hom(domain(f), codomain(f), M, check = false)
end

function -(f::FinGenAbGroupHom)
  M = -f.map
  C = codomain(f)
  assure_reduced!(C, M)

  return hom(domain(f), codomain(f), M, check = false)
end

function Base.:(*)(a::IntegerUnion, f::FinGenAbGroupHom)
  M = a*f.map
  C = codomain(f)
  assure_reduced!(C, M)
  return hom(domain(f), codomain(f), M, check = false)
end

Base.:(*)(f::FinGenAbGroupHom, a::IntegerUnion) = a*f

function Base.:^(f::FinGenAbGroupHom, n::Integer)
  @assert domain(f) === codomain(f)
  @assert n >= 0
  C = codomain(f)
  if isdefined(C, :exponent)
    if fits(Int, C.exponent)
      RR = residue_ring(ZZ, Int(C.exponent), cached = false)[1]
      fRR = map_entries(RR, f.map)
      MRR = fRR^n
      M = lift(MRR)
    else
      R = residue_ring(ZZ, C.exponent, cached = false)[1]
      fR = map_entries(R, f.map)
      MR = fR^n
      M = map_entries(lift, MR)
    end
  else
    M = f.map^n
  end
  assure_reduced!(C, M)
  return hom(domain(f), codomain(f), M, check = false)
end

function evaluate(p::ZZPolyRingElem, f::FinGenAbGroupHom)
  @assert domain(f) === codomain(f)
  M = p(f.map)
  C = codomain(f)
  assure_reduced!(C, M)
  return hom(domain(f), codomain(f), M, check = false)
end

function evaluate(p::QQPolyRingElem, f::FinGenAbGroupHom)
  @assert domain(f) === codomain(f)
  @assert all(a -> is_integral(a), coefficients(p))
  return evaluate(map_coefficients(ZZ, p, cached = false), f)
end

(p::ZZPolyRingElem)(f::FinGenAbGroupHom) = evaluate(p, f)

(p::QQPolyRingElem)(f::FinGenAbGroupHom) = evaluate(p, f)

###############################################################################

struct MapParent
  dom
  codom
  typ::String
end

# == and hash are doing the right thing, since this is immutable

elem_type(::Type{MapParent}) = Map

function show(io::IO, MP::MapParent)
  io = pretty(io)
  print(io, "Set of all $(MP.typ) from ")
  print(terse(io), Lowercase(), MP.dom)
  print(io, " to ")
  print(terse(io), Lowercase(), MP.codom)
end

parent(f::FinGenAbGroupHom) = MapParent(domain(f), codomain(f), "homomorphisms")

function cyclic_hom(a::ZZRingElem, b::ZZRingElem)
  #hom from Z/a -> Z/b
  if iszero(a)
    return (b, ZZRingElem(1))
  end
  if iszero(b)
    return (ZZRingElem(1), ZZRingElem(1))
  end
  g = gcd(a, b)
  return (g, divexact(b, g))
end


@doc raw"""
    hom(G::FinGenAbGroup, H::FinGenAbGroup; task::Symbol = :map) -> FinGenAbGroup, Map

Computes the group of all homomorpisms from $G$ to $H$ as an abstract group.
If `task` is ":map", then a map $\phi$ is computed that can be used
to obtain actual homomorphisms. This map also allows preimages.
Set `task` to ":none" to not compute the map.
"""
function hom(G::FinGenAbGroup, H::FinGenAbGroup; task::Symbol = :map)
  @assert task in [:map, :none]
  sG, mG = snf(G)  # mG : sG -> G
  sH, mH = snf(H)  # mH : sH -> G
  n = ngens(sG)
  m = ngens(sH)
  r = [cyclic_hom(x, y) for x = sG.snf for y = sH.snf]
  R = FinGenAbGroup([x[1] for x = r])
  set_attribute!(R, :hom=>(G, H), :show => show_hom)
  if task == :none
    return R
  end

  c = [x[2] for x = r]

  function phi(r::FinGenAbGroupElem)
    return FinGenAbGroupHom(inv(mG) * hom(sG, sH, matrix(ZZ, n, m, [r[i] * c[i] for i=1:length(c)]), check = true) * mH)
  end

  function ihp(r::FinGenAbGroupHom)
    #transpose is due to linear indexing being wrong order
    if ngens(sG) == 0
      return R[0]
    end
    local mm = transpose(reduce(vcat, [preimage(mH, r(mG(sG[i]))).coeff for i = 1:ngens(sG)]))
    return R([divexact(mm[j,i], c[(i-1)*m+j]) for i=1:n for j=1:m])
  end
  return R, MapFromFunc(R, MapParent(G, H, "homomorphisms"), phi, ihp)
end

################################################################################
#
#  Pre- and postinverse
#
################################################################################

function _prepostinverse(f::FinGenAbGroupHom)
  # in the surjective case, we find the preimage and
  # if it does not exist, we find any element of the domain,
  # which is also fine
  return [has_preimage_with_preimage(f, g)[2] for g in gens(codomain(f))]
end

# Given surjective f, find g such that fg = id
function preinverse(f::FinGenAbGroupHom)
  @req is_surjective(f) "Map must be surjective"
  return hom(codomain(f), domain(f), _prepostinverse(f))
end

# Given surjective f, find g such that gf = id
function postinverse(f::FinGenAbGroupHom)
  @req is_injective(f) "Map must be injective"
  return hom(codomain(f), domain(f), _prepostinverse(f))
end
