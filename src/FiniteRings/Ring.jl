################################################################################
#
#  Ring interface functions
#
################################################################################

function is_known(::typeof(is_finite), ::FiniteRing)
  return true
end

function is_finite(R::FiniteRing)
  return true
end

function is_exact_type(::Type{FiniteRing})
  return true
end

function elem_type(::Type{FiniteRing})
  return FiniteRingElem
end

function parent_type(::Type{FiniteRingElem})
  return FiniteRing
end

function characteristic(R::FiniteRing)
  return exponent(underlying_abelian_group(R))
end

function order(R::FiniteRing)
  return order(underlying_abelian_group(R))
end

# Generators of R as a Z-module, that is, the underlying
# concrete abelian group
@attr Vector{FiniteRingElem} function _zgens(R::FiniteRing)
  A = underlying_abelian_group(R)
  return FiniteRingElem.(Ref(R), gens(A))
end

@doc raw"""
    additive_generators(R::FiniteRing) -> Vector{FiniteRingElement}

Return generators of the additive group of a finite ring $R$.

# Examples

```jldoctest
julia> R, _ = finite_ring(matrix_algebra(GF(2), 2));

julia> additive_generators(R)
4-element Vector{FiniteRingElem}:
 Finite ring element [1, 0, 0, 0]
 Finite ring element [0, 1, 0, 0]
 Finite ring element [0, 0, 1, 0]
 Finite ring element [0, 0, 0, 1]
```
"""
additive_generators(R::FiniteRing) = _zgens(R)

@attr Int function _nzgens(R::FiniteRing)
  return ngens(underlying_abelian_group(R))
end

@doc raw"""
    number_of_additive_generators(R::FiniteRing) -> Int

Return the number generators of the additive group of a finite ring $R$.

# Examples

```jldoctest
julia> R, _ = finite_ring(matrix_algebra(GF(2), 2));

julia> number_of_additive_generators(R)
4
```
"""
number_of_additive_generators(R::FiniteRing) = _nzgens(R)

AbstractAlgebra.promote_rule(::Type{FiniteRingElem}, ::Type{T}) where {T <: IntegerUnion} = FiniteRingElem

################################################################################
#
#  Field access
#
################################################################################

function underlying_abelian_group(R::FiniteRing)
  return R.A
end

@doc raw"""
    elementary_divisors(R::FiniteRing) -> Vector

Return the elementary divisors of the additive group of the finite ring $R$.

# Examples

```jldoctest
julia> R, f = finite_ring(matrix_algebra(GF(2), 2));

julia> elementary_divisors(R)
4-element Vector{ZZRingElem}:
 2
 2
 2
 2
```
"""
elementary_divisors(R::FiniteRing) = elementary_divisors(underlying_abelian_group(R))

################################################################################
#
#  Predicates
#
################################################################################

@attr Bool function is_commutative(R::FiniteRing)
  for xR in _zgens(R)
    for yR in _zgens(R)
      if xR * yR != yR * xR
        return false
      end
    end
  end
  return true
end

function is_zero(R::FiniteRing)
  return is_trivial(underlying_abelian_group(R))
end

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, A::FiniteRing)
  print(io, "Finite ring")
end

function Base.show(io::IO, ::MIME"text/plain", R::FiniteRing)
  io = AbstractAlgebra.pretty(io)
  A = underlying_abelian_group(R)
  println(io, "Finite ring with additive group")
  print(io, AbstractAlgebra.Indent(), "isomorphic to ", )
  show_snf_structure(io, snf(A)[1])
  println(io)
  print(io, "and with ", ItemQuantity(ncols(rels(A)), "generator"), " and ",
        ItemQuantity(nrows(rels(A)), "relation"))
  print(io, AbstractAlgebra.Dedent())
end

################################################################################
#
#  Construction from other objects
#
################################################################################

@doc raw"""
    finite_ring(c::Vector{IntegerUnion},
                m::Vector{ZZMatrix}; check::Bool = true)

Return the finite ring with additive group isomorphic to
$\mathbf{Z}/c_1\mathbf{Z} \times \dotsb \times \mathbf{Z}/c_n \mathbf{Z}$ and
such that generators satisfy $b_i b_j = \sum_{k=1}^n m^{(i)}_{jk} b_k$,
where $m^{(i)}$ is the $j$-th entry of $m$.

If `check` is `true` (default), it is verified that this defines a ring.

# Examples

```jldoctest
julia> finite_ring([2, 2], [ZZ[1 0; 0 0], ZZ[0 0; 0 1]]) # Z/2Z x Z/2Z
Finite ring with additive group
  isomorphic to (Z/2)^2
  and with 2 generators and 2 relations
```
"""
function finite_ring(c::Vector{<:IntegerUnion}, mats; check::Bool = true)
  A = abelian_group(c)
  @req length(mats) == length(c) "Must have same number of generators and matrices"
  R = FiniteRing(A, [hom(A, A, m) for m in mats])
  gR = _zgens(R)
  if check
    for x in gR, y in gR, z in gR
      @req x * (y * z) == (x * y) * z "Multiplication not associative"
      @req x*(y + z) == x*y + x * z "Distributive law violated"
      @req (x + y)*z == x*z + y * z  "Distributive law violated"
    end
  end
  return R
end

@doc raw"""
    finite_ring(c::Vector{IntegerUnion},
                m::Array{IntegerUnion, 3}; check::Bool = true)

Return the finite ring with additive group isomorphic to
$\mathbf{Z}/c_1\mathbf{Z} \times \dotsb \times \mathbf{Z}/c_n \mathbf{Z}$ and
such that generators satisfy $b_i b_j = \sum_{k=1}^n m_{ijk} b_k$.

If `check` is `true` (default), it is verified that this defines a ring.

# Examples

```jldoctest
julia> m = [1 0; 0 0;;; 0 0; 0 1];

julia> R = finite_ring([2, 2], m) # this is the direct product Z/2Z x Z/2Z
Finite ring with additive group
  isomorphic to (Z/2)^2
  and with 2 generators and 2 relations
```
"""
function finite_ring(c::Vector{<: IntegerUnion}, mult::Array{<: IntegerUnion, 3}; check::Bool = true)
  k = length(c)
  @req size(mult) == (k, k, k) "Dimension mismatch"
  mats = [mult[i, :, :] for i in 1:k]
  return finite_ring(c, matrix.(Ref(ZZ), Ref(k), Ref(k), mats); check)
end

@doc raw"""
    finite_ring(A::AbstractAssociativeAlgebra) -> FiniteRing, FiniteRingMap

Given an algebra $A$ over a finite field $k$, return $(R, f)$, where $R$ is a finite ring and $f \colon
R \to A$ an isomorphism rings. Currently, the field $k$ must be a prime field.

# Examples

```jldoctest
julia> R, f = finite_ring(matrix_algebra(GF(2), 3));

julia> R
Finite ring with additive group
  isomorphic to (Z/2)^9
  and with 9 generators and 9 relations
```
"""
function finite_ring(A::AbstractAssociativeAlgebra)
  F = base_ring(A)
  @assert is_finite(F) && absolute_degree(F) == 1
  p = characteristic(F)
  n = dim(A)
  AA = abelian_group([p for i in 1:n])
  B = basis(A)
  mult = FinGenAbGroupHom[]
  for b in B
    push!(mult, hom(AA, AA, lift.(Ref(ZZ), representation_matrix(b))))
  end
  R = FiniteRing(AA, mult)
  inv = hom(A, R, x -> lift(ZZ, x), [R(lift.(Ref(ZZ), coefficients(x))) for x in basis(A)]; check = false)
  f = hom(R, A, [A(F.(_eltseq(x.a.coeff))) for x in _zgens(R)]; inverse = inv, check = false)
  inv.inverse = f
  f.inv = inv
  if is_prime(order(F))
    set_attribute!(R, :rgens, [preimage(f, x) for x in gens(A)])
  end
  return R, f
end

function _ideal_to_matrix_ring_ideal(R, M, MR, I, hhinv)
  zgens = _zgens(I) # Z-generating set
  n = degree(M)
  newzgens = elem_type(MR)[]
  # radical is M_n(J)
  _z = zero_matrix(R, n, n)
  for i in 1:n
    for j in 1:n
      for r in zgens
        _z[i, j] = r
        push!(newzgens, hhinv(M(deepcopy(_z))))
      end
      _z[i, j] = zero(R)
    end
  end
  return _ideal_zgens(MR, newzgens; side = :twosided, check = false)
end

@doc raw"""
    finite_ring(A::MatRing{FiniteRingElem}) -> FiniteRing

Given a matrix ring $A$ over a finite ring, return $(R, f)$, where $R$ is a
finite ring and $f \colon R \to A$ an isomorphism rings. Currently, the field
$k$ must be a prime field.

# Examples

```jldoctest
julia> R, = finite_ring(matrix_algebra(GF(2), 2));

julia> S = matrix_ring(R, 2);

julia> T, = finite_ring(S);

julia> T
Finite ring with additive group
  isomorphic to (Z/2)^16
  and with 16 generators and 16 relations
```
"""
function finite_ring(M::AbstractAlgebra.Generic.MatRing{FiniteRingElem})
  R = base_ring(M)
  S = underlying_abelian_group(R)
  n = degree(M)
  D, DtoSs, SstoD = biproduct(fill(S, n^2)...)
  Inds = CartesianIndices((n, n))
  h = function(d)
    m = zero(M)
    for i in 1:n^2
      m[Inds[i]] = FiniteRingElem(R, DtoSs[i](d))
    end
    return m
  end
  hinv = function(m)
    return sum([ SstoD[i](data(m[Inds[i]])) for i in 1:n^2])
  end
  homs = [ hom(D, D, [ hinv(h(D[i]) * h(D[j])) for j in 1:ngens(D)]) for i in 1:ngens(D)]
  MR = FiniteRing(D, homs)
  hhinv = m -> FiniteRingElem(MR, hinv(m))
  hh = hom(MR, M, h.(data.(additive_generators(MR))); inverse = hhinv, check = false)
  #hh = r -> h(data(r))

  # Let's compute the radical (chain)
  _J = radical(R)
  rad_chain = [_ideal_to_matrix_ring_ideal(R, M, MR, _J, hhinv)]
  while !is_zero(_J)
    _J = _J *_J
    push!(rad_chain, _ideal_to_matrix_ring_ideal(R, M, MR, _J, hhinv))
  end
  set_attribute!(MR, :radical => rad_chain[1])
  set_attribute!(MR, :radical_chain => rad_chain)
  return MR, hh
end

function finite_ring(A::AbsOrdQuoRing)
  AA, AAtoA, AtoAA = abelian_group(A)
  B = gens(AA)
  mult = FinGenAbGroupHom[]
  for b in B
    push!(mult, hom(AA, AA, [AtoAA(AAtoA(b) * AAtoA(a)) for a in B]))
  end
  R = FiniteRing(AA, mult)
  iso = hom(R, A, [AAtoA(x.a) for x in _zgens(R)]; check = false)
  isoinv = hom(A, R, [FiniteRingElem(R, AtoAA(A(x))) for x in basis(base_ring(A))])
  iso.inv = isoinv
  #fw = x -> AAtoA(x.a)
  #bw = x -> FiniteRingElem(R, AtoAA(x))
  return R, iso
end

################################################################################
#
#  Maximal p-subring
#
################################################################################

@doc raw"""
    maximal_p_quotient_ring(R::FiniteRing, p::IntegerUnion) -> FiniteRing, FiniteRingHom

Given a finite ring $R$ and a prime $p$, return the largest quotient ring $S$ of $p$-power order and the projection $R \to S$.

# Examples

```jldoctest
julia> R = finite_ring([6, 6], [ZZ[1 0; 0 0], ZZ[0 0; 0 1]]); # Z/6Z x Z/6Z

julia> S, f = maximal_p_quotient_ring(R, 3);

julia> S
Finite ring with additive group
  isomorphic to (Z/3)^2
  and with 2 generators and 4 relations
```
"""
function maximal_p_quotient_ring(R::FiniteRing, p::IntegerUnion)
  A = underlying_abelian_group(R)
  B, BtoA = sylow_subgroup(A, p)
  fl, j = has_complement(BtoA)
  @assert fl
  C, AtoC = quo(A, j)
  homss = FinGenAbGroupHom[]
  for c in gens(C)
    h = hom(C, C, [AtoC(data(FiniteRingElem(R, preimage(AtoC, c)) * FiniteRingElem(R, preimage(AtoC, cc)))) for cc in gens(C)])
    push!(homss, h)
  end
  S = FiniteRing(C, homss)
  f = FiniteRingHom(R, S, true, AtoC)
  g = FiniteRingHom(S, R, false, inv(BtoA * AtoC) * BtoA)
  f.g = g
  return S, f
end

@attr Tuple function decompose_into_p_rings(R::FiniteRing)
  ps = prime_divisors(characteristic(R))
  if length(ps) == 1
    return FiniteRing[R], FiniteRingHom[id_hom(R)]
  end
  idems = elem_type(R)[]
  quorings = FiniteRing[]
  projs = FiniteRingHom[]
  for p in ps
    S, RtoS = maximal_p_quotient_ring(R, p)
    push!(idems, preimage(RtoS, one(S)))
    push!(quorings, S)
    push!(projs, RtoS)
  end
  @assert is_one(sum(idems))
  return quorings, projs
end

################################################################################
#
#  Decomposing semisimple rings
#
################################################################################

function decompose_semisimple_p_ring(R::FiniteRing)
  @assert is_prime(characteristic(R))
  RtoA = isomorphism(MatAlgebra, R)
  A = codomain(RtoA)
  dec = decompose(A)
  rngs = FiniteRing[]
  projs = FiniteRingHom[]
  for (B, mB) in dec
    S, StoB = finite_ring(B)
    h = hom(R, S, [preimage(StoB, mB\(RtoA(x))) for x in _zgens(R)])#, y -> AtoRs(mB(StoB(y))))
    g = FiniteRingHom(S, R, false, hom(underlying_abelian_group(S), underlying_abelian_group(R), [data(preimage(RtoA, mB(StoB(y)))) for y in _zgens(S)]))
    h.g = g
    push!(rngs, S)
    push!(projs, h)
  end
  @assert is_one(sum(preimage(p, one(D)) for (D, p) in zip(rngs, projs)))
  return rngs, projs
end

################################################################################
#
#  Center
#
################################################################################

function _rgens(R::FiniteRing)
  r = get_attribute(R, :rgens, nothing)
  if r === nothing
    return _zgens(R)
  end
  return r
end

@doc raw"""
    center(R::FiniteRing) -> FiniteRing, FiniteRingHom

Given a finite ring $R$, return a finite ring $C$ together with an injective ring homomorphism $C \to R$ with image equal to the center of $R$.

# Examples

```jldoctest
julia> R, _ = finite_ring(matrix_algebra(GF(2), 2));

julia> C, f = center(R);

julia> C
Finite ring with additive group
  isomorphic to Z/2
  and with 1 generator and 1 relation
```
"""
@attr Tuple function center(R::FiniteRing)
  z = _rgens(R)
  n = length(z)
  A = underlying_abelian_group(R)
  D, _, injs = biproduct([A for i in 1:n]...)
  imgs = elem_type(D)[]
  for a in gens(A)
    b = FiniteRingElem(R, a)
    push!(imgs, sum(injs[i](data(b * z[i] - z[i] * b)) for i in 1:length(injs)))
  end
  _K, KtoA = kernel(hom(A, D, imgs))
  K, StoK = snf(_K)
  KtoA = StoK * KtoA
  mult = FinGenAbGroupHom[]
  for k in gens(K)
    h = hom(K, K, [preimage(KtoA, data(FiniteRingElem(R, KtoA(k)) * FiniteRingElem(R, KtoA(l)))) for l in gens(K)])
    push!(mult, h)
  end
  Z = FiniteRing(K, mult)
  ZtoR = FiniteRingHom(Z, R, true, hom(K, A, [KtoA(data(x)) for x in _zgens(Z)]))
  set_attribute!(Z, :is_commutative => true)
  return Z, ZtoR
end

@doc raw"""
    central_primitive_idempotents(R::FiniteRing) -> Vector{FiniteRingElem}

Given a finite ring $R$, return the set of orthgonal central primitive idempotents of $R$.

# Examples

```jldoctest; filter = r"Finite ring element \[.*\]"
julia> R = finite_ring([6, 6], [ZZ[1 0; 0 0], ZZ[0 0; 0 1]]); # Z/6Z x Z/6Z

julia> central_primitive_idempotents(R)
4-element Vector{FiniteRingElem}:
 Finite ring element [0, 3]
 Finite ring element [3, 0]
 Finite ring element [4, 0]
 Finite ring element [0, 4]
```
"""
function central_primitive_idempotents(R::FiniteRing)
  return _central_idempotents(R)
end

function _central_idempotents(R::FiniteRing)
  prings, projs = decompose_into_p_rings(R)
  res = elem_type(R)[]
  for i in 1:length(prings)
    S = prings[i]
    c = _central_idempotents_pring(S)
    for cc in c
      push!(res, preimage(projs[i], cc))
    end
  end
  return res
end

function _central_idempotents_pring(R::FiniteRing)
  C, CtoR = center(R)
  J = radical(C)
  Q, CtoQ = quo(C, J)
  rngs, projs = decompose_semisimple_p_ring(Q)
  res = elem_type(R)[]
  for i in 1:length(rngs)
    e = preimage(CtoQ, preimage(projs[i], one(rngs[i])))
    e = _lift_idempotent(e)
    push!(res, CtoR(e))
  end
  return res
end

function _lift_idempotent(x)
  # assume that x is idempotent modulo a nilpotent ideal
  f(a) = 3*a^2 - 2 * a^3
  xx = f(x)
  i = 0
  while xx != x
    i += 1
    x = xx
    xx = f(x)
    i > 100 && error("Error in idempotent lifting: nilpotency index too large?")
  end
  @assert x^2 == x
  return x
end

function _quotient_ring_from_quotient_group(R::FiniteRing, f)
  H = codomain(f)
  @assert domain(f) === underlying_abelian_group(R)
  gH = gens(H)
  mult = FinGenAbGroupHom[]
  for k in gH
    h = hom(H, H, [f(data(FiniteRingElem(R, f\k) * FiniteRingElem(R, f\l))) for l in gH])
    push!(mult, h)
  end
  S = FiniteRing(H, mult)
  RtoS = FiniteRingHom(R, S, true, f)
  return S, RtoS
end

function _quotient_ring_from_central_idempotent(R::FiniteRing, e::FiniteRingElem)
  A = underlying_abelian_group(R)
  ee = one(R) - e
  S = [data(z * ee) for z in _zgens(R)] # generators for the complement
  Q, AtoQ = quo(A, S)
  QQ, QQtoQ = snf(Q)
  QtoQQ = inv(QQtoQ)
  S, RtoS = _quotient_ring_from_quotient_group(R, AtoQ * QtoQQ)
  # we also build the non-unitary section
  SS = [data(z * e) for z in _zgens(R)]
  B, BtoA = sub(A, SS)
  g = FiniteRingHom(S, R, false, inv(BtoA * AtoQ * QtoQQ) * BtoA)
  RtoS.g = g
  return S, RtoS
end

@attr Tuple function decompose_into_indecomposable_rings(R::AbstractAssociativeAlgebra)
  ZR, ZRtoR = center(R)
  J = radical(ZR)
  B, AtoB = quo(ZR, J)
  idems = central_primitive_idempotents(B)
  idemsR = ZRtoR.(_lift_idempotent.(preimage.(Ref(AtoB), idems)))
  # want the projections
  t = [_subalgebra(R, e) for e in idemsR]
  rngs = first.(t)
  re = []
  for ((S, StoR), e) in zip(t, idemsR)
    bmat = basis_matrix([has_preimage_with_preimage(StoR, x*e)[2] for x in basis(R)])
    invbmat = basis_matrix([StoR(x) for x in basis(S)])
    push!(re, hom(R, S, bmat, invbmat; check = false))
  end
  return rngs, identity.(re)
end

@doc raw"""
    decompose_into_indecomposable_rings(R::FiniteRing)
                                    -> Vector{FiniteRing}, Vector{FiniteRingHom}

Given a finite ring $R$, return a list of indecomposable rings $S$ and a list of projections $R \to S$, such that $R$ is the direct product of these rings.

# Examples

```jldoctest
julia> R = finite_ring([6, 6], [ZZ[1 0; 0 0], ZZ[0 0; 0 1]]); # Z/6Z x Z/6Z

julia> rings, projections = decompose_into_indecomposable_rings(R);

julia> length(rings)
4
```
"""
@attr Tuple function decompose_into_indecomposable_rings(R::FiniteRing)
  es = _central_idempotents(R)
  rngs = FiniteRing[]
  projs = FiniteRingHom[]
  for e in es
    S, RtoS = _quotient_ring_from_central_idempotent(R, e)
    push!(rngs, S)
    push!(projs, RtoS)
  end
  return rngs, projs
end

@doc raw"""
    is_indecomposable(R::FiniteRing) -> Bool

Return whether the finite ring $R$ is indecomposable.

# Examples

```jldoctest
julia> R = finite_ring([6, 6], [ZZ[1 0; 0 0], ZZ[0 0; 0 1]]); # Z/6Z x Z/6Z

julia> is_indecomposable(R)
false

julia> R, _ = finite_ring(matrix_algebra(GF(2), 2));

julia> is_indecomposable(R)
true
```
"""
function is_indecomposable(R::FiniteRing)
  return length(first(decompose_into_indecomposable_rings(R))) == 1
end
