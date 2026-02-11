################################################################################
#
#  Ideals
#
################################################################################

function Base.show(io::IO, A::FiniteRingIdeal)
  print(io, "Ideal of finite ring")
end

function Base.show(io::IO, ::MIME"text/plain", I::FiniteRingIdeal)
  io = AbstractAlgebra.pretty(io)
  println(io, "Ideal of")
  print(io, AbstractAlgebra.Indent())
  println(AbstractAlgebra.terse(io), AbstractAlgebra.Lowercase(), base_ring(I))
  print(io, "with additive group isomorphic to ")
  show_snf_structure(io, snf(underlying_abelian_group(I))[1])
  #print(io, "and with ", ItemQuantity(ncols(rels(A)), "generator"), " and ", ItemQuantity(nrows(rels(A)), "relation"))
  print(io, AbstractAlgebra.Dedent())
end

underlying_abelian_group(I::FiniteRingIdeal) = I.B

_embedding(I::FiniteRingIdeal) = I.BtoA

base_ring(I::FiniteRingIdeal) = I.R

order(I::FiniteRingIdeal) = order(underlying_abelian_group(I))

# Basics
is_zero(I::FiniteRingIdeal) = is_trivial(underlying_abelian_group(I))

function Base.in(x::FiniteRingElem, I::FiniteRingIdeal)
  fl, = has_preimage_with_preimage(_embedding(I), data(x))
  return fl
end

function Base.issubset(I::FiniteRingIdeal, J::FiniteRingIdeal)
  return all(x -> in(x, J), _zgens(I))
end

function Base.:(==)(I::FiniteRingIdeal, J::FiniteRingIdeal)
  return all(in(J), _zgens(I)) && all(in(I), _zgens(J))
end

function _ideal_zgens(R::FiniteRing, v::Vector{FiniteRingElem}; side, check::Bool = true)
  S, StoA = sub(R.A, [x.a for x in v])
  SS, SStoS = snf(S)
  I = FiniteRingIdeal(R, SS, SStoS * StoA)
  if check
    _test_ideal_sidedness(I, side)
  end
  return I
end

@doc raw"""
    additive_generators(I::FiniteRingIdeal) -> Vector{FiniteRingElem}

Return additive generators of the ideal $I$.

# Examples

```jldoctest
julia> R = finite_ring([6, 6], [ZZ[1 0; 0 0], ZZ[0 0; 0 1]]); # Z/6Z x Z/6Z

julia> I = ideal(R, R([1, 0]); side = :left)
Ideal of
  finite ring
  with additive group isomorphic to Z/6

julia> additive_generators(I)
1-element Vector{FiniteRingElem}:
 Finite ring element [5, 0]
```
"""
function additive_generators(I::FiniteRingIdeal)
  return _zgens(I)
end

@attr Vector{FiniteRingElem} function _zgens(I::FiniteRingIdeal)
  R = base_ring(I)
  m = _embedding(I)
  B = underlying_abelian_group(I)
  return FiniteRingElem.(Ref(R), m.(gens(B)))
end

################################################################################
#
#  Creation
#
################################################################################

function Base.:(*)(n::IntegerUnion, R::FiniteRing)
  return _ideal_zgens(R, [n * a for a in _zgens(R)]; side = :twosided, check = false)
end

Base.:(*)(R::FiniteRing, n::IntegerUnion) = n * R

@doc raw"""
    radical(R::FiniteRing) -> FiniteRingIdeal

Return the Jacobson radical of $R$. Currently, it is only implemented for $p$-rings.

# Examples

```jldoctest
julia> R, = finite_ring(GF(2)[small_group(4, 2)]);

julia> J = radical(R);

julia> additive_generators(J)
3-element Vector{FiniteRingElem}:
 Finite ring element [1, 0, 0, 1]
 Finite ring element [0, 1, 0, 1]
 Finite ring element [0, 0, 1, 1]
```
"""
@attr FiniteRingIdeal function radical(R::FiniteRing)
  if is_one(order(R))
    return _ideal_zgens(R, [one(R)]; check = false, side = :twosided)
  end
  fl, e, p = is_prime_power_with_data(order(R))
  !fl && error("Radical implemented only for rings of prime power order")
  # If the order is a power of p, then p is nilpotent. So the radical contains
  # p * R, and we can look at R/p*R, which is an Fp-algebra.
  Q, RtoQ = quo(underlying_abelian_group(R), p)
  G = gens(Q)
  @assert length(G) == length(elementary_divisors(Q))
  # G is a basis of Q
  liftgens = preimage.(Ref(RtoQ), gens(Q))
  mats = ZZMatrix[]
  for g in liftgens
    push!(mats, reduce(vcat, [RtoQ(data(FiniteRingElem(R, g) * FiniteRingElem(R, h))).coeff for h in liftgens]))
  end
  F = GF(p; cached = false, check = false)
  J = radical(matrix_algebra(F, map_entries.(Ref(F), mats); isbasis = true)) # isbasis = true is important
  BJ = basis(J)
  ss = FiniteRingElem[]
  for b in BJ
    push!(ss, FiniteRingElem(R, preimage(RtoQ, Q(lift.(Ref(ZZ), coefficients(b))))))
  end
  # Return J + p*R
  return _ideal_zgens(R, append!(ss, _zgens(p * R)); side = :twosided, check = false)
end

################################################################################
#
#  Multiplication
#
################################################################################

function Base.:(*)(I::FiniteRingIdeal, J::FiniteRingIdeal)
  @assert base_ring(I) === base_ring(J)
  return _ideal_zgens(base_ring(I), [a * b for a in _zgens(I) for b in _zgens(J)]; side = :twosided, check = false)
end

################################################################################
#
#  Creation
#
################################################################################

function ideal(R::FiniteRing, g::Vector; side)
  idzgens = elem_type(R)[]
  @req side in (:left, :right, :twosided) "side keyword (:$(side)) must be one of :left, :right or :twosided"
  for el in g
    for b in _zgens(R)
      if side == :left || side == :twosided
        bel = b * el
        if side == :twosided
          for bb in _zgens(R)
            push!(idzgens, bel * bb)
          end
        else
          @assert side == :left
          # side == :left
          push!(idzgens, bel)
        end
      else
        @assert side == :right
        push!(idzgens, el * b)
      end
    end
  end
  return _ideal_zgens(R, idzgens; side, check = false)
end

left_ideal(A::FiniteRing, x...; kw...) = ideal(A, x...; side = :left, kw...)

right_ideal(A::FiniteRing, x...; kw...) = ideal(A, x...; side = :right, kw...)

twosided_ideal(A::FiniteRing, x...; kw...) = ideal(A, x...; side = :twosided, kw...)

Base.:(*)(A::FiniteRing, x::NCRingElement) = left_ideal(A, x)

#Base.:(*)(A::FiniteRing, x::RingElement) = left_ideal(A, x)

Base.:(*)(x::NCRingElement, A::FiniteRing) = right_ideal(A, x)

#Base.:(*)(x::RingElement, A::FiniteRing) = right_ideal(A, x)

################################################################################
#
#  Test sidedness
#
################################################################################

################################################################################
#
#  Test right/left
#
################################################################################

function _test_ideal_sidedness(a::FiniteRingIdeal, side::Symbol)
  R = base_ring(a)
  ba = _zgens(a)
  Rb = _zgens(R)
  t = zero(R)
  for b in Rb
    for c in ba
      if side === :left || side === :twosided
        t = mul!(t, b, c)
        if !(t in a)
          return false
        end
      end
      if side === :right || side === :twosided
        t = mul!(t, c, b)
        if !(t in a)
          return false
        end
      end
    end
  end
  return true
end

################################################################################
#
#  Quotient ring
#
################################################################################

function quo(R::FiniteRing, J::FiniteRingIdeal; check::Bool = true)
  @req base_ring(J) == R "Ideal of the wrong ring"
  check && @req _test_ideal_sidedness(J, :twosided) "Ideal must be a two-sided ideal"
  gensJ = _zgens(J)
  gensJinI = FinGenAbGroupElem[]
  Q, RtoQ = quo(R.A, J.BtoA.(gens(J.B)))
  SQ, SQtoQ = snf(Q)
  Q, RtoQ = SQ, RtoQ * inv(SQtoQ)
  gensQ = gens(Q)
  homs = FinGenAbGroupHom[]
  for a in gensQ
    H = FinGenAbGroupElem[]
    for x in gensQ
      push!(H, RtoQ((FiniteRingElem(R, RtoQ\a) * FiniteRingElem(R, RtoQ\x)).a))
    end
    push!(homs, hom(Q, Q, H))
  end
  quoring = FiniteRing(Q, homs)

  proj = FiniteRingHom(R, quoring, true, RtoQ)
  return quoring, proj
end


function quo(I::FiniteRingIdeal, J::FiniteRingIdeal)
  gensJ = _zgens(J)
  R = I.R
  @assert I.R === J.R
  gensJinI = FinGenAbGroupElem[]
  for g in gensJ
    fl, x = has_preimage_with_preimage(I.BtoA, g.a)
    !fl && error("Ideal not containing second argument")
    push!(gensJinI, x)
  end
  Q, ItoQ = quo(I.B, gensJinI)
  SQ, SQtoQ = snf(Q)
  Q, ItoQ = SQ, ItoQ * inv(SQtoQ)
  gensQ = gens(Q)
  homs = FinGenAbGroupHom[]
  for a in gensQ
    H = FinGenAbGroupElem[]
    for x in gensQ
      push!(H, ItoQ(I.BtoA\((FiniteRingElem(R, I.BtoA(ItoQ\a)) * FiniteRingElem(R, I.BtoA(ItoQ\x))).a)))
    end
    push!(homs, hom(Q, Q, H))
  end
  quoring = FiniteRing(Q, homs)
  pr = x -> FiniteRingElem(quoring, ItoQ(I.BtoA\(x.a)))
  lf = y -> FiniteRingElem(R, I.BtoA(ItoQ\(y.a)))
  return quoring, MapFromFunc(R, quoring, pr, lf)
end

################################################################################
#
#  Random
#
################################################################################

function Base.rand(I::FiniteRingIdeal)
  x = FiniteRingElem(base_ring(I), I.BtoA(rand(I.B)))
  @assert x in I
  return x
end
