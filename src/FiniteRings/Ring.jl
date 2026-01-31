################################################################################
#
#  Basics
#
################################################################################

base_ring(R::FiniteRing) = Union{}

base_ring_type(::Type{FiniteRing}) = typeof(Union{})

elem_type(::Type{FiniteRing}) = FiniteRingElem

parent_type(::Type{FiniteRingElem}) = FiniteRing

parent(x::FiniteRingElem) = x.parent

Base.copy(x::FiniteRingElem) = x

function data(a::FiniteRingElem)
  return a.a
end

function underlying_abelian_group(R::FiniteRing)
  return R.A
end

elementary_divisors(R::FiniteRing) = elementary_divisors(underlying_abelian_group(R))

function Base.deepcopy_internal(x::FiniteRingElem, stackdict::IdDict)
  return FiniteRingElem(parent(x), Base.deepcopy_internal(data(x), stackdict))
end

function Base.hash(x::FiniteRingElem, h::UInt)
  return Base.hash(data(x), h)
end

function order(R::FiniteRing)
  return order(underlying_abelian_group(R))
end

function characteristic(R::FiniteRing)
  return exponent(underlying_abelian_group(R))
end

is_finite(R::FiniteRing) = true

# Generators of R as a Z-module, that is, the underlying
# concrete abelian group
@attr Vector{FiniteRingElem} function _zgens(R::FiniteRing)
  A = underlying_abelian_group(R)
  return FiniteRingElem.(Ref(R), gens(A))
end

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
  Hecke.show_snf_structure(io, snf(A)[1])
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

function finite_ring(A::AbstractAssociativeAlgebra)
  F = base_ring(A)
  @assert is_finite(F) && absolute_degree(F) == 1
  p = characteristic(F)
  n = dim(A)
  AA = abelian_group([characteristic(F) for i in 1:n])
  B = basis(A)
  mult = FinGenAbGroupHom[]
  for b in B
    push!(mult, hom(AA, AA, lift.(Ref(ZZ), representation_matrix(b))))
  end
  R = FiniteRing(AA, mult)
  inv = _hom(A, R, x -> lift(ZZ, x), [R(lift.(Ref(ZZ), Hecke.coefficients(x))) for x in basis(A)])
  f = _hom(R, A, [A(F.(Hecke._eltseq(x.a.coeff))) for x in _zgens(R)]; inverse = inv)
  for i in 1:10
    r = rand(R)
    s = rand(R)
    @assert f(r) * f(s) == f(r * s)
    @assert f(r) + f(s) == f(r + s)
    @assert preimage(f, f(r)) == r
  end
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
  hh = r -> h(data(r))
  hhinv = m -> FiniteRingElem(MR, hinv(m))

  # Let's compute the radical (chain)
  _J = radical(R)
  rad_chain = [_ideal_to_matrix_ring_ideal(R, M, MR, _J, hhinv)]
  while !is_zero(_J)
    _J = _J *_J
    push!(rad_chain, _ideal_to_matrix_ring_ideal(R, M, MR, _J, hhinv))
  end
  set_attribute!(MR, :radical => rad_chain[1])
  set_attribute!(MR, :radical_chain => rad_chain)
  return MR, hh, hhinv
end

function finite_ring(A::Hecke.AbsOrdQuoRing)
  AA, AAtoA, AtoAA = abelian_group(A)
  B = gens(AA)
  mult = FinGenAbGroupHom[]
  for b in B
    push!(mult, hom(AA, AA, [AtoAA(AAtoA(b) * AAtoA(a)) for a in B]))
  end
  R = FiniteRing(AA, mult)
  inv = _hom(A, R, [FiniteRingElem(R, AtoAA(A(x))) for x in basis(base_ring(A))])
  f = _hom(R, A, [AAtoA(x.a) for x in _zgens(R)]; inverse = inv)
  #fw = x -> AAtoA(x.a)
  #bw = x -> FiniteRingElem(R, AtoAA(x))
  for i in 1:10
    r = rand(R)
    s = rand(R)
    @assert f(r) * f(s) == f(r * s)
    @assert f(r) + f(s) == f(r + s)
    @assert preimage(f, f(r)) == r
  end
  return R, f
end

################################################################################
#
#  Maximal p-subring
#
################################################################################

function maximal_psubring(R::FiniteRing, p)
  A = underlying_abelian_group(R)
  B, BtoA = sylow_subgroup(A, p)
  homss = FinGenAbGroupHom[]
  for b in gens(B)
    h = hom(B, B, [preimage(BtoA, data(FiniteRingElem(R, BtoA(b)) * FiniteRingElem(R, BtoA(bb)))) for bb in gens(B)])
    push!(homss, h)
  end
  S = FiniteRing(B, homss)
  return S, FiniteRingHom(S, R, x -> FiniteRingElem(R, BtoA(data(x))), y -> FiniteRingElem(S, preimage(BtoA, data(y))))
end

@attr Tuple function decompose_into_prings(R::FiniteRing)
  ps = prime_divisors(characteristic(R))
  if length(ps) == 1
    return [R], [FiniteRingHom(R, R, x -> x, x -> x)], [FiniteRingHom(R, R, x -> x, x -> x)]
  end
  idems = elem_type(R)[]
  subs = Tuple{FiniteRing, FiniteRingHom}[]
  for p in ps
    S, StoR = maximal_psubring(R, p)
    push!(idems, StoR(one(S)))
    push!(subs, (S, StoR))
  end
  proj = [FiniteRingHom(R, subs[i][1], x-> preimage(subs[i][2], idems[i] * x), y -> subs[i][2](y)) for i in 1:length(ps)]
  return first.(subs), proj, [x[2] for x in subs]
end

################################################################################
#
#  Decomposing semisimple rings
#
################################################################################

function decompose_semisimple_pring(R::FiniteRing)
  @assert is_prime(characteristic(R))
  A, AtoRs = isomorphism(MatAlgebra, R)
  dec = decompose(A)
  rngs = FiniteRing[]
  projs = FiniteRingHom[]
  for (B, mB) in dec
    S, StoB = finite_ring(B)
    h = FiniteRingHom(R, S, x -> preimage(StoB, mB\(preimage(AtoRs, x))), y -> AtoRs(mB(StoB(y))))
    push!(rngs, S)
    push!(projs, h)
  end
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
  ZtoR = FiniteRingHom(Z, R, x -> FiniteRingElem(R, KtoA(data(x))), y -> FiniteRingElem(Z, preimage(KtoA, data(y))))
  set_attribute!(Z, :is_commutative => true)
  return Z, ZtoR
end

function _central_idempotents(R::FiniteRing)
  prings, _, injs = decompose_into_prings(R)
  res = elem_type(R)[]
  for i in 1:length(prings)
    S = prings[i]
    c = _central_idempotents_pring(S)
    for cc in c
      push!(res, injs[i](cc))
    end
  end
  return res
end

function _central_idempotents_pring(R::FiniteRing)
  C, CtoR = center(R)
  J = radical(C)
  Q, CtoQ = quo(C, J)
  rngs, projs = decompose_semisimple_pring(Q)
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
    if i > 100
      error("asds")
    end
  end
  @assert x^2 == x
  return x
end

function _subring_from_subgroup(R::FiniteRing, f)
  H = domain(f)
  gH = gens(H)
  mult = FinGenAbGroupHom[]
  for k in gH
    h = hom(H, H, [preimage(f, data(FiniteRingElem(R, f(k)) * FiniteRingElem(R, f(l)))) for l in gH])
    push!(mult, h)
  end
  Z = FiniteRing(H, mult)
  ZtoR = FiniteRingHom(Z, R, x -> FiniteRingElem(R, f(data(x))), y -> FiniteRingElem(Z, preimage(f, data(y))))
  return Z, ZtoR
end

function _subring_from_central_idempotent(R::FiniteRing, e::FiniteRingElem)
  A = underlying_abelian_group(R)
  S = [data(z * e) for z in _zgens(R)]
  _B, BtoA = sub(A, S)
  B, Bto_B = snf(_B)
  return _subring_from_subgroup(R, Bto_B * BtoA)
end

@attr Tuple function decompose_into_indecomposable_rings(R::Hecke.AbstractAssociativeAlgebra)
  ZR, ZRtoR = center(R)
  J = radical(ZR)
  B, AtoB = quo(ZR, J)
  idems = Hecke.central_primitive_idempotents(B)
  idemsR = ZRtoR.(_lift_idempotent.(preimage.(Ref(AtoB), idems)))
  # want the projections
  t = [Hecke._subalgebra(R, e) for e in idemsR]
  rngs = first.(t)
  re = []
  for ((S, StoR), e) in zip(t, idemsR)
    bmat = basis_matrix([has_preimage_with_preimage(StoR, x*e)[2] for x in basis(R)])
    invbmat = basis_matrix([StoR(x) for x in basis(S)])
    push!(re, hom(R, S, bmat, invbmat; check = false))
  end
  return rngs, identity.(re)
end

@attr Tuple function decompose_into_indecomposable_rings(R::FiniteRing)
  es = _central_idempotents(R)
  rngs = FiniteRing[]
  projs = FiniteRingHom[]
  for e in es
    S, StoR = _subring_from_central_idempotent(R, e)
    push!(rngs, S)
    proj = FiniteRingHom(R, S, x -> preimage(StoR, e * x), y -> StoR(y))
    push!(projs, proj)
  end
  return rngs, projs
end
