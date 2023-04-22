
######################################################################
#
#    Q/nZ interface
#
######################################################################

struct QmodnZ <: GrpAb
  trivialmodulus::Bool
  n::ZZRingElem
  d::ZZRingElem

  function QmodnZ(; cached::Bool = true)
    return get_cached!(QmodnZID, (true, ZZRingElem(1), ZZRingElem(1)), cached) do
      return new(true, ZZRingElem(1), ZZRingElem(1))
    end
  end

  function QmodnZ(n::ZZRingElem; cached::Bool = true)
    if isone(abs(n))
      return QmodnZ(cached = cached)
    else
      return get_cached!(QmodnZID, (false, ZZRingElem(n), ZZRingElem(1)), cached) do
        return new(false, ZZRingElem(n), ZZRingElem(1))
      end
    end
  end

  function QmodnZ(n::QQFieldElem; cached::Bool = true)
    if is_integral(n)
      return QmodnZ(numerator(n), cached = cached)
    else
      return get_cached!(QmodnZID, (false, numerator(n), denominator(n)), cached) do
        return new(false, numerator(n), denominator(n))
      end
    end
  end
end

const QmodnZID = Dict{Tuple{Bool, ZZRingElem, ZZRingElem}, QmodnZ}()

function show(io::IO, G::QmodnZ)
  if G.trivialmodulus
    print(io, "Q/Z")
  else
    if isone(G.d)
      print(io, "Q/", G.n, "Z")
    else
      print(io, "Q/(", G.n, "/", G.d, ")Z")
    end
  end
end

modulus(T::QmodnZ) = T.n

struct QmodnZElem <: GrpAbElem
  elt::QQFieldElem
  parent::QmodnZ

  function QmodnZElem(R::QmodnZ, a::QQFieldElem)
    if R.trivialmodulus
      q = QQFieldElem(mod(numerator(a), denominator(a)), denominator(a))
    else
      q = QQFieldElem(mod(R.d * numerator(a), R.n * denominator(a)), R.d * denominator(a))
    end
    @assert is_integral(R.d * (q - a)) && iszero(mod(numerator(R.d * (q - a)), R.n))
    return new(q, R)
  end
end

function show(io::IO, a::QmodnZElem)
  G = parent(a)
  if G.trivialmodulus
    print(io, "$(a.elt) + Z")
  else
    if isone(G.d)
      print(io, "$(a.elt) + ", G.n, "Z")
    else
      print(io, "$(a.elt) + (", G.n, "/", G.d, ")Z")
    end
  end
end

iszero(x::QmodnZElem) = iszero(x.elt)

function +(a::QmodnZElem, b::QmodnZElem)
  return QmodnZElem(a.parent, a.elt + b.elt)
end

function *(a::ZZRingElem, b::QmodnZElem)
  return QmodnZElem(b.parent, a*b.elt)
end

function *(a::Integer, b::QmodnZElem)
  return QmodnZElem(b.parent, a*b.elt)
end

function divexact(a::QmodnZElem, b::ZZRingElem)
  iszero(b) && throw(DivideError())
  return QmodnZElem(a.parent, a.elt // b)
end

function divexact(a::QmodnZElem, b::Integer)
  iszero(b) && throw(DivideError())
  return QmodnZElem(a.parent, a.elt // b)
end

function root_of_one(::Type{QmodnZ}, n::ZZRingElem)
  return QmodnZElem(QmodnZ(), QQFieldElem(1, n))
end

function inv(a::QmodnZElem)
  return QmodnZElem(a.parent, -(a.elt))
end

function parent(x::QmodnZElem)
  return x.parent
end

elem_type(::Type{QmodnZ}) = QmodnZElem

function order(a::QmodnZElem)
  if parent(a).trivialmodulus
    return denominator(a.elt)
  else
    throw(NotImplemented())
  end
end

(R::QmodnZ)(a::ZZRingElem) = QmodnZElem(R, QQFieldElem(a))
(R::QmodnZ)(a::Integer) = QmodnZElem(R, QQFieldElem(a))
(R::QmodnZ)(a::QQFieldElem) = QmodnZElem(R, a)
(R::QmodnZ)(a::Rational) = QmodnZElem(R, QQFieldElem(a))

function Base.:(==)(a::QmodnZ, b::QmodnZ)
  return a.n == b.n && a.d == b.d
end

function Base.:(==)(a::QmodnZElem, b::QmodnZElem)
  if parent(a).trivialmodulus
    return is_integral(a.elt - b.elt)
  else
    z = a.elt - b.elt
    d = denominator(z)
    return isone(d) && iszero(mod(numerator(z), modulus(parent(a))))
  end
end

function Base.hash(a::QmodnZElem, h::UInt)
  if parent(a).trivialmodulus
    return hash(a.elt, h)
  end
  error("not implemented")
end

for T in [ZZRingElem, Integer, QQFieldElem, Rational]
  @eval begin
    Base.:(==)(a::$T, b::QmodnZElem) = parent(b)(a) == b

    Base.:(==)(a::QmodnZElem, b::$T) = b == a
  end
end

lift(a::QmodnZElem) = a.elt

################################################################################
#
#   Dual
#
################################################################################


mutable struct GrpAbFinGenToQmodnZ <: Map{GrpAbFinGen, QmodnZ,
                                            HeckeMap, GrpAbFinGenToQmodnZ}
  header::MapHeader{GrpAbFinGen, QmodnZ}

  function GrpAbFinGenToQmodnZ(G::GrpAbFinGen, QZ::QmodnZ, image)
    z = new()
    z.header = MapHeader(G, QZ, image)
    return z
  end
end

function kernel(mp::GrpAbFinGenToQmodnZ)
  G = domain(mp)
  QmodnZ = codomain(mp)
  n = exponent(G)
  C = abelian_group(ZZRingElem[n])
  gensG = gens(G)
  imgs = Vector{GrpAbFinGenElem}()
  if QmodnZ.trivialmodulus
    for x in gensG
      imgx = lift(mp(x))
      o = divexact(n, denominator(imgx))
      push!(imgs, numerator(imgx)*o*C[1])
    end
  end
  mpk = hom(gensG, imgs)
  return kernel(mpk)
end

#TODO: technically, dual Z could be Q/Z ...
@doc raw"""
    dual(G::GrpAbFinGen) -> GrpAbFinGen, Map

Computes the dual group, i.e. $hom(G, Q/Z)$ as an
abstract group. The map can be used to obtain actual homomorphisms.
It assumes that the group is finite.
"""
function dual(G::GrpAbFinGen)
  T, mT = torsion_subgroup(G)
  u = root_of_one(QmodnZ, exponent(T))
  return dual(G, u)
end

function dual(G::GrpAbFinGen, u::QmodnZElem)
  o = order(u)
  H = abelian_group(ZZRingElem[o])
  QZ = parent(u)
  R, phi = hom(G, H)
  R::GrpAbFinGen
  ex = MapFromFunc(x -> x[1]*u, y -> H(ZZRingElem[numerator(y.elt) * div(o, denominator(y.elt))]), H, parent(u))
  local mu
  let phi = phi, G = G, QZ = QZ, u = u
    function mu(r::GrpAbFinGenElem)
      f = phi(r)
      return GrpAbFinGenToQmodnZ(G, QZ, x -> f(x)[1]*u)
    end
  end

  local nu
  let ex = ex, phi = phi
    function nu(f::Map)
      g = GrpAbFinGenMap(f*inv(ex))
      return preimage(phi, g)
    end
  end
  return R, MapFromFunc(mu, nu, R, MapParent(G, parent(u), "homomorphisms"))
end

parent(f::GrpAbFinGenToQmodnZ) = MapParent(domain(f), codomain(f), "homomorphisms")

function restrict(f::GrpAbFinGenToQmodnZ, U::GrpAbFinGen)
  G = domain(f)
  fl, mU = is_subgroup(U, G)
  @assert fl
#  z = QmodnZ(exponent(U))
  h = GrpAbFinGenToQmodnZ(U, codomain(f), x->(mU*f)(x))
  return h
end

#
# used in RCF for knot computation
#
#TODO: figure out how to do this properly, ie. how this should interact
#      with the other cohomology
function H2_G_QmodZ(G::GrpAbFinGen)
  s, ms = snf(G)
  e = elementary_divisors(s)
  @assert ngens(s) == length(e)
  r = ZZRingElem[]
  for i=1:length(e)
    for j=i+1:length(e)
      push!(r, gcd(e[i], e[j]))
    end
  end
  return abelian_group(r)
end

function H2_G_QmodZ_restriction(G::GrpAbFinGen, U::Vector{GrpAbFinGen})
  S, mS = snf(G)
  e = elementary_divisors(S)
  @assert ngens(S) == length(e)
  r = ZZRingElem[gcd(e[i], e[j]) for i=1:length(e) for j=i+1:length(e)]
  H = abelian_group(r)
  D, mD = dual(H)
  phi = []
  #= theory:
    H^2(G, Q/Z) = G hat G = Dual(prod C_(gcd(..))) as above
    the cocycle (and the iso!!!) is given as
    H = prod C_i
    chi in Dual()
    sigma(g, h)  = chi((g[i]*h[j] - g[j]*h[i])) (i<j)
    sigma should be unique if g, h run through the generattors

    Let chi in Dual(H)  and U < G a subgrooup
    Dual(G) -> Dual(U) is the composition: U->G 
  =#
  #function chi(sigma) #in H return the cocycle
  #  return (g, h) -> mD(sigma)(H([g[i]*h[j] - g[j]*h[i] for i=1:length(e) for j=i+1:length(e)]))
  #end
  # (H) is generated by (g_i, g_j)_{i<j}
  for u = U
    fl, mp = is_subgroup(u, G)
    @assert fl
    gs = map(x->mS(mp(x)), gens(u))
    s, ms = sub(H, [H([gs[i][l]*gs[j][k] - gs[i][k]*gs[j][l] for l=1:length(e) for k=l+1:length(e)]) for i=1:length(gs) for j=i+1:length(gs)])
    d, md = dual(s)
    ms = hom(D, d, [preimage(md, restrict(mD(x), s)) for x = gens(D)])
    push!(phi, ms)
  end
  return phi
end

