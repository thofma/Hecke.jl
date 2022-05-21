
######################################################################
#
#    Q/nZ interface
#
######################################################################

mutable struct QmodnZ <: GrpAb
  trivialmodulus::Bool
  n::fmpz
  d::fmpz

  function QmodnZ()
    z = new()
    z.n = fmpz(1)
    z.d = fmpz(1)
    z.trivialmodulus = true
    return z
  end

  function QmodnZ(n::fmpz)
    z = new()
    if isone(abs(n))
      return QmodnZ()
    else
      z = new()
      z.trivialmodulus = false
      z.n = abs(n)
      z.d = one(FlintZZ)
      return z
    end
  end

  function QmodnZ(n::fmpq)
    if is_integral(n)
      return QmodnZ(numerator(n))
    else
      z = new()
      z.trivialmodulus = false
      z.n = numerator(n)
      z.d = denominator(n)
      return z
    end
  end

end

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
  elt::fmpq
  parent::QmodnZ

  function QmodnZElem(R::QmodnZ, a::fmpq)
    if R.trivialmodulus
      q = fmpq(mod(numerator(a), denominator(a)), denominator(a))
    else
      q = fmpq(mod(R.d * numerator(a), R.n * denominator(a)), R.d * denominator(a))
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

function *(a::fmpz, b::QmodnZElem)
  return QmodnZElem(b.parent, a*b.elt)
end

function *(a::Integer, b::QmodnZElem)
  return QmodnZElem(b.parent, a*b.elt)
end

function divexact(a::QmodnZElem, b::fmpz)
  iszero(b) && throw(DivideError())
  return QmodnZElem(a.parent, a.elt // b)
end

function divexact(a::QmodnZElem, b::Integer)
  iszero(b) && throw(DivideError())
  return QmodnZElem(a.parent, a.elt // b)
end

function root_of_one(::Type{QmodnZ}, n::fmpz)
  return QmodnZElem(QmodnZ(), fmpq(1, n))
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

(R::QmodnZ)(a::fmpz) = QmodnZElem(R, fmpq(a))
(R::QmodnZ)(a::Integer) = QmodnZElem(R, fmpq(a))
(R::QmodnZ)(a::fmpq) = QmodnZElem(R, a)
(R::QmodnZ)(a::Rational) = QmodnZElem(R, fmpq(a))

function Base.:(==)(a::QmodnZElem, b::QmodnZElem)
  if parent(a).trivialmodulus
    return is_integral(a.elt - b.elt)
  else
    z = a.elt - b.elt
    d = denominator(z)
    return isone(d) && iszero(mod(numerator(z), modulus(parent(a))))
  end
end

for T in [fmpz, Integer, fmpq, Rational]
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
  C = abelian_group(fmpz[n])
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
@doc Markdown.doc"""
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
  H = abelian_group(fmpz[o])
  QZ = parent(u)
  R, phi = hom(G, H)
  R::GrpAbFinGen
  ex = MapFromFunc(x -> x[1]*u, y -> H(fmpz[numerator(y.elt) * div(o, denominator(y.elt))]), H, parent(u))
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
