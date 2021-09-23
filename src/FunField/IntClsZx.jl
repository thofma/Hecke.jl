module HessMain
using Hecke
using ..HessQRModule, ..GenericRound2
import ../HessQRModule: HessQR

function GenericRound2.integral_closure(S::HessQR, F::Generic.FunctionField{T}) where {T}
  return GenericRound2._integral_closure(S, F)
end

function _gcdx(a::fmpq, b::fmpq)
  l = lcm(denominator(a), denominator(b))
  g, e, f = gcdx(numerator(a*l), numerator(b*l))
  return g//l, e, f
end

#= 
  base case:
  given
    a 0
    b c 
  where a, b, c are polynomials, deg b < deg c
  do Q[x]-col transforms and Z<x>-row transforms (HessQR) to get diagonal.

  Several steps.
  Input
  a*alpha 0
  b*beta  c*gamma
  where a, b, c in Q, alpha, beta, gamma in Z[x], primitive

  Step 1:
  alpha is a Z<x> unit, so
  ->
    a       0
    b*beta  c*gamma
  is valid row-transform

  Step 2:
    g = gcd(a, b) = ea + fb (via common denominator of a, b, g), so in particular
    a/g, b/g, e, f in Z

    more row-tranforms:
    e*beta       f          a      0           g*beta   c*f*gamma
    -b/g*beta    a/g    *   b*beta c gamma  =  0        a/g*c*gamma

    det(trans) = (ea+fb)/g * beta = beta is a Z<x> unit

  Step 3:
    Q[x] col. operations: since deg beta < deg gamma we get
    g*beta (c*f*gamma mod g*beta)
    0      a/g*c*gamma
    
  Step 4: row and col swap
    a/g*c*gamma 0
    d*delta     g*beta  (d*delta :=  (c*f*gamma mod g*beta))

    and deg delta < deg beta
  
  This is iterated until delta == 0
=#
   
function two_by_two(Q::MatElem{<:Generic.Rat{_T}}, R::PolyRing{_T}, S::HessQR) where {_T}
  @assert size(Q) == (2,2)

  Qt = base_ring(Q)
  T1 = identity_matrix(Qt, 2)
  T2 = identity_matrix(Qt, 2)
  while !iszero(Q[2,1])
    @assert all(x->isone(denominator(x, R)), Q)
    @assert iszero(Q[1,2])
    @assert degree(numerator(Q[2,1])) < degree(numerator(Q[2,2]))

    n, d = integral_split(Q[1,1], S)
    @assert isconstant(d)
    a = n.c//d.c
    Q[1,1] = a
    c = Qt(n)//Qt(d)*inv(Q[1,1])
    @assert isunit(c)
    T1[1,:] *= inv(c)
    n, d = integral_split(Q[2,1], S)
    b = n.c//d.c
    beta = Q[2,1]//b

    g, e, f = _gcdx(a, b)
    T = matrix(Qt, 2, 2, [e*beta, Qt(f), -Q[2,1]//g, Q[1,1]//g])
    Q = T*Q
    @assert iszero(Q[2,1])
    T1 = T*T1

    if iszero(Q[1,2])
      return Q, T1, T2
    end

    n, d = integral_split(Q[1,1], R)
    @assert isone(d)
    nn, d = integral_split(Q[1,2], R)
    @assert isone(d)
    @assert degree(nn) > degree(n)
    q, r = divrem(nn, n)
    
    T = matrix(Qt, 2, 2, [Qt(1), -q, Qt(0), Qt(1)])
    Q = Q*T
    T2 = T2 * T

    swap_cols!(Q, 1, 2)
    swap_cols!(T2, 1, 2)
    swap_rows!(Q, 1, 2)
    swap_rows!(T1, 1, 2)
  end

  return Q, T1, T2
end

function GenericRound2.integral_closure(Zx::FmpzPolyRing, F::Generic.FunctionField)
  Qt = base_ring(F)
  t = gen(Qt)
  S = HessQR(Zx, Qt)
  R = parent(numerator(t))
  o1 = integral_closure(S, F)
  o2 = integral_closure(R, F)
  if isdefined(o1, :trans)
    T = o1.trans
  else
    T = identity_matrix(Qt, degree(F))
  end
  if isdefined(o2, :itrans)
    T = T * o2.itrans
  end
  q, w = integral_split(T, R)
  h, T2 = Hecke._hnf_with_transform(q', :upperright)
  T = map_entries(Qt, h')
#TODO: we don't need TT2 other than to debug assertions
# make it optional? tricky to also do this in two_by_two...
  TT2 = map_entries(Qt, T2')
  TT1 = identity_matrix(Qt, degree(F))
  cnt = 0
#  @assert TT1*o1.trans*o2.itrans*TT2 == divexact(T, Qt(w))
  for i=1:degree(F)
    for j=i+1:degree(F)
      q, t1, t2 = two_by_two(T[ [i,j], [i,j]], R, S)
      T[[i,j], [i,j]] = q
      TT = identity_matrix(Qt, degree(F))
      TT[[i,j], [i,j]] = t1
      TT1 = TT*TT1
      TT[[i,j], [i,j]] = t2
      TT2 = TT2 * TT
#  @assert TT1*o1.trans*o2.itrans*TT2 == divexact(T, Qt(w))
    end
  end


  @assert isdiagonal(T)
  T = divexact(T, Qt(w))
#  @assert TT1*o1.trans*o2.itrans*TT2 == T
  # the diagonal in Q(t) is splint into a/b * alpha/beta where
  #  a/b in Q (hence a unit there)
  # and alpha, beta in Z[x] primitive, so alpha/beta is a unit in Z<x>
  for i=1:degree(F)
    n, d = integral_split(T[i,i], S)
    @assert isconstant(d)
    u = Qt(n.f)//Qt(n.g)
#    @assert n.c//d.c*u == T[i,i]
    TT2[:, i] *= Qt(d.c)*inv(Qt(n.c))
    TT1[i, :] *= inv(u)
    T[i,i] = 1
#  @assert TT1*o1.trans*o2.itrans*TT2 == T
  end

  TT1 = TT1
  n, d = integral_split(TT1, Zx)
  @assert map_entries(Qt, n) == TT1 * Qt(d)
  o3 = GenericRound2.Order(Zx, F)
  if isdefined(o1, :trans)
    return GenericRound2.Order(o3, integral_split(map_entries(Qt, TT1)*o1.trans, Zx)..., check = false)
  else
    return GenericRound2.Order(o3, integral_split(map_entries(Qt, TT1), Zx)..., check = false)
  end
  return GenericRound2.Order(o1, TT1, one(S)), GenericRound2.Order(o2, inv(TT2'), one(base_ring(TT2)))
end

function Base.denominator(a::Generic.Rat{fmpq}, S::FmpzPolyRing)
  return integral_split(a, S)[2]
end

function Base.numerator(a::Generic.Rat{fmpq}, S::FmpzPolyRing)
  return integral_split(a, S)[1]
end

function Hecke.integral_split(a::Generic.Rat{fmpq}, S::FmpzPolyRing)
  #TODO: feels too complicated....
  if iszero(a)
    return zero(S), one(S)
  end
  n = numerator(a)
  d = denominator(a)
  dn = reduce(lcm, map(denominator, coefficients(n)), init = fmpz(1))
  dd = reduce(lcm, map(denominator, coefficients(d)), init = fmpz(1))
  zn = S(n*dn)
  zd = S(d*dd)
  cn = content(zn)
  cd = content(zd)
  zn = divexact(zn, cn)
  zd = divexact(zd, cd)
  cn *= dd
  cd *= dn
  g = gcd(cn, cd)
  cn = divexact(cn, g)
  cd = divexact(cd, g)
  return cn*zn, cd*zd
end

function (S::FmpzPolyRing)(a::Generic.Rat{fmpq})
  n, d = integral_split(a, S)
  @assert isone(d)
  return n
end

end

using .HessMain


#=
  this should work:

Hecke.example("Round2.jl")

?GenericRound2

Qt, t = RationalFunctionField(QQ, "t")
Qtx, x = PolynomialRing(Qt, "x")
F, a = FunctionField(x^6+27*t^2+108*t+108, "a")
integral_closure(parent(denominator(t)), F)
integral_closure(Localization(Qt, degree), F)
integral_closure(Hecke.Globals.Zx, F)
basis(ans, F)
derivative(F.pol)(gen(F)) .* ans #should be integral

k, a = wildanger_field(3, 8*13)
integral_closure(ZZ, k)
integral_closure(Localization(ZZ, 2), k)

more interesting and MUCH harder:

G, b = FunctionField(x^6 + (140*t - 70)*x^3 + 8788*t^2 - 8788*t + 2197, "b")

=#
