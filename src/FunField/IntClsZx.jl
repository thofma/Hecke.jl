module HessMain
using Hecke
using ..HessQRModule, ..GenericRound2
import ..HessQRModule: HessQR

function GenericRound2.integral_closure(S::HessQR, F::Generic.FunctionField{T}) where {T}
  return GenericRound2._integral_closure(S, F)
end

_lcm(a::fmpq, b::fmpq) = fmpq(lcm(numerator(a), numerator(b)), gcd(denominator(a), denominator(b)))
_gcd(a::fmpq, b::fmpq) = fmpq(gcd(numerator(a), numerator(b)), lcm(denominator(a), denominator(b)))

#=
Hallo Claus,

für R Hauptidealring geht es dann wohl so:

Sei M die Trafomatrix zwischen einer R<t>- und einer K[t]-Basis, wobei
die Zeilen zu R<t> und die Spalten zu K[t] korrespondieren.  Es ist
det(M) neq 0. Die Zeilen von M können durch Multiplikation mit primitiven
Polynomen aus R[t] so skaliert werden, dass M nur Polynome aus R[t] als
Einträge hat. Dies ist eine R<t>-unimodulare Operation.

Wenn det(M) Inhalt eins hat, dann ist M R<t>-unimodular, durch
Basiswechsel beim R<t>-Modul läßt sich also M = Einheitsmatrix
erreichen. Also korrespondieren die Spalten von M zu einer Basis des
Schnitts des K[t]- und R<t>-Moduls.

Wenn det(M) nicht Inhalt eins hat, dann gibt es einen Primteiler p des
Inhalts. Dann ist det(M) mod p = 0, also hat die
Spaltenhermitenormalform von M mod p Nullspalten.  Diese
Spaltenhermitenormalform wird durch durch Multiplikation von rechts mit
Elementarmatrizen über R/p[t] erreicht. Diese Elementarmatrizen können
modulo p geliftet werden, so dass sie Einträge aus R[t] haben und
R[t]-unimodular sind.  Multiplikation von rechts mit diesen gelifteten
Elementarmatrizen liefert eine Matrix, die mod p die oben erwähnte
Spaltenhermitenormalform ist. Insbesondere ist mindestens eine der
hinteren Spalten über R[t] durch p teilbar. Also diese Spalten solange
durch p dividieren, bis keine Spalte mehr durch p dividierbar ist.  Das
ist eine k[t]-unimodulare Operation. Nun ist auch der p-Anteil des
Inhalts von det(M) echt verringert worden. Iteration mit diesem oder
anderen p jenachdem, was noch im Inhalt übrig ist, führt schließlich zu
Inhalt eins.

Viele Grüße,
Florian
=#

function florian(M::MatElem{<:Generic.Rat{fmpq}}, R::FmpqPolyRing, S::HessQR)
  Qt = base_ring(M)
  n = nrows(M)
  #step 1: make integral

  MM, d = integral_split(M, R)
  #M and d are in /over Q[x] (of type Q[x])
  cM = reduce(_gcd, map(content, MM), init = fmpq(1,1))
  MM *= inv(cM) #should now be in Z[x]!
  cd = content(d)
  d *= inv(cd)  #should be in Z[x] and primitive, so

  T1 = identity_matrix(Qt, n)*d
  T2 = identity_matrix(Qt, n)*inv(cM)*inv(cd)

  @assert T1*M*T2 == MM
  @assert isone(integral_split(T1, S)[2])
  @assert isone(integral_split(T2, R)[2])
  @assert is_unit(integral_split(det(T1), S)[1])
  @assert is_unit(integral_split(det(T2), R)[1])


  de = det(MM)
  for p = keys(factor(content(de), ZZ).fac)
    #step 2: do a HNF mod p and record the lifted operations
    k = GF(p)
    kt = PolynomialRing(k, cached = false)[1]
    while true
      H = map(kt, MM)
      piv = 1
      for i=1:n
        if iszero(H[i,piv])
          j = piv+1
          while j<= n && iszero(H[i, j])
            j += 1
          end
          if j>n
            continue
          end
          H[:, piv], H[:, j] = H[:, j], H[:, piv]
          T2[:, piv], T2[:, j] = T2[:, j], T2[:, piv]
          MM[:, piv], MM[:, j] = MM[:, j], MM[:, piv]
        end
        for j=piv+1:n
          while !iszero(H[i, j])
            q, r = divrem(H[i, j], H[i,piv])
            H[:, j] = H[:, j] - q*H[:, piv]
            @assert H[i, j] == r
            T2[:, j] = T2[:, j] - Qt(Hecke.lift(Hecke.Globals.Zx, q))*T2[:, piv]
            MM[:, j] = MM[:, j] - R(Hecke.lift(Hecke.Globals.Zx, q))*MM[:, piv]
            if iszero(r) 
              break
            end
            H[:, piv], H[:, j] = H[:, j], H[:, piv]
            T2[:, piv], T2[:, j] = T2[:, j], T2[:, piv]
            MM[:, piv], MM[:, j] = MM[:, j], MM[:, piv]
          end
        end
        @assert !iszero(H[i,piv])
        #= Don't reduce upwards...it does not change the "being zero or not"
        for j=1:piv-1
          q, r = divrem(H[i, j], H[i,piv])
          H[:, j] = H[:, j] - q*H[:, piv]
          @assert H[i, j] == r
          T2[:, j] = T2[:, j] - Qt(Hecke.lift(Hecke.Globals.Zx, q))*T2[:, i]
          MM[:, j] = MM[:, j] - R(Hecke.lift(Hecke.Globals.Zx, q))*MM[:, i]
        end
        =#
        piv += 1
      end
      done = true
      for i=1:n
        if iszero(H[:,i])
          done = false
          T2[:, i] *= Qt(fmpq(1, p))
          MM[:, i] *= R(fmpq(1, p))
        end
      end
      @assert T1*M*T2 == MM
      done && break
    end
  end
  return M, T1, T2
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
  _, T1, T2 = florian(T, R, S)
  
  o3 = GenericRound2.Order(Zx, F, true)
  if isdefined(o2, :trans)
    oo2 = GenericRound2.Order(o3, integral_split(inv(T2)*o2.trans, Zx)..., check = false)
  else
    oo2 = GenericRound2.Order(o3, integral_split(inv(T2), Zx)..., check = false)
  end
  return oo2

  #for testing....
  H, TT1 = hnf_with_transform(map_entries(S, T1*T*T2))
  @assert isone(H)
  T1 = map_entries(Qt, TT1)*T1
  if isdefined(o1, :trans)
    oo1 = GenericRound2.Order(o3, integral_split(T1*o1.trans, Zx)..., check = false)
  else
    oo1 = GenericRound2.Order(o3, integral_split(T1, Zx)..., check = false)
  end
  return oo1, oo2
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
