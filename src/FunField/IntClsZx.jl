module HessMain
using Hecke
using ..HessQRModule
import ..HessQRModule: HessQR

function Hecke.integral_closure(S::HessQR, F::Generic.FunctionField{T}) where {T}
  return Hecke._integral_closure(S, F)
end

_lcm(a::QQFieldElem, b::QQFieldElem) = QQFieldElem(lcm(numerator(a), numerator(b)), gcd(denominator(a), denominator(b)))
_gcd(a::QQFieldElem, b::QQFieldElem) = QQFieldElem(gcd(numerator(a), numerator(b)), lcm(denominator(a), denominator(b)))

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

function florian(M::MatElem{<:Generic.RationalFunctionFieldElem{QQFieldElem}}, R::QQPolyRing, S::HessQR)
  Qt = base_ring(M)
  n = nrows(M)
  #step 1: make integral

  MM, d = integral_split(M, R)
  #M and d are in /over Q[x] (of type Q[x])
  cM = reduce(_gcd, map(content, MM), init = QQFieldElem(1,1))
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
  for p = keys(factor(ZZ, content(de)).fac)
    #step 2: do a HNF mod p and record the lifted operations
    k = Native.GF(p)
    kt = polynomial_ring(k, cached = false)[1]
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
            H[:, j:j] = H[:, j:j] - q*H[:, piv:piv]
            @assert H[i, j] == r
            T2[:, j] = T2[:, j:j] - Qt(Hecke.lift(Hecke.Globals.Zx, q))*T2[:, piv:piv]
            MM[:, j] = MM[:, j:j] - R(Hecke.lift(Hecke.Globals.Zx, q))*MM[:, piv:piv]
            if iszero(r)
              break
            end
            H[:, piv:piv], H[:, j:j] = H[:, j:j], H[:, piv:piv]
            T2[:, piv:piv], T2[:, j:j] = T2[:, j:j], T2[:, piv:piv]
            MM[:, piv:piv], MM[:, j:j] = MM[:, j:j], MM[:, piv:piv]
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
        if iszero(H[:,i:i])
          done = false
          T2[:, i:i] *= Qt(QQFieldElem(1, p))
          MM[:, i:i] *= R(QQFieldElem(1, p))
        end
      end
      @assert T1*M*T2 == MM
      done && break
    end
  end
  return M, T1, T2
end

function Hecke.integral_closure(Zx::ZZPolyRing, F::Generic.FunctionField)
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

  o3 = Hecke.GenOrd(Zx, F, true)
  if isdefined(o2, :trans)
    oo2 = order(o3, integral_split(inv(T2)*o2.trans, Zx)..., check = false)
  else
    oo2 = order(o3, integral_split(inv(T2), Zx)..., check = false)
  end
  return oo2

  #for testing....
  H, TT1 = hnf_with_transform(map_entries(S, T1*T*T2))
  @assert isone(H)
  T1 = map_entries(Qt, TT1)*T1
  if isdefined(o1, :trans)
    oo1 = order(o3, integral_split(T1*o1.trans, Zx)..., check = false)
  else
    oo1 = order(o3, integral_split(T1, Zx)..., check = false)
  end
  return oo1, oo2
end

function Base.denominator(a::Generic.RationalFunctionFieldElem{QQFieldElem}, S::ZZPolyRing)
  return integral_split(a, S)[2]
end

function Base.numerator(a::Generic.RationalFunctionFieldElem{QQFieldElem}, S::ZZPolyRing)
  return integral_split(a, S)[1]
end

function Hecke.integral_split(a::Generic.RationalFunctionFieldElem{QQFieldElem}, S::ZZPolyRing)
  #TODO: feels too complicated....
  if iszero(a)
    return zero(S), one(S)
  end
  n = numerator(a)
  d = denominator(a)
  dn = reduce(lcm, map(denominator, coefficients(n)), init = ZZRingElem(1))
  dd = reduce(lcm, map(denominator, coefficients(d)), init = ZZRingElem(1))
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

function (S::ZZPolyRing)(a::Generic.RationalFunctionFieldElem{QQFieldElem})
  n, d = integral_split(a, S)
  @assert isone(d)
  return n
end

end

using .HessMain


#=
  this should work:

Qt, t = rational_function_field(QQ, "t")
Qtx, x = polynomial_ring(Qt, "x")
F, a = function_field(x^6+27*t^2+108*t+108, "a")
integral_closure(parent(denominator(t)), F)
integral_closure(localization(Qt, degree), F)
integral_closure(Hecke.Globals.Zx, F)
basis(ans, F)
derivative(F.pol)(gen(F)) .* ans #should be integral

k, a = wildanger_field(3, 8*13)
integral_closure(ZZ, k)
integral_closure(localization(ZZ, 2), k)

more interesting and MUCH harder:

G, b = function_field(x^6 + (140*t - 70)*x^3 + 8788*t^2 - 8788*t + 2197, "b")

=#
