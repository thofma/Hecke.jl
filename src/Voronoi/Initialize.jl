#DIR:="~/arbeit/papiere/glnzconj/";
#
#//voronoi_stuff := recformat<n, d, steinitz, K, w, tau, p1, p2, ZB, B, BasHermNorm, mmax, F, sqrtd, Injec>;
#
#voronoi_stuff := recformat<n, d, steinitz, K, w, tau, p1, p2, ZB, B, BasHermNorm, mmax, F, sqrtd, Injec, DimSym, ERank, FRank>;
#
#;
#
#declare attributes RngInt: voronoi_stuff; 
#

mutable struct VoronoiCtx
  n
  d
  steinitz
  K
  w
  tau
  p1
  p2
  ZB
  B
  BasHermNorm
  mmax
  F
  sqrtd
  Injec
  DimSym
  ERank
  FRank
  function VoronoiCtx()
    return new()
  end
end

function VoronoiCtx(n, d, steinitz)
  V = VoronoiCtx()
  myideal = 0
  x = gen(Globals.Qx)
  K, w = NumberField(x^2 - d, "w", cached = false)
  V.K = K
  V.n = n
  V.d = d
  V.w = w
  V.steinitz = steinitz
  V.w = w
  if d % 4 == 1
    tau = divexact(1 + w, 2)
  else
    tau = w
  end
  V.tau = tau
  OK = maximal_order(K)
  C, f = class_group(OK)
  small_gens = find_gens(pseudo_inv(f), PrimesSet(fmpz(1), fmpz(-1)))[1]
  if length(small_gens) == 0
    V.mmax = one(fmpz)
  else
    V.mmax = maximum([norm(p) for p in small_gens])
  end
  if steinitz != 0
    p1 = 1 * OK
    p2 = 1 * OK
  else
    p1 = 1 * OK
    p2 = 1 * OK
  end

  V.p1 = p1
  V.p2 = p2

  V.Injec = () -> error("AsdsD")
  V.F = () -> error("AsdsD")
  V.sqrtd = () -> error("AsdsD")

#  if d ne -1 then
#   F<sqrtd>:=QuadraticField(-d);
#   Injec:=hom<F -> RealField() | Sqrt(-d)>;
#  else
#   F:=Rationals();
#   sqrtd:=1;
#   Injec:=hom<F -> RealField() |>;
#  end if;
#
#  temp`F := F;
#  temp`sqrtd := sqrtd;
#  temp`Injec := Injec;

  if p2 == p1 
    ZB = [1, tau]
  else
    ZB = basis(p2)
  end

  V.ZB = ZB

  B = []
  for k in 1:(n - 1)
    for i in 1:2
      v = zero_matrix(K, 1, n)
      if i == 1
        v[1, k] = one(K)
      else
        v[1, k] = tau
      end
      push!(B, v)
    end
  end

  for i in 1:2
    v = zero_matrix(K, 1, n)
    if i == 1
      v[1, n] = ZB[1]
    else
      v[1, n] = ZB[2]
    end
    push!(B, v)
  end

  V.B = B

  # Z-basis for L
#  //Z-base for a:
#  if p2 eq p1 then ZB:=[1,tau]; else ZB:=Basis(p2); end if;
#
#  temp`ZB := ZB;
#
#  //Determine normalized R-base of space of Hermitian forms

  BasHermNorm = []

  for i in 1:n
    res = zero_matrix(K, n, n)
    res[i, i] = 1
    push!(BasHermNorm, res)
    for j in (i + 1):n
      for k in 1:2
        res = zero_matrix(K, n, n)
        if k == 1
          res[i, j] = 1//2
          res[j, i] = 1//2
          push!(BasHermNorm, res)
        else
          res[i, j] = w//2
          res[j, i] = -w//2
          push!(BasHermNorm, res)
        end
      end
    end
  end

  V.BasHermNorm = BasHermNorm

  DimSym = n^2
  ERank = DimSym - 2
  FRank = DimSym - 1
  V.DimSym = DimSym
  V.ERank = ERank
  V.FRank = FRank

  return V
end
