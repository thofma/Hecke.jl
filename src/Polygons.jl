export newton_polygon, Line, Polygon

###############################################################################
#
#  Types
#
###############################################################################

mutable struct Line
  points :: Tuple{Tuple{Int, Int}, Tuple{Int, Int}}
  slope :: fmpq
  
  function Line(points::Tuple{Tuple{Int, Int}, Tuple{Int, Int}})
    line = new()
    line.points = points
    line.slope = slope(points[1],points[2])
    return line
  end
  
  function Line(a::Tuple{Int, Int}, b::Tuple{Int, Int})
    return Line((a,b))
  end
end

mutable struct Polygon
  lines :: Array{Line,1}
  f :: fmpz_poly
  phi :: fmpz_poly
  p :: fmpz
  
  function Polygon(lines::Array{Line,1}; sorted = false)
    polygon = new()
    if sorted
      polygon.lines = lines
    else
      for j = 1:length(lines)-1
        iMin = j
        for i = j+1:length(lines)
          if (lines[i]).points[1][1] < lines[iMin].points[1][1]
            iMin = i
          end
        end
        if iMin != j
          lines[j],lines[iMin] = lines[iMin],lines[j]
        end
      end
      polygon.lines = lines
    end
     
    return polygon
  end
end 

###############################################################################
#
#  Invariants of lines an polygons
#
###############################################################################

function length(L::Line)
  return L.points[2][1]-L.points[1][1]
end

function heigth(L::Line)
  return L.points[2][1]-L.points[1][1]
end

function slope(L::Line)
  return slope(L.points[1], L.points[2])
end

function slope(a::Tuple{Int, Int}, b::Tuple{Int, Int})
  return fmpq((b[2]-a[2])//(b[1]-a[1]))
end

function degree(L::Line)
  return divexact(L.points[2][1]-L.points[1][1], denominator(L.slope))
end

###############################################################################
#
#  Lower convex hull of a set of points
#
###############################################################################

function sortpoints(x::Array{Tuple{Int, Int},1})
  for j = 1:length(x)-1
    iMin = j
    for i = j+1:length(x)
      if x[i][1] < x[iMin][1]
        iMin = i
      end
    end
    if iMin != j
      x[j],x[iMin] = x[iMin],x[j]
    end 
  end
  return x
end

function lowerconvexhull(points::Array{Tuple{Int, Int},1})

  points = sortpoints(points)

  # Take care of trivial case with 1 or 2 elements

  if length(points) == 1
    error("Lower convex hull of 1 point is not defined")
  elseif length(points) == 2
    return Polygon([Line((points[1], points[2]))])
  end
  
  i = 1
  while points[i][2] !=0
    i += 1
  end
  
  pointsconvexhull = Tuple{Int, Int}[points[i]]
  while pointsconvexhull[end][1] != 0
    best_slope = slope(pointsconvexhull[end], points[1])
    i = 2
    new_point = points[1]
    while points[i][1] < pointsconvexhull[end][1]
      candidate = slope(pointsconvexhull[end], points[i])
      if candidate > best_slope
        new_point = points[i]
        best_slope = candidate
      end
      i += 1
    end 
    push!(pointsconvexhull, new_point)
  end
  
  n=length(pointsconvexhull)
  l= Line[]
  for i=0:n-2
    push!(l, Line(pointsconvexhull[n-i], pointsconvexhull[n-i-1]))
  end
  return Polygon(l, sorted = true)
  #=
  #This thing clearly cannot work, I don't know how to fix it
  i = 1
  while points[i][2] !=0
    i += 1
  end
  
  pointsonconvexhull = [ points[i-1], points[i] ]

  n = length(points)-2
  

  oldslope = slope(pointsonconvexhull[1],pointsonconvexhull[2])

  for i = 1:n
    newslope = slope(points[n-i+1], pointsonconvexhull[1])
    if newslope >= oldslope
      pointsonconvexhull[1] = points[n-i+1]
    else
      unshift!(pointsonconvexhull, points[n-i+1])
    end
    oldslope = newslope
  end
  =#
  t = Line[]
  for i=1:length(pointsonconvexhull)-1
    push!(t,Line((pointsonconvexhull[i], pointsonconvexhull[i+1])))
  end
  return Polygon(t)
end

###############################################################################
#
#  Newton polygon
#
###############################################################################

function phi_development(f::fmpz_poly, phi::fmpz_poly)
  dev = Array{fmpz_poly, 1}()
  g = f
  while degree(g)>=degree(phi)
    g, r = divrem(g, phi)
    push!(dev, r)
  end
  push!(dev, g)
  return dev
end

function valuation(f::fmpz_poly, p::fmpz)
  l = [Int(valuation(coeff(f,i), p)) for i= 0:degree(f) if coeff(f,i)!=0]
  return minimum(l)
end


function newton_polygon(dev::Array{fmpz_poly, 1}, p::fmpz)
  a = Tuple{Int, Int}[]
  for i = 0:length(dev)-1
    if !iszero(dev[i+1])
      push!(a, (i,valuation(dev[i+1],p)))
    end
  end 
  return lowerconvexhull(a)
end

function newton_polygon(f::fmpz_poly, phi::fmpz_poly, p::fmpz)
  a = Tuple{Int, Int}[]
  if !(isprime(p))
    error("Not a prime")
  end
  #Compute the development
  dev=phi_development(f,phi)
  for i = 0:length(dev)-1
    if !iszero(dev[i+1])
      push!(a, (i,valuation(dev[i+1],p)))
    end
  end 
  return lowerconvexhull(a)
end


function residual_polynomial(F::FqFiniteField, L::Line, dev::Array{fmpz_poly, 1}, p::fmpz)

  cof=Array{fq,1}()
  R=ResidueRing(FlintZZ, p, cached=false)
  Rx,x=PolynomialRing(R,"y", cached=false)
  s=L.points[1][1]
  e=denominator(L.slope)
  for i=0:degree(L)
    if !iszero(dev[Int(s+e*i+1)])
      el=Rx(divexact(dev[Int(s+e*i+1)], p^(Int(L.points[1][2]+numerator(L.slope*i*e)))))
      push!(cof, F(el))
    else
      push!(cof, F(0))
    end 
  end
  Fx, x=PolynomialRing(F,"x", cached=false)
  return Fx(cof)

end

function phi_development_with_quos(f::fmpz_poly, phi::fmpz_poly)
  dev=Array{fmpz_poly, 1}()
  quos=Array{fmpz_poly, 1}()
  g=f
  while degree(g)>=degree(phi)
    g, r = divrem(g, phi)
    push!(dev, r)
    push!(quos, g)
  end
  push!(dev, g)
  return dev, quos
end

function phi_development_with_quos(f::fmpz_poly, phi::fmpz_poly, Rx::FmpzModPolyRing)
  dev=Array{fmpz_poly, 1}()
  quos=Array{fmpz_poly, 1}()
  Zx = parent(f)
  g = Rx(f)
  h = Rx(phi)
  while degree(g)>=degree(h)
    g, r = divrem(g, h)
    push!(dev, lift(Zx,r))
    push!(quos, lift(Zx,g))
  end
  push!(dev, lift(Zx,g))
  return dev, quos
end

function _floor_newton_polygon(N::Polygon, i::Int)
  
  j = 1
  while N.lines[j].points[2][1]< i
    j += 1
  end
  l = N.lines[j].points[1][2] - (N.lines[j].points[1][1]-i)*slope(N.lines[j])
  return floor(Int, BigFloat(numerator(l)//denominator(l)))

end

###############################################################################
#
#  p-overorder using Polygons
#
###############################################################################

function gens_overorder_polygons(O::NfOrd, p::fmpz)

  K = nf(O)
  f = K.pol
  
  els = nf_elem[]
  Zx, x = PolynomialRing(FlintZZ, "x", cached = false)
  modu = valuation(rres(Zx(f), derivative(Zx(f))), p) 
  R = ResidueRing(FlintZZ, p, cached = false)
  Rx, y = PolynomialRing(R, "y", cached = false)
  #R1 = ResidueRing(FlintZZ, p^(modu+2), cached = false)
  #R1x, z = PolynomialRing(R1, "z", cached = false)
  f1 = Rx(K.pol)
  fac = factor(f1)
  l = nf_elem[gen(K)^i for i=0:degree(K)-1]
  regular = true
  vdisc = 0
  for (g, m) in fac
    if m==1
      continue
    end
    F, a = FiniteField(g, "a", cached = false)
    phi = lift(Zx, g)
    dev, quos = phi_development_with_quos(Zx(f), phi)#, R1x)
    N = newton_polygon(dev, p)
    if regular
      for lin in N.lines
        if slope(lin) < 0 && degree(lin) != 1
          rp = residual_polynomial(F, lin, dev, p)
          if !issquarefree(rp)
            regular = false
            break
          end
        end
      end
    end
    for i = 1:m
      v = _floor_newton_polygon(N, i)
      if v > 0
        vdisc += v*degree(phi)
        for j = 1:degree(phi)
          push!(l, divexact(K(x^(j-1)*quos[i]), p^v))
        end
      end
    end
  end
  B = basis_mat(l)
  B = sub(hnf(B), nrows(B)-degree(K)+1:nrows(B), 1:degree(K))
  if !regular
    elt = nf_elem[]
    for i in 1:nrows(B) 
      push!(elt, elem_from_mat_row(K, B.num, i, B.den))
    end
    O1 = _order_for_polygon_overorder(K, elt)
  else
    #N1 = B.den * B.num
    #N1 = _hnf_modular_eldiv(N1, p^(modu+1), :lowerleft)
    #O1 = Order(K, FakeFmpqMat(N1, B.den))
    O1 = Order(K, B, false)
    O1.disc = divexact(O.disc, p^(2*vdisc))
    push!(O1.primesofmaximality, p)
  end
  return O1
  
end


function polygons_overorder(O::NfOrd, p::fmpz)
  #First, Dedekind criterion. If the Dedekind criterion says that we are p-maximal,
  # or it can produce an order which is p-maximal, we are done.
  Zy, y = PolynomialRing(FlintZZ, "y", cached = false)
  Kx, x = PolynomialRing(ResidueRing(FlintZZ, p, cached=false), "x", cached=false)

  f = nf(O).pol

  Zyf = Zy(f)

  fmodp = Kx(Zyf) 
 
  fac = factor_squarefree(fmodp)

  g = prod(x for x in keys(fac.fac))
  h = divexact(fmodp,g)

  # first build 1/p ( f - g*h)
  gZ = lift(Zy,g)
  hZ = lift(Zy, h)

  g1 = Zyf - gZ*hZ

  for i in 0:degree(g1)
    q, r = divrem(coeff(g1,i),p)
    @assert r == 0
    setcoeff!(g1,i,q)
  end
  
  g1modp = Kx(g1)
  U = gcd(gcd(g,h), g1modp)
  if isone(U)
    return O
  elseif 2*degree(U) == valuation(discriminant(O), p)
    #@show "Dedekind"
    U = divexact(fmodp, U)

    @hassert :NfOrd 1 rem(O.disc, p^2) == 0
    alpha = nf(O)(parent(f)(lift(Zy,U)))

    # build the new basis matrix
    # we have to take the representation matrix of alpha!
    # concatenating the coefficient vector won't help
    Malpha, d = representation_matrix_q(alpha)
    @assert isone(d)
    n = _hnf_modular_eldiv(Malpha, p, :lowerleft)
    b = FakeFmpqMat(n, p)
    @hassert :NfOrd 1 defines_order(nf(O), b)[1]
    OO = Order(nf(O), b, false)
    OO.isequation_order = false
    OO.disc = divexact(O.disc, p^(2*(degree(O)-degree(U))))
    push!(OO.primesofmaximality, p)
    return OO
  end
  return gens_overorder_polygons(O, p)

end

function _order_for_polygon_overorder(K::S, elt::Array{T, 1}) where {S, T}

  n = degree(K)
  closed = false
  dold = fmpq(0)

  # Since 1 is in elt, prods will contain all elements
  while !closed
    prods = T[elt[i] for i=1:length(elt)]
    for i = 2:length(elt)
      for j = i:length(elt)
        el = elt[i]*elt[j]
        if denominator(el) != 1
          push!(prods, elt[i]*elt[j])
        end
      end
    end
    
    B = hnf(basis_mat(prods))
    
    dd = B.num[nrows(B) - degree(K) + 1, 1]
    for i in 2:degree(K)
      dd *= B.num[nrows(B) - degree(K) + i, i]
    end
    if iszero(dd)
      error("Elements do not define a module of full rank")
    end
    d = dd//(B.den)^n

    if dold == d
      closed = true
    else
      dold = d
      elt = T[]
      for i in 1:n
        push!(elt, elem_from_mat_row(K, B.num, nrows(B) - degree(K) + i, B.den))
      end
    end
  end

  # Make an explicit check
  @hassert :NfOrd 1 defines_order(K, elt)[1]
  return Order(K, elt, false, false)
end

###############################################################################
#
#  Decomposition type using polygons
#
###############################################################################

function _from_algs_to_ideals(A::AlgAss{T}, OtoA::Map, AtoO::Map, Ip1::NfOrdIdl, p::fmpz) where {T}
  
  O = order(Ip1)
  @vprint :NfOrd 1 "Splitting the algebra\n" 
  AA = decompose(A)
  @vprint :NfOrd 1 "Done \n"
  ideals = Array{Tuple{NfOrdIdl, Int}, 1}(undef, length(AA))
  m = zero_matrix(FlintZZ, 1, degree(O))
  for i = 1:length(AA)
    B = AA[i][1]
    BtoA = AA[i][2]
    f = dim(B)
    idem = BtoA(one(B)) # Assumes that B == idem*A
    M = representation_matrix(idem)
    ker = left_kernel_basis(M)
    N = basis_mat(Ip1, Val{false})
    for s = 1:length(ker)
      b = elem_in_basis(AtoO(A(ker[s])))
      for j = 1:degree(O)
        m[1, j] = b[j]
      end
      N = vcat(N, m)
    end
    @vtime :NfOrd 1 N = view(_hnf_modular_eldiv(N, p, :lowerleft), nrows(N) - degree(O) + 1:nrows(N), 1:degree(O))
    P = NfOrdIdl(O, N)
    P.minimum = p
    P.norm = p^f
    P.splitting_type = (0, f)
    P.is_prime = 1
    fromOtosimplealgebra = compose(OtoA, inv(BtoA))
    compute_residue_field_data!(P, fromOtosimplealgebra)

    ideals[i] = (P, 0)
  end
  return ideals, AA
end

function _decomposition(O::NfAbsOrd, I::NfAbsOrdIdl, Ip::NfAbsOrdIdl, T::NfAbsOrdIdl, p::fmpz)
  #I is an ideal lying over p
  #T is the product of all the prime ideals lying over p that do not appear in the factorization of I
  #Ip is the p-radical
  Ip1 = Ip + I
  A, OtoA = AlgAss(O, Ip1, p)
  
  if dim(A) == 1
    Ip1.norm = p
    Ip1.splitting_type = (0, 1)
    Ip1.is_prime = 1
    ideals = Array{Tuple{ideal_type(O), Int}, 1}(undef, 1)
    ideals[1] = (Ip1, Int(0))
  else
    AtoO = inv(OtoA)
    @vtime :NfOrd 3 ideals , AA = _from_algs_to_ideals(A, OtoA, AtoO, Ip1, p)
  end
  k = (1-1/BigInt(p))^degree(O) < 0.1
  for j in 1:length(ideals)
    P = ideals[j][1]
    f = P.splitting_type[2]
    
    @vprint :NfOrd 1 "Searching for 2-element presentation \n"
    
    if length(ideals) > 1 && k
      # The following does not work if there is only one prime ideal
      # This is roughly Algorithm 6.4 of Belabas' "Topics in computational algebraic
      # number theory".
      # Compute Vp = P_1 * ... * P_j-1 * P_j+1 * ... P_g

      B, BtoA = AA[j]
      v1 = AtoO(BtoA(one(B)))
      #u1 = AtoO(sum([AA[i][2](AA[i][1][1]) for i=1:length(ideals) if i != j]))
      u1 = 1 - v1
      @hassert :NfOrd 1 isone(u1+v1)
      @hassert :NfOrd 1 u1 in P
      u2, v2 = idempotents(P, T)
      u = u1*(u2+v2) + u2*v1
      v = v1*v2
      @hassert :NfOrd 1 isone(u + v)
      
      @hassert :NfOrd 1 u in P
      x = zero(parent(u))
      modulo = norm(P)*p

      if !is_norm_divisible(u.elem_in_nf, modulo)
        x = u
      elseif !is_norm_divisible(u.elem_in_nf+p, modulo)
        x = u + p
      elseif !is_norm_divisible(u.elem_in_nf-p, modulo)
        x = u - p
      else
        Ba = basis(P, Val{false})
        for i in 1:degree(O)
          if !is_norm_divisible((v*Ba[i] + u).elem_in_nf, modulo)
            x = v*Ba[i] + u
            break
          end
        end
      end

      @hassert :NfOrd 1 !iszero(x)
      @hassert :NfOrd 2 O*O(p) + O*x == P
      P.gen_one = p
      P.gen_two = x
      P.gens_normal = p
      P.gens_weakly_normal = 1
      @vtime :NfOrd 3 e = Int(valuation(nf(O)(p), P)) #I can probably do something just looking at the Newton polygon.
      P.splitting_type = e, f
      ideals[j] = (P, e)
    else
      @vprint :NfOrd 1 "Chances for finding second generator: ~$((1-1/BigInt(p)))\n"
      @vtime :NfOrd 3 _assure_weakly_normal_presentation(P)
      u = P.gen_two
      modulo = norm(P)*p
      x = zero(parent(u))
      
      if !is_norm_divisible(u.elem_in_nf, modulo)
        x = u
      elseif !is_norm_divisible(u.elem_in_nf+p, modulo)
        x = u + p
      elseif !is_norm_divisible(u.elem_in_nf-p, modulo)
        x = u - p
      else
        Ba = basis(P, Val{false})
        for i in 1:degree(O)
          if !is_norm_divisible((v*Ba[i] + u).elem_in_nf, modulo)
            x = v*Ba[i] + u
            break
          end
        end
      end

      @hassert :NfOrd 1 !iszero(x)
      @hassert :NfOrd 2 O*O(p) + O*x == P
      P.gen_two = x
      P.gens_normal = p
      if length(ideals) == 1
        e = Int(divexact(valuation(norm(I), p), f))
      else
        @vtime :NfOrd 3 e = Int(valuation(nf(O)(p), P))
      end
      P.splitting_type = e, f
      ideals[j] = (P, e)
    end
  end
  return ideals

end

function decomposition_type_polygon(O::NfOrd, p::fmpz)
  K = nf(O)
  f = K.pol
  Zx ,x = PolynomialRing(FlintZZ, "x", cached = false)
  R = ResidueRing(FlintZZ, p, cached = false)
  Rx, y = PolynomialRing(R, "y", cached = false)
  f1 = Rx(Zx(K.pol))
  @vprint :NfOrd 1 "Factoring the polynomial \n"
  fac = factor(f1) #TODO: We don't need the factorization directly, but only the factorization of the non-squarefree part
  res = Tuple{Int, Int}[]
  l = Tuple{NfOrdIdl, NfOrdIdl}[]
  for (g,m) in fac
    @vprint :NfOrd 1 "Doing $((g,m)) \n"
    if m==1
      push!(res, (degree(g), 1))
      continue
    end
    phi = lift(Zx, g)
    dev = phi_development(Zx(f), phi)
    N = newton_polygon(dev, p)
    if denominator(slope(N.lines[1])) == m
      push!(res, (degree(g), m))
      continue
    end
    filter(x -> slope(x)<0, N.lines)
    F, a = FiniteField(g, "a", cached = false)
    pols = fq_poly[]
    for ll in N.lines
      rp = residual_polynomial(F, ll, dev, p)
      if issquarefree(rp)
        push!(pols, rp)
      else
        break
      end
    end  
    if length(N.lines) != length(pols)
      push!(l, (ideal(O, fmpz(p), O(K(parent(f)(lift(Zx, g^m))))), ideal(O, fmpz(p), O(K(parent(f)(lift(Zx, divexact(f1, g^m)))))))) 
    else
      for i=1:length(pols)
        fact = factor(pols[i])
        s = denominator(slope(N.lines[i]))
        for psi in keys(fact.fac)
          push!(res, (degree(phi)*degree(psi), s))
        end      
      end
    end
  end
  if !isempty(l)
    Ip = pradical(O, p)
    for (I, J) in l
      lp = _decomposition(O, I, Ip, J, p)
      for (P, e) in lp
        push!(res, (P.splitting_type[2], e))
      end
    end
  end
  return res
  
end

###############################################################################
#
#  Prime decomposition
#
###############################################################################

function prime_decomposition_polygons(O::NfAbsOrd{S, T}, p::fmpz, degree_limit::Int = 0, lower_limit::Int = 0) where {S, T}
  if degree_limit == 0
    degree_limit = degree(O)
  end
  K = nf(O)
  f = K.pol
  Zx = PolynomialRing(FlintZZ, "x", cached = false)[1]
  R = ResidueRing(FlintZZ, p, cached = false)
  Rx, y = PolynomialRing(R, "y", cached = false)
  f1 = Rx(K.pol)
  @vprint :NfOrd 1 "Factoring the polynomial \n"
  @vtime :NfOrd 1 fac = factor(f1)
  res = Tuple{NfOrdIdl, Int}[]
  l = Tuple{NfOrdIdl, NfOrdIdl}[]
  @vtime :NfOrd 3 for (g, m) in fac
    if degree(g) > degree_limit || lower_limit > degree(g)
      continue
    end
    @vprint :NfOrd 1 "Doing $((g, m)) \n"
    phi = lift(Zx, g)
    if m==1
      ei = m
      t = parent(f)(phi)
      b = K(t)
      J = NfAbsOrdIdl(O)
      J.gen_one = p
      J.gen_two = O(b, false)
      J.is_prime = 1
      J.splitting_type = ei, degree(phi)
      J.norm = FlintZZ(p)^degree(phi)
      J.minimum = FlintZZ(p)

      # We have to do something to get 2-normal presentation:
      # if ramified or valuation val(b,P) == 1, (p,b)
      # is a P(p)-normal presentation
      # otherwise we need to take p+b
      # I SHOULD CHECK THAT THIS WORKS

      if !(!is_norm_divisible(b, (J.norm)^2) || (ei > 1))
        J.gen_two = J.gen_two + O(p)
      end

      J.gens_normal = p
      J.gens_weakly_normal = true
      push!(res, (J, ei))
      continue
    end
    #=
    dev = phi_development(Zx(f),phi)
    N = newton_polygon(dev, p)
    filter(x -> slope(x)<0, N.lines)
    if length(N.lines) == 1 && degree(N.lines[1]) == 1 && length(fac)==1
      s = slope(N.lines[1])
      x=K(1)
      if abs(numerator(s))> denominator(s)
        d, r = divrem(numerator(s), denominator(s))
        x = divexact(K(phi), p^(-d))
        d, u, v = gcdx(r, denominator(s))
        @assert d == 1
        x = divexact(x^-u, p^(-v))#*K(parent(f)(lift(Zx, divexact(f1, g^m)))) Can this be correct?
      else
        d, u, v = gcdx(numerator(s), denominator(s))
        @assert d==1
        x=divexact(K(phi)^(-u), p^(-v))#*K(parent(f)(lift(Zx, divexact(f1, g^m)))) Can this be correct?
      end
      J = NfAbsOrdIdl(O)
      J.gen_one = p
      J.gen_two = O(x)
      J.is_prime = 1
      J.splitting_type = Int(denominator(s)), degree(phi)
      J.norm = FlintZZ(p)^degree(phi)
      J.minimum = FlintZZ(p)
      J.gens_normal = p
      J.gens_weakly_normal = true
      push!(res, (J, Int(denominator(s))))
      continue
    end
    =#
    #TODO: p-adic factorization of the polynomial.
    push!(l, (ideal(O, fmpz(p), O(K(parent(f)(lift(Zx, g^m))))), ideal(O, fmpz(p), O(K(parent(f)(lift(Zx, divexact(f1, g^m))))))))
  end
  @vtime :NfOrd 3 if !isempty(l)
    @vtime :NfOrd 3 Ip = pradical(O, p)
    for (I, Q) in l
      @vtime :NfOrd 3 lp = _decomposition(O, I, Ip, Q, p)
      for (P, e) in lp
        if degree(P) > degree_limit || degree(P) < lower_limit
          continue
        end
        push!(res, (P, e))
      end
    end
  end
  return res

end
