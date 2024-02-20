###############################################################################
#
#  Types
#
###############################################################################

mutable struct Line
  points :: Tuple{Tuple{Int, Int}, Tuple{Int, Int}}
  slope :: QQFieldElem

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
  lines :: Vector{Line}

  function Polygon(lines::Vector{Line}; sorted = false)
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


mutable struct NewtonPolygon{T}
  P::Polygon
  f::T
  phi::T
  p::ZZRingElem
  development::Vector{T}
end

lines(N::NewtonPolygon) = N.P.lines

function is_one_sided(N::NewtonPolygon)
  return isone(length(lines(N)))
end

###############################################################################
#
#  Invariants of lines an polygons
#
###############################################################################

function length(L::Line)
  return L.points[2][1]-L.points[1][1]
end

function height(L::Line)
  return L.points[2][1]-L.points[1][1]
end

function slope(L::Line)
  return slope(L.points[1], L.points[2])
end

function slope(a::Tuple{Int, Int}, b::Tuple{Int, Int})
  return QQFieldElem(b[2]-a[2], b[1]-a[1])
end

function degree(L::Line)
  return divexact(L.points[2][1]-L.points[1][1], denominator(L.slope))
end

function Base.:(==)(L::Line, L2::Line)
  return L.points == L2.points
end

function Base.:(==)(P::Polygon, P2::Polygon)
  return P.lines == P2.lines
end

###############################################################################
#
#  Lower convex hull of a set of points
#
###############################################################################

function sortpoints(x::Vector{Tuple{Int, Int}})
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

function lower_convex_hull_old(points::Vector{Tuple{Int, Int}})

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
  l = Vector{Line}(undef, n-1)
  for i=0:n-2
    l[i + 1] = Line(pointsconvexhull[n-i], pointsconvexhull[n-i-1])
  end
  return Polygon(l, sorted = true)
end


function lower_convex_hull(points::Vector{Tuple{Int, Int}})
  orig_points = copy(points)

  points = sortpoints(points)

  # Take care of trivial case with 1 or 2 elements
  if length(points) == 1
    error("Lower convex hull of 1 point is not defined")
  elseif length(points) == 2
    P = Polygon([Line((points[1], points[2]))])
  else
    pointsconvexhull = Tuple{Int, Int}[points[1]]
    i = 2
    while i<= length(points)
      y = pointsconvexhull[end]
      sl = [slope(y, x) for x = points[i:end]]
      min_sl = minimum(sl)
      p = findlast(x->x == min_sl, sl)::Int
      push!(pointsconvexhull, points[p+i-1])
      i += p
    end
    pointsconvexhull = reverse(pointsconvexhull)

    n=length(pointsconvexhull)
    l = Vector{Line}(undef, n-1)
    for i=0:n-2
      l[i + 1] = Line(pointsconvexhull[n-i], pointsconvexhull[n-i-1])
    end
    P = Polygon(l, sorted = true)
  end
  return P
end

###############################################################################
#
#  Computation of the phi-development
#
###############################################################################

@doc raw"""
    phi_development(f::PolyRingElem, phi::PolyRingElem) -> Vector{PolyRingElem}

Computes an array of polynomials $[a_0, \ldots, a_s]$ such that $\sum a_i \phi^i = f$.
"""
function phi_development(f::T, phi::T) where T <: PolyRingElem
  dev = Vector{T}()
  g = f
  while degree(g) >= degree(phi)
    g, r = divrem(g, phi)
    push!(dev, r)
  end
  push!(dev, g)
  return dev
end

###############################################################################
#
#  Construction of Newton polygon
#
###############################################################################

@doc raw"""
    newton_polygon(f::PolyRingElem{T}, phi::PolyRingElem{T}) where T <: Union{PadicFieldElem, QadicFieldElem}

Computes the $\phi$-polygon of $f$, i.e. the lower convex hull of the points $(i, v(a_i))$
where $a_i$ are the coefficients of the $\phi$-development of $f$.
"""
function newton_polygon(f::T, phi::T) where T <: Generic.Poly{S} where S <: Union{QadicFieldElem, PadicFieldElem, LocalFieldElem}
  dev = phi_development(f, phi)
  a = Tuple{Int, Int}[]
  for i = 0:length(dev) -1
    if !iszero(dev[i+1])
      push!(a, (i, _valuation(dev[i+1])))
    end
  end
  P = lower_convex_hull(a)
  p = prime(base_ring(f))
  return NewtonPolygon(P, f, phi, p, dev)
end

#TODO: in Oscar/experimental/GaloisGrp are the "missing" functions
# - without phi
# - for QQFieldElem/ZZPolyRingElem and prime
# - over Q(t) with degree
@doc raw"""
    newton_polygon(f::ZZPolyRingElem, phi::ZZPolyRingElem, p::ZZRingElem)

Computes the $\phi$-polygon of $f$, i.e. the lower convex hull of the points $(i, v_p(a_i))$
where $a_i$ are the coefficients of the $\phi$-development of $f$.
"""
function newton_polygon(f::T, phi::T, p::ZZRingElem) where T
  dev = phi_development(f, phi)
  a = Tuple{Int, Int}[]
  for i = 0:length(dev) -1
    if !iszero(dev[i+1])
      push!(a, (i, valuation(dev[i+1], p)))
    end
  end
  P = lower_convex_hull(a)
  return NewtonPolygon(P, f, phi, p, dev)
end

function _newton_polygon(dev, p)
  a = Tuple{Int, Int}[]
  for i = 0:length(dev) -1
    if !iszero(dev[i+1])
      push!(a, (i, valuation(dev[i+1], p)))
    end
  end
  return lower_convex_hull(a)
end


function valuation(f::ZZPolyRingElem, p::Union{ZZRingElem, Int})
  l = Int[Int(valuation(coeff(f, i), p)) for i = 0:degree(f) if coeff(f, i)!=0]
  return minimum(l)
end

function valuation(f::Generic.Poly{AbsSimpleNumFieldElem}, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  l = Int[Int(valuation(coeff(f, i), p)) for i = 0:degree(f) if !iszero(coeff(f, i))]
  return minimum(l)
end

function _valuation(f::Generic.Poly{T}) where T <: Union{QadicFieldElem, PadicFieldElem}
  return minimum([valuation(coeff(f, i)) for i = 0:degree(f)])
end

function _valuation(f::Generic.Poly{<:LocalFieldElem})
  K = base_ring(f)
  e = absolute_ramification_index(K)
  return minimum(ZZRingElem[numerator(e*valuation(coeff(f, i))) for i = 0:degree(f)])
end

################################################################################
#
#  Construction of the residual polynomial
#
################################################################################

@doc raw"""
    residual_polynomial(N::NewtonPolygon{ZZPolyRingElem}, L::Line)

Computes the residual polynomial of the side $L$ of the Newton Polygon $N$.
"""
function residual_polynomial(N::NewtonPolygon{ZZPolyRingElem}, L::Line)
  F = GF(N.p, cached = false)
  Ft = polynomial_ring(F, "t", cached = false)[1]
  FF = finite_field(Ft(N.phi), "a", cached = false)[1]
  return residual_polynomial(FF, L, N.development, N.p)
end

function residual_polynomial(F, L::Line, dev::Vector{ZZPolyRingElem}, p::Union{Int, ZZRingElem})

  R = Native.GF(p, cached=false)
  cof = Vector{elem_type(F)}()
  Rx, x = polynomial_ring(R, "y", cached=false)
  s = L.points[1][1]
  e = denominator(L.slope)
  for i=0:degree(L)
    if !iszero(dev[Int(s+e*i+1)])
      el=Rx(divexact(dev[Int(s+e*i+1)], ZZRingElem(p)^(Int(L.points[1][2]+numerator(L.slope*i*e)))))
      push!(cof, F(el))
    else
      push!(cof, F(0))
    end
  end
  Fx, x = polynomial_ring(F,"x", cached=false)
  return Fx(cof)

end

function phi_development_with_quos(f::T, phi::T) where T <: PolyRingElem
  dev = Vector{T}()
  quos = Vector{T}()
  g = f
  while degree(g) >= degree(phi)
    g, r = divrem(g, phi)
    push!(dev, r)
    push!(quos, g)
  end
  push!(dev, g)
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
#  IsRegular (In the sense of Newton polygons) for fields at prime p
#
###############################################################################

function is_regular_at(f::ZZPolyRingElem, p::ZZRingElem)
  Zx = parent(f)
  R = Native.GF(p, cached = false)
  Rx = polynomial_ring(R, "y", cached = false)[1]
  f1 = Rx(f)
  sqf = factor_squarefree(f1)
  for (g, v) in sqf
    isone(v) && continue
    fac = factor(g)
    for (gg, v1) in fac
      phi = lift(Zx, gg)
      N = newton_polygon(f, phi, p)
      for lin in N.P.lines
        if slope(lin) < 0 && degree(lin) != 1
          rp = residual_polynomial(N, lin)
          if !is_squarefree(rp)
            return false
          end
        end
      end
    end
  end
  return true
end

###############################################################################
#
#  p-overorder using Polygons
#
###############################################################################

function gens_overorder_polygons(O::AbsSimpleNumFieldOrder, p::ZZRingElem)
  K = nf(O)
  f = K.pol
  Qx = parent(f)
  Zx, x = polynomial_ring(FlintZZ, "x", cached = false)
  R = Native.GF(p, cached = false)
  Rx, y = polynomial_ring(R, "y", cached = false)
  f1 = Rx(K.pol)
  sqf = factor_squarefree(f1)
  l = powers(gen(K), degree(K)-1)
  regular = true
  vdisc = 0
  for (gg, m) in sqf
    isone(m) && continue
    fac = factor(gg)
    for (g, m1) in fac
      F, a = Native.finite_field(g, "a", cached = false)
      phi = lift(Zx, g)
      dev, quos = phi_development_with_quos(Zx(f), phi)
      N = _newton_polygon(dev, p)
      if regular
        for lin in N.lines
          if slope(lin) < 0 && degree(lin) != 1
            rp = residual_polynomial(F, lin, dev, p)
            if !is_squarefree(rp)
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
            q1 = shift_left(quos[i], j-1)
            push!(l, divexact(K(q1), p^v))
          end
        end
      end
    end
  end
  B = basis_matrix(l, FakeFmpqMat)
  hnf_modular_eldiv!(B.num, B.den, :lowerleft)
  B = FakeFmpqMat(view(B.num, nrows(B)-degree(K)+1:nrows(B), 1:degree(K)), B.den)
  if !regular
    elt = Vector{AbsSimpleNumFieldElem}(undef, nrows(B))
    for i in 1:nrows(B)
      elt[i] = elem_from_mat_row(K, B.num, i, B.den)
    end
    O1 = _order_for_polygon_overorder(K, elt, inv(QQFieldElem(p^vdisc)))
  else
    O1 = AbsNumFieldOrder(K, B)
    O1.disc = divexact(O.disc, p^(2*vdisc))
    O1.index = p^vdisc
    push!(O1.primesofmaximality, p)
  end
  return O1

end


function polygons_overorder(O::AbsSimpleNumFieldOrder, p::ZZRingElem)
  #First, Dedekind criterion. If the Dedekind criterion says that we are p-maximal,
  # or it can produce an order which is p-maximal, we are done.
  Zy, y = polynomial_ring(FlintZZ, "y", cached = false)
  Kx, x = polynomial_ring(Native.GF(p, cached=false), "x", cached=false)

  f = nf(O).pol

  Zyf = Zy(f)

  fmodp = Kx(Zyf)

  fac = factor_squarefree(fmodp)

  g = prod(x for x in keys(fac.fac); init = one(fmodp))
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

    @hassert :AbsNumFieldOrder 1 rem(O.disc, p^2) == 0
    alpha = nf(O)(parent(f)(lift(Zy, U)))

    # build the new basis matrix
    # we have to take the representation matrix of alpha!
    # concatenating the coefficient vector won't help
    Malpha, d = representation_matrix_q(alpha)
    @assert isone(d)
    hnf_modular_eldiv!(Malpha, p, :lowerleft)
    b = FakeFmpqMat(Malpha, p)
    @hassert :AbsNumFieldOrder 1 defines_order(nf(O), b)[1]
    OO = AbsNumFieldOrder(nf(O), b)
    OO.is_equation_order = false
    OO.disc = divexact(O.disc, p^(2*(degree(O)-degree(U))))
    OO.index = p^(degree(O)-degree(U))
    push!(OO.primesofmaximality, p)
    return OO
  end
  return gens_overorder_polygons(O, p)

end

function _order_for_polygon_overorder(K::S, elt::Vector{T}, dold::QQFieldElem = QQFieldElem(0)) where {S, T}

  n = degree(K)
  closed = false
  Oattempt = AbsSimpleNumFieldOrder(elt)

  # Since 1 is in elt, prods will contain all elements
  first = true
  while !closed
    prods = T[elt[i] for i=1:length(elt)]
    for i = 2:length(elt)
      d = denominator(elt[i])
      for j = i:length(elt)
        d1 = denominator(elt[j])
        if isone(d) && isone(d1)
          continue
        end
        el = elt[i]*elt[j]
        if denominator(el) != 1 && !(el in Oattempt)
          push!(prods, el)
        end
      end
    end
    if length(prods) == n && first
      break
    end

    B = basis_matrix(prods, FakeFmpqMat)
    hnf_modular_eldiv!(B.num, B.den, :lowerleft)

    dd = B.num[nrows(B) - degree(K) + 1, 1]
    for i in 2:degree(K)
      dd = mul!(dd, dd, B.num[nrows(B) - degree(K) + i, i])
    end
    if iszero(dd)
      error("Elements do not define a module of full rank")
    end
    d = dd//(B.den)^n

    if dold == d
      closed = true
    else
      dold = d
      elt = Vector{T}(undef, n)
      for i in 1:n
        elt[i] = elem_from_mat_row(K, B.num, nrows(B) - n + i, B.den)
      end
    end
  end

  # Make an explicit check
  @hassert :AbsNumFieldOrder 1 defines_order(K, elt)[1]
  res = Order(K, elt, check = false, isbasis = true, cached = false)
  res.gen_index = inv(dold)
  res.index = numerator(res.gen_index)
  res.disc = divexact(numerator(discriminant(K)), res.index^2)
  return res
end

###############################################################################
#
#  Decomposition type using polygons
#
###############################################################################

function _from_algs_to_ideals(A::StructureConstantAlgebra{T}, OtoA::Map, AtoO::Map, Ip1, p::Union{ZZRingElem, Int}) where {T}

  O = order(Ip1)
  n = degree(O)
  @vprintln :AbsNumFieldOrder 1 "Splitting the algebra"
  AA = _dec_com_finite(A)
  @vprintln :AbsNumFieldOrder 1 "Done"
  ideals = Vector{Tuple{typeof(Ip1), Int}}(undef, length(AA))
  N = basis_matrix(Ip1, copy = false)
  list_bases = Vector{Vector{Vector{ZZRingElem}}}(undef, length(AA))
  for i = 1:length(AA)
    l = Vector{Vector{ZZRingElem}}(undef, dim(AA[i][1]))
    for j = 1:length(l)
      l[j] = coordinates(AtoO(AA[i][2](AA[i][1][j])))
    end
    list_bases[i] = l
  end
  for i = 1:length(AA)
    B = AA[i][1]
    BtoA = AA[i][2]
    #we need the kernel of the projection map from A to B.
    #This is given by the basis of all the other components.
    f = dim(B)
    N1 = vcat(N, zero_matrix(FlintZZ, dim(A) - f, n))
    t = 1
    for j = 1:length(AA)
      if j == i
        continue
      end
      for s = 1:length(list_bases[j])
        b = list_bases[j][s]
        for j = 1:degree(O)
          N1[n + t, j] = b[j]
        end
        t += 1
      end
    end
    N1 = view(hnf_modular_eldiv!(N1, ZZRingElem(p), :lowerleft), nrows(N1) - degree(O) + 1:nrows(N1), 1:degree(O))
    P = ideal(O, N1)
    P.minimum = ZZRingElem(p)
    P.norm = ZZRingElem(p)^f
    P.splitting_type = (0, f)
    P.is_prime = 1
    fromOtosimplealgebra = compose(OtoA, pseudo_inv(BtoA))
    compute_residue_field_data!(P, fromOtosimplealgebra)
    ideals[i] = (P, 0)
  end
  return ideals, AA
end

function _decomposition(O::AbsNumFieldOrder, I::AbsNumFieldOrderIdeal, Ip::AbsNumFieldOrderIdeal, T::AbsNumFieldOrderIdeal, p::Union{Int, ZZRingElem})
  #I is an ideal lying over p
  #T is contained in the product of all the prime ideals lying over p that do not appear in the factorization of I
  #Ip is the p-radical
  Ip1 = Ip + I
  A, OtoA = StructureConstantAlgebra(O, Ip1, p)

  if dim(A) == 1
    Ip1.norm = ZZRingElem(p)
    Ip1.minimum = ZZRingElem(p)
    Ip1.splitting_type = (0, 1)
    Ip1.is_prime = 1
    ideals = Vector{Tuple{ideal_type(O), Int}}(undef, 1)
    ideals[1] = (Ip1, Int(0))
  else
    AtoO = pseudo_inv(OtoA)
    ideals , AA = _from_algs_to_ideals(A, OtoA, AtoO, Ip1, p)
  end
  k = (1-1/BigInt(p))^degree(O) < 0.1


  if !k
    #The probability of finding a random generator is high
    for j in 1:length(ideals)

      P = ideals[j][1]
      f = P.splitting_type[2]
      #@vprintln :AbsNumFieldOrder 1 "Chances for finding second generator: ~$((1-1/BigInt(p)))"
      P.gen_one = ZZRingElem(p)
      @vtime :AbsNumFieldOrder 3 find_random_second_gen(P)
      u = P.gen_two
      modulo = norm(P)*p
      x = zero(parent(u))

     if is_simple(nf(O)) && is_defining_polynomial_nice(nf(O))
        if !is_norm_divisible_pp(u.elem_in_nf, modulo)
          x = u
        elseif !is_norm_divisible_pp(u.elem_in_nf+p, modulo)
          x = u + p
        end
      else
        if iszero(mod(norm(u), modulo))
          if !iszero(mod(norm(u+p), modulo))
            add!(u, u, p)
          elseif !iszero(mod(norm(u-p), modulo))
            sub!(u, u, p)
          end
        end
        x = u
      end

      @hassert :AbsNumFieldOrder 1 !iszero(x)
      @hassert :AbsNumFieldOrder 2 O*O(p) + O*x == P
      P.gen_two = x
      P.gens_normal = ZZRingElem(p)
      if !iszero(mod(discriminant(O), p)) || valuation(norm(I), p) == length(ideals)
        e = 1
      elseif length(ideals) == 1
        e = Int(divexact(valuation(norm(I), p), f))
      else
        anti_uni = anti_uniformizer(P)
        e = 1
        xyz = anti_uni^2*p
        while xyz in O
          e += 1
          mul!(xyz, xyz, anti_uni)
        end
        @hassert :AbsNumFieldOrder 3 e == Int(valuation(nf(O)(p), P))
      end
      P.splitting_type = e, f
      @hassert :AbsNumFieldOrder 3 is_consistent(P)
      ideals[j] = (P, e)
    end
  elseif length(ideals) > 1
    u2, v2 = idempotents(Ip1, T)
    for j in 1:length(ideals)
      P = ideals[j][1]
      f = P.splitting_type[2]

      #@vprintln :AbsNumFieldOrder 1 "Searching for 2-element presentation"
      # The following does not work if there is only one prime ideal
      # This is roughly Algorithm 6.4 of Belabas' "Topics in computational algebraic
      # number theory".
      # Compute Vp = P_1 * ... * P_j-1 * P_j+1 * ... P_g

      B, BtoA = AA[j]
      v1 = AtoO(BtoA(one(B)))
      u1 = 1 - v1
      @hassert :AbsNumFieldOrder 1 isone(u1+v1)
      @hassert :AbsNumFieldOrder 1 containment_by_matrices(u1, P)
      u = O()
      v = O()
      add!(u, u2, v2)
      mul!(u, u, u1)
      mul!(v, u2, v1)
      add!(u, u, v)
      mul!(v, v1, v2)
      #u = u1*(u2+v2) + u2*v1
      #v = v1*v2
      @hassert :AbsNumFieldOrder 1 isone(u + v)
      if is_simple(nf(O)) && is_defining_polynomial_nice(nf(O))
        u = O(mod(u.elem_in_nf, p))
      end

      @hassert :AbsNumFieldOrder 1 containment_by_matrices(u, P)
      modulo = norm(P)*p
      if iszero(mod(norm(u), modulo))
        if !iszero(mod(norm(u+p), modulo))
          add!(u, u, p)
        elseif !iszero(mod(norm(u-p), modulo))
          sub!(u, u, p)
        else
          Ba = basis(P, copy = false)
          for i in 1:degree(O)
            if !is_norm_divisible_pp((v*Ba[i] + u).elem_in_nf, modulo)
              u = v*Ba[i] + u
              break
            end
          end
        end
      end
      @hassert :AbsNumFieldOrder 1 !iszero(u)
      @hassert :AbsNumFieldOrder 2 O*O(p) + O*u == P
      P.gen_one = ZZRingElem(p)
      P.gen_two = u
      P.gens_normal = ZZRingElem(p)
      P.gens_weakly_normal = 1
      if !iszero(mod(discriminant(O), p)) || valuation(norm(I), p) == length(ideals)
        e = 1
      else
        anti_uni = anti_uniformizer(P)
        e = 1
        xyz = p*anti_uni^2
        while xyz in O
          e += 1
          mul!(xyz, xyz, anti_uni)
        end
        @hassert :AbsNumFieldOrder 3 e == Int(valuation(nf(O)(p), P))
      end
      @hassert :AbsNumFieldOrder 3 is_consistent(P)
      P.splitting_type = e, f
      ideals[j] = (P, e)
    end
  elseif !isone(T)
    P = ideals[1][1]
    f = P.splitting_type[2]
    u, v = idempotents(P, T)
    u = O(mod(u.elem_in_nf, p))
    x = zero(parent(u))
    modulo = norm(P)*p

    if !is_norm_divisible_pp(u.elem_in_nf, modulo)
      x = u
    elseif !is_norm_divisible_pp(u.elem_in_nf+p, modulo)
      x = u + p
    elseif !is_norm_divisible_pp(u.elem_in_nf-p, modulo)
      x = u - p
    else
      Ba = basis(P, copy = false)
      for i in 1:degree(O)
        if !is_norm_divisible((v*Ba[i] + u).elem_in_nf, modulo)
          x = v*Ba[i] + u
          break
        end
      end
    end
    @hassert :AbsNumFieldOrder 1 !iszero(x)
    @hassert :AbsNumFieldOrder 2 O*O(p) + O*x == P
    P.gen_one = ZZRingElem(p)
    P.gen_two = x
    P.gens_normal = ZZRingElem(p)
    P.gens_weakly_normal = 1
    if !iszero(mod(discriminant(O), p))
      e = 1
    else
      e = Int(divexact(valuation(norm(I), p), f))
    end
    P.splitting_type = e, f
    @hassert :AbsNumFieldOrder 3 is_consistent(P)
    ideals[1] = (P, e)
  else
    P = ideals[1][1]
    f = P.splitting_type[2]
    #There is only one prime ideal and the probability of finding a random generator is low.
    #I need one element of valuation 1.
    P2 = P*P
    x = find_elem_of_valuation_1(P, P2)
    @hassert :AbsNumFieldOrder 1 !iszero(x)
    @hassert :AbsNumFieldOrder 2 O*O(p) + O*x == P
    P.gen_one = ZZRingElem(p)
    P.gen_two = x
    P.gens_normal = p
    P.gens_weakly_normal = 1
    if !iszero(mod(discriminant(O), p))
      e = 1
    else
      e = Int(divexact(valuation(norm(I), p), f))
    end
    P.splitting_type = e, f
    @hassert :AbsNumFieldOrder 3 is_consistent(P)
    ideals[1] = (P, e)
  end
  return ideals
end


function find_random_second_gen(A::AbsNumFieldOrderIdeal{S, T}) where {S, T}
  O = order(A)
  K = nf(O)
  Amin2 = minimum(A, copy = false)^2
  Amind = gcd(minimum(A)^degree(O), minimum(A, copy = false)*norm(A))

  if norm(O(minimum(A))) == norm(A)
    A.gen_one = minimum(A)
    A.gen_two = O(minimum(A))
    A.gens_weakly_normal = true
    return nothing
  end
  B = Array{ZZRingElem}(undef, degree(O))

  gen = O()

  r = -Amin2:Amin2

  m = zero_matrix(FlintZZ, 1, degree(O))

  cnt = 0
  dBmat = denominator(basis_matrix(FakeFmpqMat, O, copy = false))
  while true
    cnt += 1
    if cnt > 1000
      error("Having a hard time find weak generators for $A")
    end

    rand!(B, r)

    # Put the entries of B into the (1 x d)-Matrix m
    for i in 1:degree(O)
      s = ccall((:fmpz_mat_entry, libflint), Ptr{ZZRingElem}, (Ref{ZZMatrix}, Int, Int), m, 0, i - 1)
      ccall((:fmpz_set, libflint), Nothing, (Ptr{ZZRingElem}, Ref{ZZRingElem}), s, B[i])
    end
    if iszero(m)
      continue
    end

    mul!(m, m, basis_matrix(A, copy = false))
    mul!(m, m, basis_matrix(FakeFmpqMat, O, copy = false).num)
    gen = elem_from_mat_row(K, m, 1, dBmat)
    if is_simple(K) && is_defining_polynomial_nice(K)
      gen = mod(gen, Amin2)
    end
    if iszero(gen)
      continue
    end
    if norm(A, copy = false) == _normmod(Amind, O(gen, false))
      A.gen_one = minimum(A)
      A.gen_two = O(gen, false)
      A.gens_weakly_normal = true
      break
    end
  end
  return nothing
end

function find_elem_of_valuation_1(P::AbsNumFieldOrderIdeal{S, T}, P2::AbsNumFieldOrderIdeal{S, T}) where {S, T}
  B = basis(P, copy = false)
  el = B[1]
  for i = 2:length(B)
    if !(B[i] in P2)
      el = B[i]
      break
    end
  end
  return el
end

function decomposition_type_polygon(O::AbsSimpleNumFieldOrder, p::Union{ZZRingElem, Int})
  K = nf(O)
  Zx, x = polynomial_ring(FlintZZ, "x", cached = false)
  f = Zx(K.pol)
  R = Native.GF(p, cached = false)
  Rx, y = polynomial_ring(R, "y", cached = false)
  f1 = change_base_ring(R, f, parent = Rx)
  @vprintln :AbsNumFieldOrder 1 "Factoring the polynomial"
  fac = factor(f1) #TODO: We don't need the factorization directly, but only the factorization of the non-squarefree part
  res = Tuple{Int, Int}[]
  l = Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}[]
  for (g, m) in fac
    @vprintln :AbsNumFieldOrder 1 "Doing $((g,m))"
    if m==1
      push!(res, (degree(g), 1))
      continue
    end
    phi = lift(Zx, g)
    dev = phi_development(f, phi)
    N = _newton_polygon(dev, p)
    if denominator(slope(N.lines[1])) == m
      push!(res, (degree(g), m))
      continue
    end
    Nl = filter(x -> slope(x)<0, N.lines)
    F, a = Native.finite_field(g, "a", cached = false)
    pols = dense_poly_type(elem_type(F))[]
    for ll in Nl
      rp = residual_polynomial(F, ll, dev, p)
      if is_squarefree(rp)
        push!(pols, rp)
      else
        break
      end
    end
    if length(Nl) != length(pols)
      I1 = ideal(O, ZZRingElem(p), O(K(parent(K.pol)(lift(Zx, g^m)))))
      I1.minimum = ZZRingElem(p)
      I1.norm = ZZRingElem(p)^(degree(g)*m)
      I2 = ideal(O, ZZRingElem(p), O(K(parent(K.pol)(lift(Zx, divexact(f1, g^m))))))
      if isone(I2.gen_two)
        I2.minimum = ZZRingElem(1)
      else
        I2.minimum = ZZRingElem(p)
      end

      push!(l, (I1, I2))
    else
      for i=1:length(pols)
        fact = factor(pols[i])
        s = denominator(slope(Nl[i]))
        for psi in keys(fact.fac)
          push!(res, (degree(phi)*degree(psi), s))
        end
      end
    end
  end
  if !isempty(l)
    Ip = pradical1(O, p)
    for (I, J) in l
      lp = _decomposition(O, I, Ip, J, p)
      for (P, e) in lp
        push!(res, (P.splitting_type[2], e))
      end
    end
  end
  @assert sum(x[1]*x[2] for x = res) == degree(O)
  return res

end

###############################################################################
#
#  Prime decomposition
#
###############################################################################

function prime_decomposition_polygons(O::AbsSimpleNumFieldOrder, p::Union{ZZRingElem, Int}, degree_limit::Int = 0, lower_limit::Int = 0)
  if degree_limit == 0
    degree_limit = degree(O)
  end
  K = nf(O)
  f = K.pol
  Zx = polynomial_ring(FlintZZ, "x", cached = false)[1]
  R = Native.GF(p, cached = false)
  Rx, y = polynomial_ring(R, "y", cached = false)
  f1 = Rx(K.pol)
  @vprintln :AbsNumFieldOrder 1 "Factoring the polynomial"
  @vtime :AbsNumFieldOrder 1 fac = factor(f1)
  res = Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, Int}[]
  l = Tuple{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}[]
  for (g, m) in fac
    if degree(g) > degree_limit
      continue
    end
    @vprintln :AbsNumFieldOrder 1 "Doing $((g, m))"
    phi = lift(Zx, g)
    if isone(m)
      ei = m
      t = parent(f)(phi)
      b = K(t)
      J = AbsNumFieldOrderIdeal(O)
      J.gen_one = ZZRingElem(p)
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

      if !((ei > 1) || !is_norm_divisible_pp(b, (J.norm)*p))
        J.gen_two = J.gen_two + O(p)
      end

      J.gens_normal = p
      J.gens_weakly_normal = true
      push!(res, (J, ei))
      continue
    end
    #TODO: p-adic factorization of the polynomial.
    i1 = ideal(O, ZZRingElem(p), O(K(parent(f)(lift(Zx, g^m))), false))
    i1.minimum = p
    i2 = ideal(O, ZZRingElem(p), O(K(parent(f)(lift(Zx, divexact(f1, g^m)))), false))
    i2.minimum = p
    push!(l, (i1, i2))
  end
  if !isempty(l)
    @vtime :AbsNumFieldOrder 3 Ip = pradical1(O, p)
    for (I, Q) in l
      @vtime :AbsNumFieldOrder 3 lp = _decomposition(O, I, Ip, Q, p)
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
