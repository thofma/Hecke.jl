################################################################################
#
#  RieSrf/Numerics/Auxiliary.jl : auxiliary functions
#
#  Embedding number field elements and polynomials into C (with relative
#  precision, thread safe), small helpers for balls (ordering of the sheets,
#  closest points), and the interior points of the Newton polygon (Baker's
#  basis of differentials).
#
################################################################################

################################################################################
#
#  Auxiliary functions for computation over the complex numbers
#
################################################################################

# x reduced to [0, 2pi] (for balls that straddle 0 or 2pi: as far as the
# comparisons decide).
function _mod2pi(x::ArbFieldElem)
  pi2 = 2*const_pi(parent(x))
  while x < 0
    x += pi2
  end

  while x > pi2
    x -= pi2
  end

  return x
end

# The image of c under the embedding with *relative* precision prec.
# (evaluate(c, emb, prec) guarantees an absolute error 2^-prec only. For a
# small coefficient, e.g. 10^-32 in front of x^32, that leaves ~prec - 106
# relative bits, and far out on a path (|x| ~ 50, |x|^32 ~ 2^180) the
# polynomial, and with it the roots y, lost ~160 bits.)
function _embed_coefficient(c, emb, prec::Int)
  iszero(c) && return AcbField(prec)(0)
  c isa QQFieldElem && return AcbField(prec)(c)
  q = 64
  e = _evaluate_locked(c, emb, q)
  while contains_zero(abs(e))
    q *= 2
    e = _evaluate_locked(c, emb, q)
  end
  RR = ArbField(64)
  l = Nemo.midpoint(log(RR(abs(e))) / log(RR(2)))
  extra = max(0, -Int(floor(ZZRingElem, l))) + 2
  return AcbField(prec)(_evaluate_locked(c, emb, prec + extra))
end

# Hecke caches the roots of the defining polynomial of a number field per
# precision in a Dict on the field (conjugate_data_arb_roots), which is not
# thread safe; the period computation embeds polynomials in threaded loops
# (e.g. the integrand bounds). A new precision there corrupted the Dict
# (UndefRefError in rehash!). So all evaluations of embeddings go through
# this lock. (Not const, by the Hecke policy for package code; the global is
# never reassigned.)
_embedding_lock = ReentrantLock()

_evaluate_locked(c, emb, prec::Int) = lock(() -> evaluate(c, emb, prec), _embedding_lock)

# The polynomial f over the number field, with its coefficients embedded by
# the place v at (relative) precision prec, in C[x] (cached ring, variable x).
function _embed_poly(f::PolyRingElem{AbsSimpleNumFieldElem}, v::Union{PosInf, InfPlc}, prec::Int = 100)
  Cx, _ = polynomial_ring(AcbField(prec), "x")
  return Cx([_embed_coefficient(c, v.embedding, prec) for c in coefficients(f)])
end

# The same for a multivariate polynomial, in C[x, y, ...] with the variable
# names of f.
function _embed_mpoly(f::MPolyRingElem, v::Union{PosInf, InfPlc}, prec::Int = 100)
  CCx, _ = polynomial_ring(AcbField(prec), symbols(parent(f)))
  context = MPolyBuildCtx(CCx)
  for (c, e) in zip(coefficients(f), exponent_vectors(f))
    push_term!(context, _embed_coefficient(c, v.embedding, prec), e)
  end
  return finish(context)
end

# The homogenization F(x, y, z) of f(x, y).
function homogenization_RS(f::MPolyRingElem)
  m = total_degree(f)
  k = coefficient_ring(f)
  ktuv, (x1, x2, x3) = polynomial_ring(k, [:x,:y,:z])
  f_hom = ktuv(0)
  for term in terms(f)
    i = m - total_degree(term)
    f_hom += term(x1,x2) * x3^i
  end
  return f_hom
end

@doc raw"""
    sheet_ordering(z1::AcbFieldElem, z2::AcbFieldElem) -> Bool

The lexicographic order on C used to number the sheets: z1 < z2 if
Re(z1) < Re(z2), or if the real parts cannot be distinguished and
Im(z1) < Im(z2). Throws an error if the two balls cannot be compared
(neither the real nor the imaginary parts can be distinguished).
"""
function sheet_ordering(z1::AcbFieldElem,z2::AcbFieldElem)
  if real(z1) < real(z2)
    return true
  elseif real(z1) > real(z2)
    return false
  elseif imag(z1) < imag(z2)
    return true
  elseif imag(z2) < imag(z1)
    return false
  end
  error("sheet_ordering: the points $z1 and $z2 cannot be compared at this precision.")
end

# x with its real or imaginary part set to zero if that part contains zero.
# Useful before functions like arg or log, whose output would otherwise get
# a radius of about pi for a ball around a point on an axis.
function trim_zero(x::AcbFieldElem)
  CC = parent(x)
  RR = ArbField(precision(CC))
  if contains(abs(real(x)), zero(RR))
    x = CC(imag(x))*onei(CC)
  end
  if contains(abs(imag(x)), zero(RR))
    x = CC(real(x))
  end
  return x
end

# The distance from x0 to the closest of the points, and its index (the
# first one if the comparison is undecided).
function closest_point(x0::AcbFieldElem, points::Vector{AcbFieldElem})
  closest = 1
  distance = abs(x0 - points[1])
  for i in (2:length(points))
    new_distance = abs(x0 - points[i])
    if distance > new_distance
      closest = i
      distance = new_distance
    end
  end
  return distance, closest
end

################################################################################
#
#  Newton polygon
#
################################################################################

# The interior lattice points (i, j) of the Newton polygon of f(x, y) (the
# convex hull of the exponent vectors of its terms); for Baker's basis
# x^(i-1) y^(j-1) dx / f_y. Only points with i + j <= total degree - 1 can be
# interior.
function _newton_polygon_interior_points(f::MPolyRingElem)
  points = [degrees(mon) for mon in monomials(f)]
  vertices = _convex_hull(points)
  n = length(vertices)
  edges = vcat([_line_equation(vertices[i-1], vertices[i]) for i in 2:n],
               _line_equation(vertices[end], vertices[1]))
  center = sum(vertices)//n
  result = Vector{Int}[]
  d = total_degree(f) - 3
  for i in 0:d, j in 0:d-i
    # strictly on the same side of every edge as the center
    if all([sign(h(i + 1, j + 1)) == sign(h(center[1], center[2])) for h in edges])
      push!(result, [i + 1, j + 1])
    end
  end
  return result
end

# The vertices of the convex hull of the points in the plane, in order
# (lower hull from left to right, then upper hull back; gift wrapping by the
# smallest slope). Two points: both.
function _convex_hull(points::Vector{Vector{Int}})
  points = sort(points)

  # Take care of trivial case with 1 or 2 elements
  if length(points) == 1
    error("Convex hull of 1 point is not defined")
  elseif length(points) == 2
    return([points[1], points[2]])
  else
    points_lower_convex_hull = Vector{Int}[points[1]]
    i = 2
    while i<= length(points)
      y = points_lower_convex_hull[end]
      sl = [_slope(y, x) for x = points[i:end]]
      min_sl = minimum(sl)
      p = findlast(x->x == min_sl, sl)::Int
      push!(points_lower_convex_hull, points[p+i-1])
      i += p
    end

    points = reverse(points)
    points_upper_convex_hull = Vector{Int}[points[1]]
    i = 2
    while i<= length(points)
      y = points_upper_convex_hull[end]
      sl = [_slope(y, x) for x = points[i:end]]
      min_sl = minimum(sl)
      p = findlast(x->x == min_sl, sl)::Int
      push!(points_upper_convex_hull, points[p+i-1])
      i += p
    end
    return vcat(points_lower_convex_hull[1:end-1], points_upper_convex_hull[1:end-1])
  end
end

# The slope from a to b (Hecke's inf for a vertical line).
function _slope(a::Vector{Int}, b::Vector{Int})
  if b[1] == a[1]
    return inf
  end
  return QQFieldElem(b[2]-a[2], b[1]-a[1])
end

# An equation of the line through the points a and b in the plane.
function _line_equation(a::Vector{Int}, b::Vector{Int})
  Qxy, (x,y) = polynomial_ring(QQ, ["x","y"])
  if b[1] == a[1]
    return x - a[1]
  end
  c = _slope(a,b)
  return  c*x - y - c*b[1] + b[2]
end
