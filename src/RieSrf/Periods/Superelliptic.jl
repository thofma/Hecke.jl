################################################################################
#
#  RieSrf/Superelliptic.jl : period matrices of superelliptic curves y^m = p(x)
#
#  The algorithm of Molin and Neurohr ("Computing period matrices and the
#  Abel-Jacobi map of superelliptic curves", Math. Comp. 2019), following
#  Neurohr's Magma implementation, but with ball arithmetic and a certified
#  choice of the branch of y along the edges:
#
#   * a spanning tree between the n branch points (greedy by the quadrature
#     parameter, without crossing edges, in Float64);
#   * on the edge from a to b, x = hd*u + mid with hd = (b - a)/2 and
#     u in [-1, 1], and
#         y(u) = K * (1 - u^2)^(1/m) * Y(u),   Y(u)^m = prod_q f_q(u),
#     where f_q(u) = u_q - u if Re(u_q) > 0 and u - u_q otherwise (u_q the
#     other branch points), Y the branch exp((1/m) sum_q Log f_q(u)) (each Log
#     is continuous on [-1, 1]), and K = lc^(1/m) * hd^(n/m) * eps with
#     eps^m = (-1)^(up + 1), up = #{q : Re(u_q) > 0};
#   * the integrals of x^i dx / y^j along the edge on this branch, with
#     Gauss-Chebyshev (m = 2) or double exponential quadrature (the weight
#     (1 - u^2)^(-j/m) is part of the scheme);
#   * the cycles "edge on sheet l minus edge on sheet l+1", their intersection
#     numbers (from the configuration of the lifts at the common end points
#     of the edges), and a symplectic basis.
#
#  Gauss-Jacobi quadrature for m > 2 (Neurohr's default) and the Abel-Jacobi
#  map are not implemented yet; for m > 2 all edges use double exponential
#  integration.
#
################################################################################

################################################################################
#
#  Recognizing superelliptic curves
#
################################################################################

# If f = c*y^m + q(x) (swapped = false) or f = c*x^m + q(y) (swapped = true)
# with m >= 2 and q separable of degree n >= 3: (m, p, swapped) with
# p = -q/c in k[t]. Otherwise nothing.
function _superelliptic_form(f::MPolyRingElem)
  k = base_ring(f)
  for (yv, xv, swapped) in ((2, 1, false), (1, 2, true))
    m = 0
    c = zero(k)
    ok = true
    qterms = Tuple{Int, elem_type(k)}[]
    for i in 1:length(f)
      e = exponent_vector(f, i)
      if e[yv] == 0
        push!(qterms, (e[xv], coeff(f, i)))
      elseif e[xv] == 0 && m == 0
        m = e[yv]
        c = coeff(f, i)
      else
        ok = false
        break
      end
    end
    (ok && m >= 2) || continue
    kt, t = polynomial_ring(k, :t; cached = false)
    p = -sum((a * t^d for (d, a) in qterms); init = zero(kt)) * inv(c)
    degree(p) >= 3 || continue
    isone(gcd(p, derivative(p))) || continue
    return (m, p, swapped)
  end
  return nothing
end

# The SuperellipticModel of RS, or nothing if the curve is not superelliptic.
# Cheap: nothing numerical is computed.
function _superelliptic_model(RS::RiemannSurface)
  f = RS.input_polynomial
  form = _superelliptic_form(f)
  form === nothing && return nothing
  m, p, swapped = form
  k = base_ring(f)
  R = parent(f)
  X, Y = gens(R)
  C = SuperellipticModel()
  C.surface = RS
  C.transform = swapped ? _swap_matrix(k) : identity_matrix(k, 3)
  C.defining_polynomial = Y^m - sum((coeff(p, d) * X^d for d in 0:degree(p)); init = zero(R))
  C.p = p
  C.m = m
  C.n = degree(p)
  C.delta = gcd(m, C.n)
  C.genus = div((m - 1)*(C.n - 1) - C.delta + 1, 2)
  C.embedding = RS.embedding
  C.initial_precision = RS.precision
  C.parameters = copy(RS.parameters)
  # x^i dx / y^j for 1 <= j <= m-1 and 0 <= i < floor((j*n - delta)/m)
  C.differentials = [(i, j) for j in 1:m-1 for i in 0:div(j*C.n - C.delta, m)-1]
  @assert length(C.differentials) == C.genus
  return C
end

@doc raw"""
    riemann_surface(p::PolyRingElem, m::Int, prec::Int = 100; kw...) -> RiemannSurface
    riemann_surface(p::PolyRingElem, m::Int, v, prec::Int = 100; kw...) -> RiemannSurface

The Riemann surface of the superelliptic curve y^m = p(x), for p separable of
degree at least 3 over QQ or a number field (embedded by the infinite place
v, by default the first one). The period matrices are computed with the
algorithm for superelliptic curves (`model = :superelliptic`). Further
keywords are integration parameters, see `riemann_surface`.
"""
function riemann_surface(p::PolyRingElem, m::Int, prec::Int = 100; kw...)
  k = base_ring(p)
  kk = k == QQ ? rationals_as_number_field()[1] : k
  return riemann_surface(p, m, infinite_places(kk)[1], prec; kw...)
end

function riemann_surface(p::PolyRingElem, m::Int, v::Union{PosInf, InfPlc}, prec::Int = 100; kw...)
  @req m >= 2 "m must be at least 2."
  R, (x, y) = polynomial_ring(base_ring(p), [:x, :y]; cached = false)
  f = y^m - sum((coeff(p, d) * x^d for d in 0:degree(p)); init = zero(R))
  return riemann_surface(f, v, prec; model = :superelliptic, kw...)
end

################################################################################
#
#  Basic data
#
################################################################################

genus(C::SuperellipticModel) = C.genus
embedding(C::SuperellipticModel) = C.embedding
precision(C::SuperellipticModel) = C.initial_precision
defining_polynomial(C::SuperellipticModel) = C.defining_polynomial
integration_parameters(C::SuperellipticModel) = copy(C.parameters)
resolved_integration_parameters(C::SuperellipticModel) =
  isdefined(C, :resolved_parameters) ? copy(C.resolved_parameters) : nothing

function Base.show(io::IO, C::SuperellipticModel)
  print(io, "Superelliptic model y^$(C.m) = $(C.p) of genus $(C.genus)")
end

@doc raw"""
    basis_of_differentials(C::SuperellipticModel) -> Vector{FunFldDiff}

The basis x^i dx / y^j of the holomorphic differentials of y^m = p(x) used
for the period matrices, in the order of the rows of the big period matrix.
"""
function basis_of_differentials(C::SuperellipticModel)
  isdefined(C, :basis_of_differentials) && return C.basis_of_differentials
  f0 = C.defining_polynomial
  k0 = base_ring(f0)
  kx0, x0 = rational_function_field(k0, "x")
  kxy0, y0 = polynomial_ring(kx0, "y")
  F0, a = function_field(f0(x0, y0))
  xF = F0(x0)
  C.basis_of_differentials = [FunFldDiff(xF^i * inv(a)^j) for (i, j) in C.differentials]
  return C.basis_of_differentials
end

@doc raw"""
    homology_basis(C::SuperellipticModel) -> Tuple

The spanning tree (edges between the branch points), the intersection matrix
of the cycles "edge k on sheet l minus edge k on sheet l+1" (index
(k-1)*(m-1) + l), and the symplectic transformation whose first 2g rows give
the symplectic homology basis of the period matrices.
"""
function homology_basis(C::SuperellipticModel)
  big_period_matrix(C)
  return C.tree, C.intersection_matrix, C.symplectic_transform
end

################################################################################
#
#  Small helpers
#
################################################################################

_c64(z::AcbFieldElem) = ComplexF64(_arb_mid_f64(real(z)), _arb_mid_f64(imag(z)))

# Decisions that select a branch must not depend on rounding noise, otherwise
# the result is a valid period matrix, but for different bases at different
# precisions. The typical case: a real polynomial, an edge between two complex
# conjugate branch points, and the real branch points on the imaginary axis of
# its u-coordinate (Re(u) is zero up to noise).
_near_zero(t::Float64, scale::Float64) = abs(t) <= 1e-10 * max(scale, 1e-300)

# the argument of z in (-pi, pi], with pi for (numerically) negative reals
function _stable_angle(z::ComplexF64)
  real(z) < 0 && _near_zero(imag(z), abs(z)) && return Float64(pi)
  return angle(z)
end

# the factor of u_q in Y is u_q - u (true) or u - u_q (false); for Re(u_q)
# numerically zero decide by the sign of Im(u_q) (either choice is continuous
# on [-1, 1], but it has to be the same at every precision)
_factor_sign(u::ComplexF64) = _near_zero(real(u), abs(u)) ? imag(u) > 0 : real(u) > 0

function _embed_coefficient(c, v, CC::AcbField)
  c isa QQFieldElem && return CC(c)
  return CC(evaluate(c, v.embedding, precision(CC)))
end

_embed_poly(p::PolyRingElem, v, CC::AcbField) =
  polynomial_ring(CC, "t"; cached = false)[1]([_embed_coefficient(coeff(p, d), v, CC) for d in 0:degree(p)])

# z^q for a rational q, on the branch with the argument of z taken near its
# Float64 argument theta: (z e^{-i theta})^q e^{i q theta}. Any Float64 theta
# gives a valid branch (the result to the power den(q) is z^num(q)); the
# rotation keeps the principal root away from its branch cut, also when z is
# (numerically) a negative real number.
function _rotated_power(z::AcbFieldElem, q::Rational{Int})
  CC = parent(z)
  theta = _stable_angle(_c64(z))
  I = onei(CC)
  w = z * exp(-I * CC(theta))
  qC = CC(numerator(q)) / denominator(q)
  return exp(qC * log(w)) * exp(I * qC * CC(theta))
end

################################################################################
#
#  Spanning tree and quadrature parameters (Float64)
#
################################################################################

# u-coordinates of the branch points other than a, b for the edge a -> b
function _edge_u(P::Vector{ComplexF64}, a::Int, b::Int)
  hd = (P[b] - P[a]) / 2
  mid = (P[a] + P[b]) / 2
  return [(P[q] - mid) / hd for q in eachindex(P) if q != a && q != b]
end

# ellipse parameter (|u+1| + |u-1|)/2 of u: u lies on the ellipse E_r with foci +-1
_ellipse_parameter(u::ComplexF64) = (abs(u + 1) + abs(u - 1)) / 2

# half width of the largest strip |Im t| < r whose image under
# t -> tanh(pi/2 sinh t) avoids u
_de_parameter(u::ComplexF64) = abs(imag(asinh(atanh(u) / (pi/2))))

_gj_weight(U::Vector{ComplexF64}) = minimum(_ellipse_parameter, U; init = 5.0)
_de_weight(U::Vector{ComplexF64}) = minimum(_de_parameter, U; init = pi/2)

# A spanning tree between the branch points that is good for the quadrature:
# greedy (Prim-like) by the weight w(a, b) (larger is better), but without
# edges that cross an edge already in the tree, since the intersection numbers
# below assume that edges only meet at common end points. The edges are listed
# in the order they are added; each goes from a vertex already in the tree to
# a new one.
function _orient(a::ComplexF64, b::ComplexF64, c::ComplexF64)
  return imag(conj(b - a) * (c - a))
end

function _segments_cross(p1::ComplexF64, p2::ComplexF64, q1::ComplexF64, q2::ComplexF64)
  o1, o2 = _orient(p1, p2, q1), _orient(p1, p2, q2)
  o3, o4 = _orient(q1, q2, p1), _orient(q1, q2, p2)
  return o1*o2 < 0 && o3*o4 < 0
end

function _spanning_tree(P::Vector{ComplexF64}, weight)
  n = length(P)
  pairs = [(weight(P, a, b), a, b) for a in 1:n for b in a+1:n]
  sort!(pairs, by = first, rev = true)
  intree = falses(n)
  edges = SuperellipticEdge[]
  while length(edges) < n - 1
    found = false
    for (_, a, b) in pairs
      if isempty(edges)
        push!(edges, SuperellipticEdge(a, b))
        intree[a] = intree[b] = true
        found = true
        break
      end
      intree[a] == intree[b] && continue
      a, b = intree[a] ? (a, b) : (b, a)
      any(E -> length(unique([E.a, E.b, a, b])) == 4 &&
               _segments_cross(P[E.a], P[E.b], P[a], P[b]), edges) && continue
      push!(edges, SuperellipticEdge(a, b))
      intree[b] = true
      found = true
      break
    end
    @req found "Could not find a spanning tree without crossing edges between the branch points."
  end
  return edges
end

# log of the largest |integrand| factor over the differentials:
# log|hd| + max_{(i,j)} (i log X - j log|K| + j logYinv)
function _log_bound(C::SuperellipticModel, loghd::Float64, logK::Float64, logX::Float64, logYinv::Float64)
  return loghd + maximum(i*logX + j*(logYinv - logK) for (i, j) in C.differentials)
end

# Choose method, N (and h) for the edge; target: absolute error 2^-target for
# the integrals of all differentials along the edge.
# (Gauss-Jacobi rules for m > 2 were tried: they need 2.5-3.5 times fewer
# evaluations of y than double exponential integration, but one rule per power
# of y, and computing the rules (O(N^2) at the working precision, with guard
# bits growing with N) made them 7-13 times slower at 500-1000 bits.)
function _edge_parameters!(C::SuperellipticModel, E::SuperellipticEdge, P::Vector{ComplexF64},
                           loglc::Float64, style::String)
  m, n = C.m, C.n
  U = _edge_u(P, E.a, E.b)
  hd = (P[E.b] - P[E.a]) / 2
  mid = (P[E.a] + P[E.b]) / 2
  loghd = log(abs(hd))
  logK = (loglc + n*loghd) / m
  D = C.target_precision * log(2.0)
  rgj = _gj_weight(U)
  use_cheb = m == 2 && (style == "GL" || (style == "Mixed" && rgj >= 1.005))
  if use_cheb
    E.method = :chebyshev
    @req rgj > 1 + 1e-12 "A branch point lies on an edge of the spanning tree."
    r = rgj >= 1 + 1/250 ? rgj - 1/500 : (rgj + 1)/2
    E.r = r
    logYinv = -sum(log(_ellipse_parameter(u) - r) for u in U; init = 0.0) / m
    logX = log(abs(hd)*r + abs(mid))
    logM = _log_bound(C, loghd, logK, logX, logYinv)
    E.N = max(2, ceil(Int, (D + logM + log(2*pi) + 1) / (2*acosh(r))))
    E.h = 0.0
  else
    E.method = :de
    rde = _de_weight(U)
    @req rde > 1e-12 "A branch point lies on an edge of the spanning tree."
    r = (29/30) * rde
    E.r = r
    alpha = 1/m
    # M1: on the segment [-1, 1]
    dist1(u) = abs(real(u)) > 1 ? abs(complex(abs(real(u)) - 1, imag(u))) : abs(imag(u))
    logYinv1 = -sum(log(dist1(u)) for u in U; init = 0.0) / m
    logX1 = log(max(abs(P[E.a]), abs(P[E.b]), 1e-300))
    logM1 = _log_bound(C, loghd, logK, logX1, logYinv1)
    # M2: on the boundary of the image of the strip |Im t| < r
    tmax = acosh(1/sin(r))
    logM2 = -Inf
    for s in 0:20
      z0 = tanh(pi/2 * sinh(complex(s/20*tmax, r)))
      for z in (z0, -z0, conj(z0), -conj(z0))
        logYinv = -sum(log(max(abs(z - u), 1e-300)) for u in U; init = 0.0) / m
        logX = log(abs(hd)*abs(z) + abs(mid))
        logM2 = max(logM2, _log_bound(C, loghd, logK, logX, logYinv))
      end
    end
    # Neurohr's parameters for integrands with endpoint singularities (1-u^2)^(alpha-1)
    Xr = cos(r) * sqrt(1/sin(r) - 1)
    B = (2/cos(r)) * ((Xr/2) * (1/cos(pi/2*sin(r))^(2*alpha) + 1/Xr^(2*alpha))) +
        1/(2*alpha*sinh(Xr)^(2*alpha))
    l = log(2.0) + logM2 + log(B)
    L2 = l > 30 ? l : log1p(exp(l))
    E.h = 2*pi*r / (D + L2)
    E.N = max(1, ceil(Int, asinh((D + (2*alpha + 1)*log(2.0) + logM1 - log(alpha)) / (alpha*pi)) / E.h))
    logM = max(logM1, logM2)
  end
  E.log2_bound = logM / log(2.0)
  return E
end

################################################################################
#
#  Integration along an edge
#
################################################################################

# The data of the edge at the working precision.
struct _SEEdgeData
  hd::AcbFieldElem             # (b - a)/2
  mid::AcbFieldElem            # (a + b)/2
  uq::Vector{AcbFieldElem}     # the other branch points in the u-coordinate
  uqf::Vector{ComplexF64}
  pos::Vector{Bool}            # factor u_q - u (true) or u - u_q (false)
  K::AcbFieldElem              # y = K (1-u^2)^(1/m) Y(u)
  Cab::AcbFieldElem            # hd^(n/m) * eps (Neurohr's C_ab up to 2^(n/m))
end

# one_sided: the edge from a branch point a to a point b that is not a branch
# point (Abel-Jacobi map). Then y = K (1+u)^(1/m) Y(u) with eps^m = (-1)^up.
function _se_edge_data(C::SuperellipticModel, E::SuperellipticEdge, P::Vector{AcbFieldElem},
                       L::AcbFieldElem; one_sided::Bool = false)
  CC = parent(P[1])
  m, n = C.m, C.n
  a, b = P[E.a], P[E.b]
  hd = (b - a) / 2
  mid = (a + b) / 2
  uq = [(P[q] - mid) / hd for q in eachindex(P) if q != E.a && q != E.b]
  uqf = [_c64(u) for u in uq]
  pos = [_factor_sign(u) for u in uqf]
  up = count(pos)
  eps = isodd(one_sided ? up : up + 1) ? exp(onei(CC) * const_pi(CC) / m) : one(CC)
  Cab = _rotated_power(hd, n//m) * eps
  return _SEEdgeData(hd, mid, uq, uqf, pos, L * Cab, Cab)
end

# Y(u) for real u (uf its Float64 value): the branch of (prod_q f_q(u))^(1/m)
# with argument (1/m) sum_q Arg f_q(u). The Float64 sum of the arguments only
# selects the branch (an error below pi is harmless).
function _se_Y(D::_SEEdgeData, u::AcbFieldElem, uf::Float64, m::Int)
  CC = parent(D.hd)
  Pr = one(CC)
  theta = 0.0
  for q in eachindex(D.uq)
    if D.pos[q]
      Pr *= D.uq[q] - u
      theta += angle(D.uqf[q] - uf)
    else
      Pr *= u - D.uq[q]
      theta += angle(uf - D.uqf[q])
    end
  end
  I = onei(CC)
  w = Pr * exp(-I * CC(theta))
  root = m == 2 ? sqrt(w) : exp(log(w) / m)
  return root * exp(I * CC(theta) / m)
end

# The integrals of the differentials x^i dx / y^j along the edge, on the
# reference branch y = K (1-u^2)^(1/m) Y(u).
function _se_edge_integrals(C::SuperellipticModel, E::SuperellipticEdge, D::_SEEdgeData;
                            one_sided::Bool = false)
  CC = parent(D.hd)
  RR = ArbField(precision(CC))
  m = C.m
  g = C.genus
  imax = maximum(first, C.differentials)
  acc = [zero(CC) for _ in 1:g]
  xpow = [one(CC) for _ in 0:imax]
  fj = [one(CC) for _ in 0:m-1]

  function add_node!(u::ArbFieldElem, w::ArbFieldElem, sing::Union{Nothing, ArbFieldElem})
    uf = _arb_mid_f64(u)
    uC = CC(u)
    Yinv = inv(_se_Y(D, uC, uf, m))
    if sing !== nothing
      Yinv *= sing                           # (1-u^2)^(-1/m)
    end
    x = D.hd * uC + D.mid
    for i in 1:imax
      xpow[i + 1] = xpow[i] * x
    end
    for j in 1:m-1
      fj[j + 1] = fj[j] * Yinv
    end
    wC = CC(w)
    for (d, (i, j)) in enumerate(C.differentials)
      acc[d] += wC * xpow[i + 1] * fj[j + 1]
    end
  end

  if E.method === :chebyshev
    @assert !one_sided
    # (1-u^2)^(-1/2) is the weight of the scheme (m = 2, j = 1)
    abscissae, weights = gauss_chebyshev_integration_points(E.N, precision(CC))
    for k in eachindex(abscissae)
      add_node!(abscissae[k], weights[k], nothing)
    end
  else
    # tanh-sinh: u = tanh(s), s = pi/2 sinh(t), du = pi/2 cosh(t)/cosh(s)^2 dt,
    # 1 - u^2 = 1/cosh(s)^2, so (1-u^2)^(-1/m) = cosh(s)^(2/m) exactly.
    h = RR(E.h)
    piR2 = const_pi(RR) / 2
    for k in -E.N:E.N
      t = k * h
      s = piR2 * sinh(t)
      cs = cosh(s)
      u = tanh(s)
      w = piR2 * h * cosh(t) / cs^2
      # (1-u^2)^(-1/m) = cosh(s)^(2/m); one-sided: (1+u)^(-1/m) = (cosh(s) e^(-s))^(1/m)
      sing = one_sided ? exp((log(cs) - s) / m) : exp(log(cs) * 2 / m)
      add_node!(u, w, sing)
    end
  end

  Kinv = inv(D.K)
  res = Vector{AcbFieldElem}(undef, g)
  Kpow = [one(CC)]
  for j in 1:m-1
    push!(Kpow, Kpow[end] * Kinv)
  end
  for (d, (i, j)) in enumerate(C.differentials)
    res[d] = D.hd * Kpow[j + 1] * acc[d]
  end
  return res
end

################################################################################
#
#  Intersection numbers
#
################################################################################

#  Near a branch point P (a simple root of p), s = (x - P)^(1/m) is a local
#  coordinate and y is a constant times s. The lift of an edge e at P on the
#  sheet y = zeta^l y_ref leaves P along the ray of angle A_e + 2 pi l/m in the
#  s-plane (up to a constant common to all edges at P), where A_e is the
#  argument of y_ref near P, i.e. of K_e * Y_e(-1) (P the start of e) or
#  K_e * Y_e(+1) (P the end of e). The cycle c_{e,l} = (edge on sheet l-1) -
#  (edge on sheet l) passes through P along two adjacent rays; two such cycles
#  at P cross iff the rays of one separate the rays of the other. Sign: +1 if
#  the second cycle crosses from the right to the left of the first (the
#  standard orientation; the s-plane is oriented like the x-plane).
#  Consecutive cycles of the same edge meet along a whole lift; perturbing it
#  gives c_{e,l} . c_{e,l+1} = 1 (as in Molin-Neurohr).

_in_ccw_sector(x::Float64, from::Float64, to::Float64) =
  0 < mod(x - from, 2*pi) < mod(to - from, 2*pi)

# (in, out) ray angles of the cycle c_{e,l} (l = 1..m-1) at P
function _cycle_rays(A::Float64, l::Int, m::Int, at_start::Bool)
  r0 = A + 2*pi*(l - 1)/m          # sheet l-1, traversed forwards
  r1 = A + 2*pi*l/m                # sheet l, traversed backwards
  # at the start of e: in along r1 (coming back on sheet l), out along r0;
  # at the end: in along r0, out along r1
  return at_start ? (r1, r0) : (r0, r1)
end

function _local_intersection(c1::Tuple{Float64, Float64}, c2::Tuple{Float64, Float64})
  in1, out1 = c1
  in2, out2 = c2
  left(x) = _in_ccw_sector(x, out1, in1)          # left of c1
  right(x) = _in_ccw_sector(x, in1, out1)
  right(in2) && left(out2) && return 1
  left(in2) && right(out2) && return -1
  return 0
end

function _se_intersection_matrix(C::SuperellipticModel, tree::Vector{SuperellipticEdge},
                                 data::Vector{_SEEdgeData})
  m, n = C.m, C.n
  N = (n - 1)*(m - 1)
  K = zero_matrix(ZZ, N, N)
  idx(k, l) = (k - 1)*(m - 1) + l
  for k in 1:n-1, l in 1:m-2
    K[idx(k, l), idx(k, l + 1)] = 1
    K[idx(k, l + 1), idx(k, l)] = -1
  end
  CC = parent(data[1].hd)
  mo = CC(-one(ArbField(precision(CC))))
  po = CC(one(ArbField(precision(CC))))
  # (edge, at_start, A) at every branch point
  ends = [Tuple{Int, Bool, Float64}[] for _ in 1:n]
  for (k, E) in enumerate(tree)
    D = data[k]
    Astart = angle(_c64(D.K * _se_Y(D, mo, -1.0, m)))
    Aend = angle(_c64(D.K * _se_Y(D, po, 1.0, m)))
    push!(ends[E.a], (k, true, Astart))
    push!(ends[E.b], (k, false, Aend))
  end
  for v in 1:n
    E = ends[v]
    # consistency: m*A - (direction of the edge at P) is the same for all edges at P
    ref = nothing
    for (k, st, A) in E
      hd = _c64(data[k].hd)
      theta = angle(st ? hd : -hd)
      c = mod(m*A - theta, 2*pi)
      if ref === nothing
        ref = c
      else
        d = abs(mod(c - ref + pi, 2*pi) - pi)
        @req d < 1e-6 "Inconsistent branches of y at a branch point (internal error)."
      end
    end
    for i1 in eachindex(E), i2 in i1+1:length(E)
      k1, st1, A1 = E[i1]
      k2, st2, A2 = E[i2]
      for l1 in 1:m-1, l2 in 1:m-1
        s = _local_intersection(_cycle_rays(A1, l1, m, st1), _cycle_rays(A2, l2, m, st2))
        s == 0 && continue
        K[idx(k1, l1), idx(k2, l2)] += s
        K[idx(k2, l2), idx(k1, l1)] -= s
      end
    end
  end
  return K
end

################################################################################
#
#  Period matrices
#
################################################################################

function _se_height_bits(C::SuperellipticModel)
  CC = AcbField(64)
  pC = _embed_poly(C.p, C.embedding, CC)
  lc = coeff(pC, C.n)
  vals = [abs(_c64(coeff(pC, d) / lc)) for d in 0:C.n-1]
  vals = filter(>(0), vals)
  isempty(vals) && return 0
  return max(0, ceil(Int, max(log2(1 + maximum(vals)), -log2(minimum(vals)))))
end

# Precision retry as in the general algorithm (see _big_period_matrix), but
# without extra guard bits for accuracy = :big: the working precision here
# already contains log2 of the largest integrand bound, and a retry is cheap.
function big_period_matrix(C::SuperellipticModel)
  isdefined(C, :big_period_matrix) && return C.big_period_matrix
  P = _se_compute_big_period_matrix!(C)
  params = C.resolved_parameters
  if params.precision_retry
    deficit = _precision_deficit(params.accuracy, C.initial_precision, C.genus, P)
    if deficit > 0
      C.precision_retries += 1
      C.min_target_precision = C.target_precision + ceil(Int, deficit) + _retry_extra_bits()
      @debug "Precision retry (superelliptic, $(params.accuracy)): short of $(round(deficit, digits = 1)) bits"
      P = _se_compute_big_period_matrix!(C)
    end
  end
  C.big_period_matrix = P
  return P
end

function _se_compute_big_period_matrix!(C::SuperellipticModel)
  params = copy(C.parameters)
  C.resolved_parameters = params
  m, n, g = C.m, C.n, C.genus
  prec = C.initial_precision

  # branch points at low precision: the tree and the quadrature parameters
  hbits = _se_height_bits(C)
  C.target_precision = max(prec + ceil(Int, (m + 3) * log2(10)), C.min_target_precision)
  prec0 = 64 + hbits
  pC0 = _embed_poly(C.p, C.embedding, AcbField(prec0))
  P0 = roots(pC0, initial_prec = prec0, target = 53)
  Pf = sort!([_c64(z) for z in P0], by = z -> (real(z), imag(z)))
  mind = minimum(abs(Pf[i] - Pf[j]) for i in 1:n for j in i+1:n)
  @req mind > 1e-12 * max(1.0, maximum(abs, Pf)) "The branch points are too close together for the algorithm for superelliptic curves; use superelliptic = false."
  loglc = log(abs(_c64(coeff(pC0, n))))

  style = params.int_style
  weight = (m == 2 && style != "DE") ? ((P, a, b) -> _gj_weight(_edge_u(P, a, b))) :
                                       ((P, a, b) -> _de_weight(_edge_u(P, a, b)))
  tree = _spanning_tree(Pf, weight)
  for E in tree
    _edge_parameters!(C, E, Pf, loglc, style)
  end
  C.tree = tree
  C.low_branch_points = Pf
  C.log_lc = loglc

  # working precision (Neurohr: + log(binomial(n, n/4) * max bound))
  maxlog2M = maximum(E.log2_bound for E in tree)
  extra = max(34, ceil(Int, Float64(log2(binomial(big(n), div(n, 4)))) + max(0.0, maxlog2M)))
  work = max(prec + hbits, C.target_precision + extra)
  C.computational_precision = work
  CC = AcbField(work)

  # branch points at the working precision, in the order of Pf
  pC = _embed_poly(C.p, C.embedding, CC)
  Ph = _accurate_roots(pC, work; slack = 64)
  P = Vector{AcbFieldElem}(undef, n)
  taken = falses(n)
  for z in Ph
    zf = _c64(z)
    i = argmin([abs(zf - w) for w in Pf])
    @req !taken[i] "Could not match the branch points."
    taken[i] = true
    P[i] = z
  end
  C.branch_points = P
  L = _rotated_power(coeff(pC, n), 1//m)
  C.lc_root = L

  # integrals along the edges (in parallel)
  data = [_se_edge_data(C, E, P, L) for E in tree]
  ints = Vector{Vector{AcbFieldElem}}(undef, n - 1)
  Threads.@threads for k in 1:n-1
    ints[k] = _se_edge_integrals(C, tree[k], data[k])
  end
  # the quadrature error (heuristic bound 2^-target, see _edge_parameters!)
  qerr = ArbField(work)(2)^(-C.target_precision)
  for v in ints, z in v
    ccall((:acb_add_error_arb, libflint), Nothing, (Ref{AcbFieldElem}, Ref{ArbFieldElem}), z, qerr)
  end
  C.elementary_integrals = ints

  # Abel-Jacobi map of the branch points: AJ(P_b - P_a) is the integral along
  # the edge a -> b (on any sheet: the sheets differ by periods). The base
  # point is the first vertex of the tree.
  paths = [Int[] for _ in 1:n]
  for (k, E) in enumerate(tree)
    paths[E.b] = vcat(paths[E.a], k)
  end
  C.tree_paths = paths
  C.abel_jacobi_branch_points = [sum((ints[k] for k in paths[v]); init = [zero(CC) for _ in 1:g])
                                 for v in 1:n]

  # periods of the cycles "edge k on sheet l - edge k on sheet l+1"
  I = onei(CC)
  zeta(e) = exp(2 * const_pi(CC) * I * CC(mod(e, m)) / m)      # zeta_m^e
  N = (n - 1)*(m - 1)
  PM = zero_matrix(CC, N, g)
  for k in 1:n-1, (d, (i, j)) in enumerate(C.differentials)
    base = ints[k][d] * (1 - zeta(-j))
    for l in 1:m-1
      PM[(k - 1)*(m - 1) + l, d] = zeta(-(l - 1)*j) * base
    end
  end

  # intersection matrix and symplectic basis
  K = _se_intersection_matrix(C, tree, data)
  C.intersection_matrix = K
  S = symplectic_reduction(K)
  C.symplectic_transform = S
  PMS = change_base_ring(CC, S) * PM
  @req all(contains(PMS[r, c], zero(CC)) for r in 2*g+1:N for c in 1:g) "Sanity check failed: the dependent cycles do not integrate to zero. There may have been an error in the computation of the intersection numbers."
  return transpose(PMS[1:2*g, :])
end

function small_period_matrix(C::SuperellipticModel)
  isdefined(C, :small_period_matrix) && return C.small_period_matrix
  g = C.genus
  P = big_period_matrix(C)
  P1 = P[1:g, 1:g]
  P2 = P[1:g, g+1:2*g]
  C.small_period_matrix = _solve_precond(P1, P2)
  C.complex_reduction_matrices = [_inv_precond(P1)]
  return C.small_period_matrix
end

################################################################################
#
#  Abel-Jacobi map
#
################################################################################

################################################################################
#
#  Points
#
#  Points of the curve as given are RiemannSurfacePoints of the original model
#  (so that divisors mix with points created elsewhere), but they are created
#  here without the special-point analysis of the general code (discriminant,
#  fundamental group, monodromy), which the superelliptic algorithm does not
#  need and which is expensive for large degrees.
#
################################################################################

# (x, y) in the coordinates of the curve as given <-> y^m = p(x)
_se_coords(C::SuperellipticModel, a, b) = isone(C.transform) ? (a, b) : (b, a)

@doc raw"""
    _se_point(C::SuperellipticModel, coords::Vector{AcbFieldElem})

The finite point with the given affine (or projective, z != 0) coordinates
on the curve as given.
"""
function _se_point(C::SuperellipticModel, coords::Vector{AcbFieldElem})
  @req 2 <= length(coords) <= 3 "Points need to be given in either affine coordinates (x, y) or projective coordinates (x : y : z)"
  CC = parent(coords[1])
  if length(coords) == 3
    @req !contains(coords[3], zero(CC)) "For the points at infinity use infinite_points(RS)."
    coords = [coords[1] / coords[3], coords[2] / coords[3]]
  end
  x, y = _se_coords(C, coords[1], coords[2])
  pC = _embed_poly(C.p, C.embedding, CC)
  @req contains(y^C.m - evaluate(pC, x), zero(CC)) "Not a point on the Riemann surface."
  P = RiemannSurfacePoint(original_model(C.surface))
  P.coordx, P.coordy = coords[1], coords[2]
  P.homog_coords = [coords[1], coords[2], one(CC)]
  P.is_singular = false
  P.is_finite = true
  P.ramification_index = contains(y, zero(CC)) ? C.m : 1
  return P
end

@doc raw"""
    _se_infinite_points(C::SuperellipticModel) -> Vector{RiemannSurfacePoint}

The gcd(m, n) points at infinity of y^m = p(x). The k-th one is the place
where y ~ zeta_m^(k-1) lc^(1/m) x^(n/m) (for x -> oo along the positive real
axis, with the branch lc^(1/m) = `C.lc_root`), i.e. the point (0, w0) with
w0 = zeta_m^(k-1) lc^(1/m) of the model at infinity (see
_se_abel_jacobi_infinite).
"""
function _se_infinite_points(C::SuperellipticModel)
  isdefined(C, :infinite_points) && return C.infinite_points
  O = original_model(C.surface)
  CC = AcbField(C.initial_precision)
  m, n = C.m, C.n
  delta = gcd(m, n)
  inf = CC(1/0)
  pts = RiemannSurfacePoint[]
  for k in 1:delta
    P = RiemannSurfacePoint(O)
    P.coordx = inf
    P.coordy = inf
    # the point of the plane model at infinity (y^m = x^n or x^n = ... at z = 0)
    h = m < n ? [zero(CC), one(CC), zero(CC)] : m > n ? [one(CC), zero(CC), zero(CC)] :
                [one(CC), zero(CC), zero(CC)]
    P.homog_coords = isone(C.transform) ? h : [h[2], h[1], h[3]]
    P.is_finite = false
    P.is_singular = false          # as a place; the plane model may be singular there
    P.index = k
    # Points at infinity are compared by their sets of sheets (==, used when
    # divisors are formed), so they need distinct ones. Here: -(r+1) for the
    # w0 = zeta_m^r lc^(1/m), r = k-1 mod delta, of the place (negative, so
    # that they cannot coincide with sheet numbers of the general code).
    P.sheets = [-(r + 1) for r in (k - 1):delta:(m - 1)]
    P.ramification_index = div(m, delta)
    push!(pts, P)
  end
  C.infinite_points = pts
  return pts
end

# The branch points (x_i, 0) and the ramified points at infinity.
function _se_ramification_points(C::SuperellipticModel)
  isdefined(C, :ramification_points) && return C.ramification_points
  prec = C.initial_precision
  CC = AcbField(prec)
  pts = RiemannSurfacePoint[]
  for x in _accurate_roots(_embed_poly(C.p, C.embedding, AcbField(prec + 64)), prec + 64; slack = 64)
    a, b = _se_coords(C, CC(x), zero(CC))
    push!(pts, _se_point(C, [a, b]))
  end
  gcd(C.m, C.n) < C.m && append!(pts, _se_infinite_points(C))
  C.ramification_points = pts
  return pts
end

# The base point: the branch point at the root of the spanning tree.
function base_point(C::SuperellipticModel)
  big_period_matrix(C)
  x0 = C.branch_points[C.tree[1].a]
  CO = AcbField(C.initial_precision)
  a, b = _se_coords(C, CO(x0), zero(CO))
  return _se_point(C, [a, b])
end

_is_infinite_coordinate(z::AcbFieldElem) = !isfinite(z)

function _is_point_at_infinity(P::RiemannSurfacePoint)
  is_finite(P) || return true
  (isdefined(P, :coordx) && _is_infinite_coordinate(P.coordx)) && return true
  (isdefined(P, :coordy) && _is_infinite_coordinate(P.coordy)) && return true
  return false
end

# AJ(D - deg(D) P0) (a g x 1 matrix) for a divisor D on another model of the
# Riemann surface of C (the original model: same curve, or x and y swapped).
function _se_abel_jacobi(C::SuperellipticModel, D::RiemannSurfaceDivisor)
  big_period_matrix(C)
  CC = AcbField(C.computational_precision)
  g = C.genus
  total = [zero(CC) for _ in 1:g]
  points, mults = support(D)
  inf_points = RiemannSurfacePoint[]
  inf_mults = Int[]
  for (P, k) in zip(points, mults)
    if _is_point_at_infinity(P)
      push!(inf_points, P)
      push!(inf_mults, k)
      continue
    end
    x, y = CC(P.coordx), CC(P.coordy)
    isone(C.transform) || ((x, y) = (y, x))
    v = _se_abel_jacobi_finite(C, x, y)
    for i in 1:g
      total[i] += k * v[i]
    end
  end
  delta = gcd(C.m, C.n)
  if !isempty(inf_points) && delta > 1
    # single points at infinity (see _se_abel_jacobi_infinite)
    for (P, k) in zip(inf_points, inf_mults)
      v = _se_abel_jacobi_infinite(C, P)
      for i in 1:g
        total[i] += k * v[i]
      end
    end
  elseif !isempty(inf_points)
    # D_inf = sum of the delta points at infinity. With a*m + b*n = delta:
    # div(x - x_1) = m P_1 - (m/delta) D_inf, div(y) = sum_i P_i - (n/delta) D_inf,
    # so D_inf ~ a m P_1 + b sum_i P_i, and with P_1 = P0:
    # AJ(D_inf - delta P0) = b sum_i AJ(P_i - P0).
    delta, _, b = gcdx(C.m, C.n)
    if delta == 1
      c = sum(inf_mults)
    else
      @req length(unique(objectid, inf_points)) == delta && allequal(inf_mults) "The Abel-Jacobi map of single points at infinity of y^$(C.m) = p(x) with gcd($(C.m), $(C.n)) > 1 is not available yet for the algorithm for superelliptic curves; only multiples of the sum of all $delta points at infinity. Use superelliptic = false."
      c = inf_mults[1]
    end
    for v in C.abel_jacobi_branch_points, i in 1:g
      total[i] += c * b * v[i]
    end
  end
  return matrix(CC, g, 1, total)
end

# AJ(Q - P0) for the finite point Q = (x, y) of y^m = p(x).
function _se_abel_jacobi_finite(C::SuperellipticModel, x::AcbFieldElem, y::AcbFieldElem)
  m, n, g = C.m, C.n, C.genus
  P = C.branch_points
  CC = parent(P[1])
  # a branch point
  for k in 1:n
    if overlaps(x, P[k])
      @req contains(y, zero(CC)) "Not a point of the curve."
      return C.abel_jacobi_branch_points[k]
    end
  end
  # otherwise: AJ(P_k - P0) + the integral from the branch point P_k to Q, for
  # the branch point with the best quadrature parameter of the segment
  xf = _c64(x)
  Pext = vcat(C.low_branch_points, [xf])
  best = argmax(k -> _de_weight(_edge_u(Pext, k, n + 1)), 1:n)
  E = SuperellipticEdge(best, n + 1)
  _edge_parameters!(C, E, Pext, C.log_lc, "DE")
  D = _se_edge_data(C, E, vcat(P, [x]), C.lc_root; one_sided = true)
  I = _se_edge_integrals(C, E, D; one_sided = true)
  qerr = ArbField(precision(CC))(2)^(-C.target_precision)
  for z in I
    ccall((:acb_add_error_arb, libflint), Nothing, (Ref{AcbFieldElem}, Ref{ArbFieldElem}), z, qerr)
  end
  # the sheet: y = zeta^s y_ref(x), y_ref(x) = K 2^(1/m) Y(1)
  po = CC(one(ArbField(precision(CC))))
  yref = D.K * exp(log(CC(2)) / m) * _se_Y(D, po, 1.0, m)
  s = mod(round(Int, m * (angle(_c64(y)) - angle(_c64(yref))) / (2*pi)), m)
  zeta = exp(2 * const_pi(CC) * onei(CC) / m)
  @req abs(_c64(y - zeta^s * yref)) <= 1e-8 * max(1.0, abs(_c64(y))) "The point is not on the curve (no sheet matches its y-coordinate)."
  res = copy(C.abel_jacobi_branch_points[best])
  for (d, (i, j)) in enumerate(C.differentials)
    res[d] += zeta^(mod(-j*s, m)) * I[d]
  end
  return res
end

# AJ(P - P0) for a point P at infinity of y^m = p(x) (the original model is the
# same curve), delta = gcd(m, n) > 1.
#
# With M = m/delta, N = n/delta, x = t^(-M) and y = w t^(-N) the curve becomes
#     w^m = lc * q(t^M),   q(s) = prod_i (1 - x_i s),
# which is smooth at t = 0: the points at infinity are the points (0, w0) with
# w0^m = lc, up to w0 -> w0 zeta_M^N (t -> zeta_M t gives the same point),
# i.e. the place is determined by c = w0^M = lim y^M x^(-N). A holomorphic
# differential x^i dx / y^j becomes -M t^e w^(-j) dt with
# e = N j - M (i + 1) - 1 >= 0. So
#     AJ(P - P0) = AJ(Q - P0) + M int_0^t1 t^e w(t)^(-j) dt
# for the point Q at t = t1 on the branch w(t) = w0 prod_i (1 - x_i t^M)^(1/m).
# t1 = X^(-1/M)/3 (X = max(1, |x_i|)) keeps |x_i t^M| <= 3^-M on [0, t1] and
# <= (2/3)^M on the ellipse with parameter 3 around it, so the factors have
# positive real part (principal roots) and Gauss-Legendre converges fast.
#
# Which place P is: the general code labels the points at infinity by the
# cycles of the monodromy at infinity on the sheets at its base point x0
# (left of all branch points), i.e. by continuation along the ray x0 - tau.
# There y(x) = y_s prod_i ((x_i - x)/(x_i - x0))^(1/m) (principal roots, the
# factors have positive real part), so c = lim y^M x^(-N) = A^M (-1)^N with
# A = y_s / prod_i (x_i - x0)^(1/m).
function _se_abel_jacobi_infinite(C::SuperellipticModel, P::RiemannSurfacePoint)
  m, n, g = C.m, C.n, C.genus
  delta = gcd(m, n)
  M, N = div(m, delta), div(n, delta)
  X = C.branch_points
  CC = parent(X[1])
  RR = ArbField(precision(CC))
  I = onei(CC)
  zeta = exp(2 * const_pi(CC) * I / m)
  if isdefined(P, :sheets) && !isempty(P.sheets) && P.sheets[1] < 0
    # a point created by _se_infinite_points (sheets -(r+1))
    w0 = C.lc_root * zeta^(-P.sheets[1] - 1)
  else
    # a point at infinity of the general code (labelled by sheets)
    O = parent(P)
    @req isone(C.transform) "Points at infinity of the general code cannot be used with the algorithm for superelliptic curves of a curve given as c*x^m + q(y) = 0; use infinite_points(RS)."
    @req isdefined(P, :sheets) && !isempty(P.sheets) && isdefined(O, :base_point) "Unknown point at infinity."
    # the invariant c of the place
    x0 = CC(O.base_point.coordx)
    ys = CC(fiber(complex_defining_polynomial(O), O.base_point.coordx)[P.sheets[1]])
    Pr = prod(xi - x0 for xi in X)
    theta = sum(angle(_c64(xi - x0)) for xi in X)
    A = ys / (exp(log(Pr * exp(-I * CC(theta))) / m) * exp(I * CC(theta) / m))
    c = A^M * (isodd(N) ? -1 : 1)
    r = argmin(k -> abs(_c64((C.lc_root * zeta^k)^M - c)), 0:m-1)
    w0 = C.lc_root * zeta^r
  end

  # w(t) on [0, t1]
  Xmax = max(1.0, maximum(z -> abs(_c64(z)), X))
  t1f = Xmax^(-1/M) / 3
  function w_at(t::AcbFieldElem)
    sM = t^M
    Pw = one(CC)
    th = 0.0
    for xi in X
      f = 1 - xi * sM
      Pw *= f
      th += angle(_c64(f))
    end
    return w0 * exp(log(Pw * exp(-I * CC(th))) / m) * exp(I * CC(th) / m)
  end

  # Gauss-Legendre on [0, t1]; bound on the ellipse with parameter 3:
  # |t| <= 2 t1, |w|^(-j) <= |lc|^(-j/m) 3^(j n/m)
  expo = [N*j - M*(i + 1) - 1 for (i, j) in C.differentials]
  @assert all(>=(0), expo)
  loglc = C.log_lc
  logB = log(M) + maximum(e*log(2*t1f) + j*(n*log(3.0) - loglc)/m
                          for (e, (i, j)) in zip(expo, C.differentials))
  err = RR(2)^(-C.target_precision)
  Ngl = max(2, Int(gauss_legendre_parameters(RR(3), err, exp(RR(logB)))))
  abscissae, weights = gauss_legendre_integration_points(Ngl, precision(CC))
  t1 = RR(t1f)
  acc = [zero(CC) for _ in 1:g]
  for k in eachindex(abscissae)
    t = CC(t1 * (abscissae[k] + 1) / 2)
    winv = inv(w_at(t))
    wt = CC(weights[k])
    for (d, (i, j)) in enumerate(C.differentials)
      acc[d] += wt * t^expo[d] * winv^j
    end
  end
  for d in 1:g
    acc[d] *= M * CC(t1) / 2
    ccall((:acb_add_error_arb, libflint), Nothing, (Ref{AcbFieldElem}, Ref{ArbFieldElem}), acc[d], err)
  end

  # the point Q at t = t1
  t1inv = inv(CC(t1))
  x1 = t1inv^M
  y1 = w_at(CC(t1)) * t1inv^N
  res = _se_abel_jacobi_finite(C, x1, y1)
  return [res[d] + acc[d] for d in 1:g]
end
