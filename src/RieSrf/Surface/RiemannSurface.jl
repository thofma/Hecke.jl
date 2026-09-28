################################################################################
#
#          RieSrf/RiemannSurface.jl : Riemann surfaces and their plane models
#
################################################################################

#  A RiemannSurface is the compact Riemann surface of the plane curve
#  f(x, y) = 0 given by the user. The numerical work is done on plane models
#  (RiemannSurfaceModel): the curve after a projective transformation of P^2,
#  seen as a cover of P^1 by the projection to the first coordinate.
#
#   * The original model is the curve as given (identity transformation).
#     Everything that depends on the projection x lives here: discriminant
#     points, critical, ramification, singular and infinite points, points
#     created from coordinates, fundamental group, monodromy.
#   * The computational model is the model the period matrices are computed
#     on. The homology basis, the basis of differentials and the Abel-Jacobi
#     map also come from it. Points of the original model are moved to it by
#     the transformation (see _transfer_point).
#
#  The genus, the period lattice up to the choice of bases and the
#  Abel-Jacobi map of divisors of degree 0 do not depend on the model. The
#  period matrices themselves are those of the bases of the computational
#  model.
#
#  Both models are created lazily; they are the same object when the original
#  model is used for the computations.
#
#  Example:
#     using Hecke, Hecke.RiemannSurfaces
#     Qxy, (x, y) = polynomial_ring(QQ, [:x, :y])
#     f = x^5 + x^4 + x^3 - x + 4 - y^2
#     RS = riemann_surface(f, 200)        # cheap: nothing numerical is computed yet
#     tau = small_period_matrix(RS)

################################################################################
#
#  Construction
#
################################################################################

@doc raw"""
    riemann_surface(f::MPolyRingElem, prec::Int = 100; model = :auto,
                    parameters = nothing, kw...) -> RiemannSurface

Construct the Riemann surface corresponding to the desingularization of the
plane curve f(x,y) = 0 over a number field (or QQ), embedded into CC by the
first infinite place, with initial precision equal to `prec` bits.

Only cheap data is computed when the Riemann surface is created. The basis of
differentials, the monodromy, the homology basis and the period matrix are
computed (and cached) when they are first asked for, e.g. by
`big_period_matrix(RS)`.

The keyword `model` determines the plane model the period matrices are
computed on:
- `:auto` (default): a curve of the form c*y^m + q(x) = 0 (or with x and y
  swapped, q separable of degree at least 3) uses the algorithm for
  superelliptic curves (unless the integration parameter `superelliptic` is
  `false`); otherwise the original curve or the curve with x and y swapped,
  whichever has fewer sheets over the x-line (the original on a tie).
- `:superelliptic`: the algorithm for superelliptic curves y^m = p(x) (see
  `SuperellipticModel`); the curve must be of the form c*y^m + q(x) = 0 or
  c*x^m + q(y) = 0 with q separable of degree at least 3.
- `:original`: the curve as given.
- `:swapped`: the curve f(y, x) = 0.
- an invertible 3x3 matrix M over the base field: the curve whose point
  M*(x, y, z) corresponds to the point (x : y : z) of the given curve.
The data that depends on the projection to x (discriminant points,
ramification points, monodromy, ...) always refers to the curve as given.
The period matrices are those of the bases of differentials and of homology
of the model used; see `computational_model`.

The keyword arguments `integration_method`, `int_style`, `midpoint_precision`,
`adaptive`, `chunk_len` and `group_cost`, or `parameters::IntegrationParameters`,
set the integration parameters; see `IntegrationParameters`.
"""
function riemann_surface(f::MPolyRingElem, prec::Int = 100;
                         parameters::Union{Nothing, IntegrationParameters} = nothing,
                         model = :auto, kw...)
  k = base_ring(f)
  if k == QQ
    k = rationals_as_number_field()[1]
  end
  v = infinite_places(k)[1]
  return riemann_surface(f, v, prec; parameters = parameters, model = model, kw...)
end

@doc raw"""
    riemann_surface(f::MPolyRingElem, v::Union{PosInf, InfPlc}, prec::Int = 100;
                    model = :auto, parameters = nothing, kw...) -> RiemannSurface

As `riemann_surface(f, prec)`, with the embedding into CC given by the
infinite place v of the base field.
"""
function riemann_surface(f::MPolyRingElem, v::T, prec::Int = 100;
                         parameters::Union{Nothing, IntegrationParameters} = nothing,
                         model = :auto, kw...) where T<:Union{PosInf, InfPlc}
  # Keyword arguments are integration parameters (integration_method,
  # int_style, midpoint_precision, adaptive, chunk_len, group_cost); they
  # override the ones in `parameters`.
  P = parameters === nothing ? IntegrationParameters(; kw...) : _with_changes(parameters; kw...)
  RS = RiemannSurface(f, v, prec, P, model)
  O = original_model(RS)      # cheap; checks the input
  RS.model = _check_model_choice(model, base_ring(O.defining_polynomial))
  return RS
end

@doc raw"""
    riemann_surface(f, CC::ComplexField; kw...) -> RiemannSurface
    riemann_surface(f, v, CC::ComplexField; kw...) -> RiemannSurface

As `riemann_surface(f, prec)` with `prec = precision(Balls)` at the time of
the call, but the numerical output (period matrices, Abel-Jacobi map,
discriminant points, ...) is given in `ComplexField` / `RealField` instead of
`AcbField` / `ArbField`. Points can be given with `ComplexFieldElem`
coordinates. The precision stays fixed for the surface (its results are
cached); later changes of `precision(Balls)` do not affect it.
"""
riemann_surface(f::MPolyRingElem, CC::ComplexField; kw...) =
  _complex_output!(riemann_surface(f, precision(Balls); kw...))

riemann_surface(f::MPolyRingElem, v::Union{PosInf, InfPlc}, CC::ComplexField; kw...) =
  _complex_output!(riemann_surface(f, v, precision(Balls); kw...))

_complex_output!(RS::RiemannSurface) = (RS.output = :complex; RS)

# Conversion of the output to the type chosen for RS (see RiemannSurface.output)
_out(RS::RiemannSurface, x) = RS.output === :complex ? _to_output(x) : x
_to_output(x::Union{AcbFieldElem, AcbMatrix, Vector{AcbFieldElem}}) = _to_complex(x)
_to_output(x::Union{ArbFieldElem, ArbMatrix}) = _to_real(x)
_to_output(x::MPolyRingElem{AcbFieldElem}) = _to_complex(x)
_to_output(x::Vector{Vector{AcbFieldElem}}) = [_to_complex(y) for y in x]
_to_output(x::Tuple) = map(_to_output, x)
_to_output(x::Vector{Int}) = x
_to_output(x) = x

# ComplexField input: to the working precision of the surface
_in(RS::RiemannSurface, x::Union{ComplexFieldElem, Vector{ComplexFieldElem}}) =
  _to_acb(x, _input_working_precision(RS))
_in(RS::RiemannSurface, x) = x
_input_working_precision(RS::RiemannSurface) =
  isdefined(RS, :original) ? max(original_model(RS).computational_precision, precision(RS)) : precision(RS)

# :auto, :original, :swapped, or the matrix converted to the base field k
function _check_model_choice(model, k)
  msg = "model must be :auto, :original, :swapped, :superelliptic or an invertible 3x3 matrix."
  if model isa Symbol
    @req model in (:auto, :original, :swapped, :superelliptic) msg
    return model
  end
  @req (model isa MatElem || model isa AbstractMatrix) && size(model) == (3, 3) msg
  M = matrix(k, 3, 3, [k(model[i, j]) for i in 1:3 for j in 1:3])
  @req !iszero(det(M)) msg
  return M
end

@doc raw"""
    original_model(RS::RiemannSurface) -> RiemannSurfaceModel

The plane model given by the defining polynomial of `RS`.
"""
function original_model(RS::RiemannSurface)
  if !isdefined(RS, :original)
    O = RiemannSurfaceModel(RS.input_polynomial, RS.embedding, RS.precision;
                            parameters = RS.parameters)
    O.surface = RS
    O.transform = identity_matrix(base_ring(O.defining_polynomial), 3)
    RS.original = O
  end
  return RS.original
end

@doc raw"""
    computational_model(RS::RiemannSurface) -> AbstractRiemannSurfaceModel

The plane model the period matrices of `RS` are computed on (see the keyword
`model` of `riemann_surface`): a `RiemannSurfaceModel`, or a
`SuperellipticModel` for the algorithm for superelliptic curves.
"""
function computational_model(RS::RiemannSurface)
  isdefined(RS, :computational) && return RS.computational
  O = original_model(RS)
  k = base_ring(O.defining_polynomial)
  choice = RS.model
  if choice === :original
    C = O
  elseif choice === :swapped
    C = _transformed_model(RS, _swap_matrix(k))
  elseif choice === :superelliptic
    C = _superelliptic_model(RS)
    @req C !== nothing "The curve is not of the form c*y^m + q(x) = 0 (or c*x^m + q(y) = 0) with q separable of degree at least 3."
  elseif choice === :auto
    C = RS.parameters.superelliptic ? _superelliptic_model(RS) : nothing
    C === nothing && (C = _choose_model(RS))
  else
    C = _transformed_model(RS, choice)       # converted by _check_model_choice
  end
  RS.computational = C
  return C
end

@doc raw"""
    model_transform(RS::RiemannSurface) -> MatElem

The matrix M of the computational model: the point (x : y : z) of the curve
given by the user corresponds to the point M*(x, y, z) of the computational
model.
"""
model_transform(RS::RiemannSurface) = computational_model(RS).transform

_swap_matrix(k) = matrix(k, 3, 3, [0, 1, 0, 1, 0, 0, 0, 0, 1])

# The model of RS with transformation M (identity: the original model).
function _transformed_model(RS::RiemannSurface, M::MatElem)
  O = original_model(RS)
  @req !iszero(det(M)) "The model transformation must be an invertible 3x3 matrix."
  isone(M) && return O
  g = _transform_polynomial(O.defining_polynomial, M)
  @req degree(g, 2) >= 2 "The transformed curve has degree $(degree(g, 2)) in y; the projection to x must have degree at least 2."
  # For a curve given over QQ, hand the model a polynomial over QQ as well
  # (like the original model): the exact basis of differentials is computed
  # from the input polynomial, and over QQ(x) that is much faster than over
  # K(x) for K = rationals_as_number_field() (f2: 3.5 s instead of 9 s).
  f0 = RS.input_polynomial
  if base_ring(f0) == QQ && all(c -> degree(parent(c)) == 1, coefficients(g))
    R0 = parent(f0)
    X0, Y0 = gens(R0)
    g0 = zero(R0)
    for i in 1:length(g)
      e = exponent_vector(g, i)
      g0 += QQ(coeff(coeff(g, i), 0)) * X0^e[1] * Y0^e[2]
    end
    g = g0
  end
  C = RiemannSurfaceModel(g, RS.embedding, RS.precision; parameters = RS.parameters)
  C.surface = RS
  C.transform = M
  return C
end

# g(X, Y) = F(M^(-1) (X, Y, 1)) with F the homogenization of f: the point
# (x : y : z) of f corresponds to the point M*(x, y, z) of g.
function _transform_polynomial(f::MPolyRingElem, M::MatElem)
  R = parent(f)
  X, Y = gens(R)
  Mi = inv(M)
  l = [Mi[i, 1]*X + Mi[i, 2]*Y + Mi[i, 3] for i in 1:3]
  d = total_degree(f)
  g = zero(R)
  for i in 1:length(f)
    e = exponent_vector(f, i)
    g += coeff(f, i) * l[1]^e[1] * l[2]^e[2] * l[3]^(d - e[1] - e[2])
  end
  return g
end

################################################################################
#
#  Choosing the computational model (model = :auto)
#
################################################################################

# model = :auto: for now the model with fewer sheets (the degree of f in y
# for the original, in x for the swapped model); the original on a tie. The
# degrees are kept in RS.model_costs. (predicted_cost below is a finer
# criterion, but it needs the discriminant points and paths of every
# candidate, which can cost more than it saves; to be revisited together with
# the precision management.)
function _choose_model(RS::RiemannSurface)
  O = original_model(RS)
  f = O.defining_polynomial
  mo, ms = degree(f, 2), degree(f, 1)
  RS.model_costs = [(:original, Float64(mo)), (:swapped, Float64(ms))]
  if ms >= 2 && ms < mo
    @debug "Model choice: swapped" sheets = (mo, ms)
    return _transformed_model(RS, _swap_matrix(base_ring(f)))
  end
  return O
end

@doc raw"""
    predicted_cost(C::RiemannSurfaceModel) -> Float64

A rough prediction of the cost of the period matrix computation on the plane
model `C`: the number of quadrature nodes on the paths of the fundamental
group, as the integration with `int_style = "Mixed"` would choose them
(Gauss-Legendre with the path's own parameter r, or double exponential for
r < 1.03, without grouping and splitting and with a provisional bound 10^5),
times m*(m + d_x), where m is the number of sheets and d_x the degree in x
(root finding and evaluating f(x, y) at a node).

Only needs the discriminant points and the paths, no analytic continuation.
Not used by `model = :auto` at the moment (see `_choose_model`).
"""
function predicted_cost(C::RiemannSurfaceModel)
  paths, _ = fundamental_group_of_punctured_P1(C)
  # The internal discriminant points have twice the internal precision; the
  # parameters r only need to be certified > 1, for which the internal
  # precision is plenty.
  CL = AcbField(C.internal_precision)
  points = [(z = CL(); Nemo._acb_set(z, p, C.internal_precision); z)
            for p in internal_discriminant_points(C, false)]
  err = C.computational_error
  prec = C.computational_precision
  nodes = 0
  for p in paths
    q = _fresh_path_copy(p)            # the parameter functions record data in the path
    t = path_type(q)
    r = t == 0 ? gauss_legendre_line_parameters(points, q) :
        t == 1 ? gauss_legendre_arc_parameters(points, q) :
                 gauss_legendre_circle_parameters(points, q)
    RR = parent(r)
    if r >= RR(103//100)
      nodes += Int(gauss_legendre_parameters(_gl_group_r(r), err, RR(10)^5))
    else
      rde = t == 0 ? double_exponential_line_parameters(points, q) :
            t == 1 ? double_exponential_arc_parameters(points, q) :
                     double_exponential_circle_parameters(points, q)
      RD = parent(rde)
      N, _ = double_exponential_integration_parameters(RD(19//20)*rde, prec, [RD(10)^5, RD(10)^5])
      nodes += 2*Int(N) + 1
    end
  end
  f = C.defining_polynomial
  m = degree(f, 2)
  return Float64(nodes) * m * (m + degree(f, 1))
end

_fresh_path_copy(G::CPath) =
  path_type(G) == 0 ? c_line(G.start_point_high, G.end_point_high, G.C) :
                      c_arc(G.start_point_high, G.end_point_high, G.center_high, G.C;
                            orientation = orientation(G))

################################################################################
#
#  Moving points between models
#
################################################################################

# Homogeneous coordinates of the place P, if they determine it: a finite
# point that is not a singular point of the model, or a smooth point at
# infinity whose coordinates are known (e.g. (0 : 1 : 0)). Otherwise nothing.
function _place_coordinates(P::RiemannSurfacePoint)
  isdefined(P, :homog_coords) || return nothing
  S = parent(P)
  if is_finite(P)
    (isdefined(P, :is_singular) && P.is_singular) && return nothing
    return [P.coordx, P.coordy, one(parent(P.coordx))]
  end
  h = P.homog_coords
  contains(h[3], zero(parent(h[3]))) || return nothing
  for s in S.singular_points
    all(overlaps(s[i], h[i]) for i in 1:3) && return nothing
  end
  return h
end

# The point of the model C that corresponds to the point P of another model
# of the same Riemann surface.
function _transfer_point(P::RiemannSurfacePoint, C::RiemannSurfaceModel)
  S = parent(P)
  S === C && return P
  @req isdefined(S, :transform) && isdefined(C, :transform) "The point does not belong to a model of this Riemann surface."
  h = _place_coordinates(P)
  @req h !== nothing "Points over singular points and points at infinity of a model cannot be moved to another model yet. Use riemann_surface(f, prec; model = :original) for Abel-Jacobi maps of such points."
  CC = parent(h[1])
  T = C.transform * inv(S.transform)
  e = S.embedding.embedding
  Te = [CC(evaluate(T[i, j], e, precision(CC))) for i in 1:3, j in 1:3]
  hq = [sum(Te[i, j]*h[j] for j in 1:3) for i in 1:3]
  @req !contains(hq[3], zero(CC)) "The point corresponds to a point at infinity of the computational model; this is not supported yet. Use riemann_surface(f, prec; model = :original) for Abel-Jacobi maps of such points."
  return C([hq[1]/hq[3], hq[2]/hq[3]])
end

function _transfer_divisor(D::RiemannSurfaceDivisor, C::RiemannSurfaceModel)
  points, mults = support(D)
  isempty(points) && return zero_divisor(C)
  return divisor(RiemannSurfacePoint[_transfer_point(P, C) for P in points], copy(mults))
end

################################################################################
#
#  Printing
#
################################################################################

function Base.show(io::IO, RS::RiemannSurface)
  if is_terse(io)
    print(io, "Riemann surface")
  else
    g = ""
    if isdefined(RS, :computational)
      C = RS.computational
      if C isa SuperellipticModel || isdefined(C, :differential_form_data)
        g = " of genus $(C.genus)"
      end
    end
    print(io, "Riemann surface$g defined by $(RS.input_polynomial) = 0")
  end
end

################################################################################
#
#  Data that does not depend on the model (from the computational model)
#
################################################################################

@doc raw"""
    genus(RS::RiemannSurface) -> Int

Return the genus of the Riemann surface.
"""
genus(RS::RiemannSurface) = genus(computational_model(RS))

@doc raw"""
    big_period_matrix(RS::RiemannSurface) -> AcbMatrix

Return a big period matrix (g x 2g) of the Riemann surface, with respect to
the basis of differentials and the symplectic homology basis of the
computational model.
"""
big_period_matrix(RS::RiemannSurface) = _out(RS, big_period_matrix(computational_model(RS)))

@doc raw"""
    small_period_matrix(RS::RiemannSurface) -> AcbMatrix

Return a small period matrix of the Riemann surface (see `big_period_matrix`).
"""
small_period_matrix(RS::RiemannSurface) = _out(RS, small_period_matrix(computational_model(RS)))

@doc raw"""
    homology_basis(RS::RiemannSurface)

Return the homology basis of the computational model; see
`homology_basis(::RiemannSurfaceModel)`.
"""
homology_basis(RS::RiemannSurface) = homology_basis(computational_model(RS))

@doc raw"""
    basis_of_differentials(RS::RiemannSurface) -> Vector{FunFldDiff}

Return the basis of differentials used for the period matrices, in the
coordinates of the computational model.
"""
basis_of_differentials(RS::RiemannSurface) = basis_of_differentials(computational_model(RS))

@doc raw"""
    base_point(RS::RiemannSurface) -> RiemannSurfacePoint

Return the base point of the Abel-Jacobi map (a point of the computational
model).
"""
base_point(RS::RiemannSurface) = base_point(computational_model(RS))

embedding(RS::RiemannSurface) = RS.embedding

@doc raw"""
    precision(RS::RiemannSurface) -> Int

Return the precision (in bits) the Riemann surface was created with.
"""
precision(RS::RiemannSurface) = RS.precision

complex_field(RS::RiemannSurface) = RS.output === :complex ? ComplexField() : AcbField(precision(RS))
real_field(RS::RiemannSurface) = RS.output === :complex ? RealField() : ArbField(precision(RS))

################################################################################
#
#  Data of the curve as given (from the original model)
#
################################################################################

defining_polynomial(RS::RiemannSurface) = defining_polynomial(original_model(RS))
defining_polynomial_univariate(RS::RiemannSurface) = defining_polynomial_univariate(original_model(RS))
function_field(RS::RiemannSurface) = function_field(original_model(RS))

complex_defining_polynomial(RS::RiemannSurface, prec::Int = precision(RS)) =
  _out(RS, complex_defining_polynomial(original_model(RS), prec))

discriminant_points(RS::RiemannSurface, copy::Bool = true) = _out(RS, discriminant_points(original_model(RS), copy))
internal_discriminant_points(RS::RiemannSurface, copy::Bool = true) =
  internal_discriminant_points(original_model(RS), copy)

# For the algorithm for superelliptic curves the points are created by the
# superelliptic model (no special-point analysis of the general code).
_se_or_nothing(RS::RiemannSurface) = (C = computational_model(RS); C isa SuperellipticModel ? C : nothing)

function critical_points(RS::RiemannSurface)
  C = _se_or_nothing(RS)
  C === nothing && return critical_points(original_model(RS))
  return filter(is_finite, _se_ramification_points(C))
end
function ramification_points(RS::RiemannSurface)
  C = _se_or_nothing(RS)
  return C === nothing ? ramification_points(original_model(RS)) : _se_ramification_points(C)
end
singular_points(RS::RiemannSurface) = singular_points(original_model(RS))
function infinite_points(RS::RiemannSurface)
  C = _se_or_nothing(RS)
  return C === nothing ? infinite_points(original_model(RS)) : _se_infinite_points(C)
end
function y_infinite_points(RS::RiemannSurface)
  C = _se_or_nothing(RS)
  # y^m = p(x): y is only infinite over x = infinity
  return C === nothing ? y_infinite_points(original_model(RS)) : RiemannSurfacePoint[]
end

fundamental_group_of_punctured_P1(RS::RiemannSurface, abel_jacobi::Bool = true) =
  fundamental_group_of_punctured_P1(original_model(RS), abel_jacobi)
monodromy_representation(RS::RiemannSurface) = monodromy_representation(original_model(RS))
monodromy_group(RS::RiemannSurface) = monodromy_group(original_model(RS))

fiber_with_multiplicities(RS::RiemannSurface, x0::Union{AcbFieldElem, ComplexFieldElem}) =
  _out(RS, fiber_with_multiplicities(original_model(RS), _in(RS, x0)))

@doc raw"""
    (RS::RiemannSurface)(coords::Vector{AcbFieldElem})

Return the point of `RS` with the given affine (x, y) or projective
(x : y : z) coordinates on the curve as given.
"""
function (RS::RiemannSurface)(coords::Vector{ComplexFieldElem})
  return RS(_in(RS, coords))
end

function (RS::RiemannSurface)(coords::Vector{AcbFieldElem})
  C = _se_or_nothing(RS)
  return C === nothing ? original_model(RS)(coords) : _se_point(C, coords)
end

zero_divisor(RS::RiemannSurface) = zero_divisor(original_model(RS))

################################################################################
#
#  Integration parameters
#
################################################################################

# the models of RS that exist (the original and the computational model)
function _models(RS::RiemannSurface)
  res = AbstractRiemannSurfaceModel[]
  isdefined(RS, :original) && push!(res, RS.original)
  isdefined(RS, :computational) && RS.computational !== RS.original && push!(res, RS.computational)
  return res
end

@doc raw"""
    integration_parameters(RS::RiemannSurface) -> IntegrationParameters

Return (a copy of) the integration parameters of `RS` as set by the user.
"""
integration_parameters(RS::RiemannSurface) = copy(RS.parameters)

@doc raw"""
    resolved_integration_parameters(RS::RiemannSurface) -> IntegrationParameters

Return the integration parameters actually used, with every `:auto` replaced
by the value that was chosen. Returns `nothing` if the period computation has
not started yet.
"""
function resolved_integration_parameters(RS::RiemannSurface)
  isdefined(RS, :computational) || return nothing
  return resolved_integration_parameters(RS.computational)
end

@doc raw"""
    set_integration_parameters!(RS::RiemannSurface; kw...)

Change integration parameters of `RS`, e.g.
`set_integration_parameters!(RS; midpoint_precision = 128, adaptive = false)`.
Only possible before the period computation has started; afterwards use
`with_integration_parameters`.
"""
function set_integration_parameters!(RS::RiemannSurface; kw...)
  P = _with_changes(RS.parameters; kw...)
  @req resolved_integration_parameters(RS) === nothing "The computation has already started with the current parameters. Use with_integration_parameters(RS; ...) to get a new Riemann surface with other parameters."
  RS.parameters = P
  for M in _models(RS)
    isdefined(M, :resolved_parameters) || (M.parameters = copy(P))
  end
  return RS
end

@doc raw"""
    with_integration_parameters(RS::RiemannSurface; kw...) -> RiemannSurface

Return a new Riemann surface for the same curve, embedding and precision,
with the integration parameters of `RS` changed as given. If the
computational model of `RS` has been chosen already, the new surface uses the
same model (so the period matrices are comparable). Nothing numerical is
shared with `RS`.
"""
function with_integration_parameters(RS::RiemannSurface; kw...)
  P = _with_changes(RS.parameters; kw...)
  model = RS.model
  if model === :auto && isdefined(RS, :computational)
    C = RS.computational
    model = C isa SuperellipticModel ? :superelliptic :
            C === RS.original ? :original : C.transform
  end
  RS2 = riemann_surface(RS.input_polynomial, RS.embedding, RS.precision;
                        parameters = P, model = model)
  isdefined(RS, :space_curve) && (RS2.space_curve = RS.space_curve)
  return RS2
end
