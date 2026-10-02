################################################################################
#
#  RieSrf/Surface/RiemannSurfaceModel.jl : plane models of Riemann surfaces
#
#  A RiemannSurfaceModel is one plane model of a Riemann surface: the curve
#  after a projective transformation, as a cover of P^1 by the projection to
#  x. All numerical work happens here. The user-facing RiemannSurface (see
#  RiemannSurface.jl) holds the original model and the computational model.
#
#  This file: integration parameters, the swapped model (for the Abel-Jacobi
#  map at critical points), constants and getters.
#
#  The package is a port of Christian Neurohr's Magma package RiemannSurfaces
#  (https://github.com/christianneurohr/RiemannSurfaces), based on his PhD
#  thesis "Efficient integration on Riemann surfaces & applications" (2018).
#
################################################################################

# Special points (critical points, points at infinity, singular points).
# They only need the monodromy, not the periods. Both calls are cached.
function _ensure_special_points!(RS::RiemannSurfaceModel)
  _ensure_monodromy!(RS)
  _analyze_special_points!(RS)
  return RS
end

# Fix the parameters: replace :auto by concrete values. Called when the
# numerical computation starts; afterwards the parameters cannot be changed.
function _resolve_integration_parameters!(RS::RiemannSurfaceModel)
  isdefined(RS, :resolved_parameters) && return RS.resolved_parameters
  P = copy(RS.parameters)
  if P.midpoint_precision === :auto
    P.midpoint_precision = _auto_midpoint_precision(RS.computational_precision)
  end
  RS.resolved_parameters = P
  return P
end

@doc raw"""
    integration_parameters(RS::RiemannSurfaceModel) -> IntegrationParameters

Return (a copy of) the integration parameters of `RS` as set by the user.
"""
integration_parameters(RS::RiemannSurfaceModel) = copy(RS.parameters)

@doc raw"""
    resolved_integration_parameters(RS::RiemannSurfaceModel) -> IntegrationParameters

Return the integration parameters actually used, with every `:auto` replaced
by the value that was chosen. Returns `nothing` if no numerical computation
has started yet.
"""
resolved_integration_parameters(RS::RiemannSurfaceModel) =
  isdefined(RS, :resolved_parameters) ? copy(RS.resolved_parameters) : nothing

@doc raw"""
    set_integration_parameters!(RS::RiemannSurfaceModel; kw...)

Change integration parameters of `RS`, e.g.
`set_integration_parameters!(RS; midpoint_precision = 128, adaptive = false)`.
Only possible before the first numerical computation; afterwards use
`with_integration_parameters`.
"""
function set_integration_parameters!(RS::RiemannSurfaceModel; kw...)
  @req !isdefined(RS, :resolved_parameters) "The computation has already started with the current parameters. Use with_integration_parameters(RS; ...) to get a new Riemann surface with other parameters."
  RS.parameters = _with_changes(RS.parameters; kw...)
  return RS
end

@doc raw"""
    with_integration_parameters(RS::RiemannSurfaceModel; kw...) -> RiemannSurfaceModel

Return a new Riemann surface for the same curve, embedding and precision,
with the integration parameters of `RS` changed as given. Nothing numerical is
shared with `RS`.
"""
function with_integration_parameters(RS::RiemannSurfaceModel; kw...)
  P = _with_changes(RS.parameters; kw...)
  return RiemannSurfaceModel(RS.input_polynomial, RS.embedding, RS.initial_precision; parameters = P)
end

# The model of the curve f(y, x) = 0 (projection to y instead of x), with the
# differentials of RS transported to it. Used by abel_jacobi_map (method
# :swap) for critical points: a point with f_y = 0 but f_x != 0 is not
# critical on the swapped model. Its Abel-Jacobi values are in the basis of RS,
# so they can be combined with those of RS.
#
# RS integrates omega_i = h_i(x, y) dx, with h_i stored as a product of powers
# of the polynomials in differential_form_data(RS). On the curve,
# dx = -(f_y/f_x) dy, and in the swapped coordinates (X, Y) = (y, x) with
# f_S(X, Y) = f(Y, X) we have f_y(Y, X) = d f_S/dX and f_x(Y, X) = d f_S/dY.
# The swapped model integrates
#     h_i(Y, X) * (d f_S/dX) / (d f_S/dY)  dX,
# i.e. -omega_i: the sign is left out on purpose, abel_jacobi_map compensates
# by computing AJ(O - Q) on the swapped model instead of AJ(Q - O).
# This works for any basis (Baker or not): the factors of h_i are transported
# and the two partial derivatives are merged in as extra factors.
function swapped_surface(RS::RiemannSurfaceModel)
  if !isdefined(RS, :swapped_surface)
    _ensure_differentials!(RS)
    g = genus(RS)
    RS_swap = RiemannSurfaceModel()
    RS_swap.embedding = RS.embedding
    RS_swap.genus = g
    RS_swap.initial_precision = RS.initial_precision
    RS_swap.computational_precision = RS.computational_precision
    RS_swap.target_error = RS.target_error
    RS_swap.computational_error = RS.computational_error
    RS_swap.target_precision = RS.target_precision
    RS_swap.min_target_precision = 0
    RS_swap.infinity_check = 0
    RS_swap.precision_retries = 0
    RS_swap.parameters = copy(RS.parameters)
    RS_swap.integration_schemes_GL = IntegrationSchemeGL[]
    RS_swap.integration_schemes_DE = IntegrationSchemeDE[]
    RS_swap.bounds = ArbFieldElem[]

    f = defining_polynomial(RS)
    Kxy = parent(f)
    X, Y = gens(Kxy)
    fS = f(Y, X)
    RS_swap.defining_polynomial = fS
    RS_swap.input_polynomial = fS
    RS_swap.homogeneous_defining_polynomial = homogenization_RS(fS)
    RS_swap.degree = reverse(RS.degree)
    RS_swap.function_field = function_field(RS)
    RS_swap.baker_basis = RS.baker_basis

    # transported differentials (see above)
    fs, fm, _, _ = differential_form_data(RS)
    facs = elem_type(Kxy)[p(Y, X) for p in fs]
    fmS = Matrix{Int}(fm)
    for (q, e) in ((derivative(fS, 1), 1), (derivative(fS, 2), -1))
      i = findfirst(==(q), facs)
      if i === nothing
        push!(facs, q)
        fmS = vcat(fmS, fill(e, 1, g))
      else
        fmS[i, :] .+= e
      end
    end
    keep = [i for i in 1:length(facs) if any(!iszero, fmS[i, :])]
    facs = facs[keep]
    fmS = fmS[keep, :]
    mpS = [minimum(fmS[i, :]) for i in 1:length(facs)]
    rpS = [maximum(fmS[i, :]) for i in 1:length(facs)] - mpS
    RS_swap.differential_form_data = (facs, fmS, mpS, rpS)

    big_period_matrix(RS_swap)
    _analyze_special_points!(RS_swap)
    RS_swap.swapped_surface = RS
    RS.swapped_surface = RS_swap
  end
  return RS.swapped_surface
end

function ==(X::RiemannSurfaceModel, Y::RiemannSurfaceModel)
  if precision(X)!=precision(Y)
    return false
  end
  return (defining_polynomial(X) == defining_polynomial(Y)) && (embedding(X) == embedding(Y))
end

function Base.show(io::IO, rs::RiemannSurfaceModel)
  if is_terse(io)
    print(io, "Riemann surface")
  else
    if isdefined(rs, :differential_form_data)      # genus::Int is always "defined"
      print(io, "Riemann surface of genus $(rs.genus) defined by $(rs.defining_polynomial) = 0")
    else
      print(io, "Riemann surface defined by $(rs.defining_polynomial) = 0")
    end
  end
end

################################################################################
#
#  Constants
#
################################################################################

# The circles around the discriminant points (Topology.jl): radius at most
# _max_radius, and at most _radius_factor times the distance to the nearest
# other discriminant point.
_max_radius(RS::RiemannSurfaceModel) = 1/4
_radius_factor(RS::RiemannSurfaceModel) = 2/5

################################################################################
#
#  Getter functions
#
################################################################################

@doc raw"""
    defining_polynomial(RS::RiemannSurfaceModel) -> MPolyRingElem

Return the defining polynomial of the Riemann surface.
"""
function defining_polynomial(RS::RiemannSurfaceModel)
  return RS.defining_polynomial
end

@doc raw"""
    defining_polynomial_univariate(RS::RiemannSurfaceModel) -> PolyRingElem{PolyRingElem}

Return the defining polynomial of the Riemann surface as a univariate
polynomial in y over k[x].
"""
function defining_polynomial_univariate(RS::RiemannSurfaceModel)
  f = defining_polynomial(RS)
  K = base_ring(f)
  Kx, x = polynomial_ring(K, "x")
  Kxy, y = polynomial_ring(Kx, "y")

  return f(x, y)
end

@doc raw"""
    complex_defining_polynomial(RS::RiemannSurfaceModel, prec::Int = precision(RS)) -> MPolyRingElem{AcbFieldElem}

Return the defining polynomial of the Riemann surface after embedding
its coefficients into CC using the embedding chosen when creating
the Riemann surface. 

The variable prec determines the precision used for the embedding.

"""
function complex_defining_polynomial(RS::RiemannSurfaceModel, prec::Int=precision(RS))
  return _embed_mpoly(RS.defining_polynomial, RS.embedding, prec)
end

@doc raw"""
    genus(RS::RiemannSurfaceModel) -> Int

Return genus of the Riemann surface
"""
function genus(RS::RiemannSurfaceModel)
  _ensure_differentials!(RS)
  return RS.genus
end

@doc raw"""
    embedding(RS::RiemannSurfaceModel) -> Union{PosInf, InfPlc}

Return the place used to embed the Riemann surface into CC.
"""
function embedding(RS::RiemannSurfaceModel)
  return RS.embedding
end

@doc raw"""
    precision(RS::RiemannSurfaceModel) -> Int

Return the initial precision used to construct the Riemann surface.
"""
function precision(RS::RiemannSurfaceModel)
  return RS.initial_precision
end

@doc raw"""
    function_field(RS::RiemannSurfaceModel) -> FunctionField

Return the function field of the underlying plane curve.
"""
function function_field(RS::RiemannSurfaceModel)
  return RS.function_field
end

@doc raw"""
    basis_of_differentials(RS::RiemannSurfaceModel) -> Vector{FunFldDiff}

Return the basis of differentials of the underlying curve.
"""
function basis_of_differentials(RS::RiemannSurfaceModel)
  _ensure_differentials!(RS)
  return _function_field_basis_of_differentials(RS)
end

@doc raw"""
    infinite_points(RS::RiemannSurfaceModel) -> Vector{RiemannSurfacePoint}

Return the points above infinity of the Riemann surface.
"""
infinite_points(RS::RiemannSurfaceModel) = _ensure_special_points!(RS).infinite_points::Vector{RiemannSurfacePoint}

@doc raw"""
    y_infinite_points(RS::RiemannSurfaceModel) -> Vector{RiemannSurfacePoint}

Return the points on the Riemann surface for which the y-coordinate is infinity.
"""
y_infinite_points(RS::RiemannSurfaceModel) = _ensure_special_points!(RS).y_infinite_points::Vector{RiemannSurfacePoint}

@doc raw"""
    critical_points(RS::RiemannSurfaceModel) -> Vector{RiemannSurfacePoint}

Let f be the defining polynomial of the Riemann surface RS. 
Return the points on RS for which df/dy(x,y) = 0.
"""
critical_points(RS::RiemannSurfaceModel) = _ensure_special_points!(RS).critical_points::Vector{RiemannSurfacePoint}

@doc raw"""
    singular_points(RS::RiemannSurfaceModel) -> Vector{Vector{AcbFieldElem}}

Return the coordinates of the singular points of the underlying model of the 
Riemann surface
"""
singular_points(RS::RiemannSurfaceModel) = _ensure_special_points!(RS).singular_points

@doc raw"""
    base_point(RS::RiemannSurfaceModel) -> RiemannSurfacePoint

Return the internal base point of the Riemann surface. 
"""
base_point(RS::RiemannSurfaceModel) = (fundamental_group_of_punctured_P1(RS); RS.base_point::RiemannSurfacePoint)
  
@doc raw"""
    complex_field(RS::RiemannSurfaceModel) -> AcbField

Return the field over which the Riemann surface is defined.
"""
complex_field(RS::RiemannSurfaceModel) = AcbField(precision(RS))

@doc raw"""
    real_field(RS::RiemannSurfaceModel) -> ArbField

Return the real field with the precision over which the 
Riemann surface is defined.
"""
real_field(RS::RiemannSurfaceModel) = ArbField(precision(RS))
