################################################################################
#
#  RieSrf/Types.jl : shared structs (moved from the files they were used in)
#
################################################################################

################################################################################
#
#  Paths and chains in the complex plane (see Paths/CPath.jl)
#
################################################################################

# A path in the x-plane, parametrized over t in [-1, 1]. path_type:
#   :line              x(t) = (a + b)/2 + (b - a)/2 * t
#   :arc               x(t) = c + r * exp(i*((phi_a + phi_b)/2 + (phi_b - phi_a)/2 * t))
#   :circle            x(t) = c - r * exp(i*(phi_a + orientation*pi*t)), from a around c back to a
#   :point             x(t) = a (only as the neutral element when concatenating)
#   :line_to_infinity  x(t) = 2a/(1 - t), from a (t = -1) to infinity (t = 1)
# a, b are the start and end point, c the center, r the radius and phi_a,
# phi_b the angles of a and b seen from c.
mutable struct CPath
  path_type::Symbol

  # the field of the data the path was created from (the "_high" fields)
  field::AcbField

  # start and end point at the precision of the paths, and as given (used to
  # create the reverse path and copies)
  start_point::AcbFieldElem
  end_point::AcbFieldElem
  start_point_high::AcbFieldElem
  end_point_high::AcbFieldElem

  # arcs and circles: center, radius and the angles of the start and end
  # point seen from the center; orientation 1 is counterclockwise, -1 clockwise
  center::AcbFieldElem
  center_high::AcbFieldElem
  radius::ArbFieldElem
  start_angle::ArbFieldElem
  end_angle::ArbFieldElem
  orientation::Int

  length::ArbFieldElem

  # Monodromy: the fiber over the start point, sorted by sheet_ordering,
  # continued along the path and sorted again over the end point gives this
  # permutation of the sheets.
  permutation::Perm{Int}
  # Abel-Jacobi map: the y-values at the end of the path on the sheets used
  # (see _integrate_on_sheet! and _abel_jacobi_special_point!)
  sheets::Vector{AcbFieldElem}

  # Quadrature (Neurohr, Chapters 3 and 4).
  integration_scheme::Symbol            # :gl (Gauss-Legendre) or :de (double exponential)
  # r: the integrand is holomorphic on the image under the path of the
  # ellipse E_r with foci -1, 1 (GL), or of the strip |Im t| < r after the
  # tanh-sinh substitution (DE); no discriminant point lies inside
  quadrature_parameter::ArbFieldElem
  # t (in the parameter domain) of the discriminant point closest to the
  # path, where the integrand bound is sampled
  closest_disc_point_parameter::AcbFieldElem
  number_of_nodes::ZZRingElem
  bounds::Vector{ArbFieldElem}          # bounds M of the integrands on E_r
  integration_scheme_index::Int         # index of the scheme among the GL/DE schemes
  # a line close to a discriminant point is split into several subpaths with
  # their own quadrature (Neurohr 4.7.5); otherwise the path itself
  subpaths::Vector{CPath}

  # m x g: row s holds the integrals of the g differentials along the lift
  # of the path that starts on sheet s
  integral_matrix::AcbMatrix

  reverse_path::CPath

  # a, b: start and end point; CC_path: the precision of the path points
  function CPath(path_type::Symbol, a::AcbFieldElem, b::AcbFieldElem,
                 CC_path::AcbField = parent(a); center::AcbFieldElem = zero(parent(a)),
                 radius::ArbFieldElem = real(zero(parent(a))), orientation::Int = 1)
    @req path_type in (:line, :arc, :circle, :point, :line_to_infinity) "Unknown path type $path_type."
    path = new()
    CC = parent(a)
    RR = ArbField(precision(CC))
    path.path_type = path_type
    path.field = CC
    path.start_point_high = a
    path.end_point_high = b
    path.start_point = CC_path(a)
    path.end_point = CC_path(b)
    path.center_high = center
    path.center = CC_path(center)
    path.radius = ArbField(precision(CC_path))(radius)
    path.orientation = orientation
    path.bounds = ArbFieldElem[]

    if path_type === :line
      path.length = abs(path.end_point - path.start_point)
    elseif path_type === :point
      path.length = zero(RR)
    elseif path_type === :line_to_infinity
      path.end_point = CC(1/0)
      path.length = RR(1/0)
    else
      # angles of the start and end point seen from the center, in
      # [phi_a, phi_a + 2pi) in the direction of the orientation (a real or
      # imaginary part that contains zero is set to zero first, so that the
      # angle is well defined)
      two_pi = 2*const_pi(RR)
      phi_a = _mod2pi(angle(trim_zero(a - center)))
      phi_b = _mod2pi(angle(trim_zero(b - center)))
      if orientation == 1 && phi_b < phi_a
        phi_b += two_pi
      elseif orientation == -1 && phi_a < phi_b
        phi_a += two_pi
      end
      path.start_angle = phi_a
      path.end_angle = phi_b
      path.length = path_type === :arc ? abs(phi_b - phi_a) * radius : two_pi * radius
    end
    return path
  end
end

# A chain: a sequence of paths, each starting where the previous one ends.
mutable struct CChain
  paths::Vector{CPath}
  permutation::Perm{Int}                # product of the permutations of the paths
  sheets::Vector{AcbFieldElem}          # Abel-Jacobi map: y-values at the end, as for paths
  is_closed::Bool
  start_point::AcbFieldElem
  end_point::AcbFieldElem
  # m x g, as for a path: row s holds the integrals along the lift of the
  # chain that starts on sheet s (see _set_chain_integral!)
  integral_matrix::AcbMatrix
  # loops around a discriminant point (or infinity): that point
  center::AcbFieldElem
  # chains around discriminant points: the points of the Riemann surface
  # over the center (see SpecialPoints.jl)
  points

  function CChain(paths::Vector{CPath})
    is_connected, is_closed = test_chain(paths)
    @req is_connected "A chain should consist of a connected sequence of paths."
    chain = new()
    chain.paths = paths
    chain.is_closed = is_closed
    chain.start_point = start_point(paths[1])
    chain.end_point = end_point(paths[end])
    if all(path -> isdefined(path, :permutation), paths)
      chain.permutation = prod(map(permutation, paths))
      if all(path -> isdefined(path, :integral_matrix), paths)
        _set_chain_integral!(chain)
      end
    end
    return chain
  end

  function CChain(paths::Vector{CPath}, center::AcbFieldElem)
    chain = CChain(paths)
    chain.center = center
    return chain
  end
end

# A Gauss-Legendre integration scheme: nodes and weights for one group of
# subpaths (see Grouping.jl). The number of nodes N is chosen for the ellipse
# parameter r, the integrand bound and the error (Neurohr, Chapter 3): r has
# a strong influence on N, the bound only a logarithmic one.
mutable struct IntegrationSchemeGL
  abscissae::Vector{ArbFieldElem}       # the nodes in [-1, 1]
  weights::Vector{ArbFieldElem}         # the weights
  quadrature_parameter::ArbFieldElem    # the ellipse parameter r
  number_of_nodes::Int                  # N
  bounds::Vector{ArbFieldElem}          # the integrand bound used
  prec::Int                             # precision of the nodes and weights

  function IntegrationSchemeGL(r::ArbFieldElem, prec::Int, error::ArbFieldElem, bound::ArbFieldElem)
    scheme = new()
    N = _gauss_legendre_parameters(r, error, bound)
    scheme.number_of_nodes = N
    scheme.abscissae, scheme.weights = _gauss_legendre_nodes(N, prec)
    scheme.quadrature_parameter = r
    scheme.bounds = [bound]
    scheme.prec = prec
    return scheme
  end
end

# A double exponential (tanh-sinh) integration scheme for one group of
# subpaths. prec: precision of the nodes; target: the parameters are chosen
# for errors 2^-target.
mutable struct IntegrationSchemeDE
  abscissae::Vector{ArbFieldElem}       # the nodes in (-1, 1)
  weights::Vector{ArbFieldElem}         # the weights
  quadrature_parameter::ArbFieldElem    # the strip parameter r (0 < r < pi/2)
  number_of_nodes::Int                  # 2N + 1
  bounds::Vector{ArbFieldElem}          # the two integrand bounds used (M_1, M_2)
  prec::Int                             # precision of the nodes and weights

  function IntegrationSchemeDE(r::ArbFieldElem, prec::Int, bounds::Vector{ArbFieldElem},
                               target::Int = prec)
    RR = parent(r)
    @req RR(0) < r < const_pi(RR)/2 "The parameter of a double exponential scheme must lie in (0, pi/2) (got $r)."
    scheme = new()
    scheme.prec = prec
    N, h = _double_exponential_parameters(r, target, bounds)
    scheme.abscissae, scheme.weights = _tanh_sinh_nodes(N, h)
    scheme.quadrature_parameter = r
    scheme.bounds = bounds
    scheme.number_of_nodes = 2*N + 1
    return scheme
  end
end

struct DiscriminantFactorData
  p                          # monic irreducible factor in K[x]
  vanishing::Vector{Bool}    # vanishing[i+1]: coefficient of y^i is divisible by p
  ydeg::Int                  # degree of f(alpha, y)
  pattern::Vector{Int}       # multiplicities of the distinct finite roots, descending
end

# A plane model of a Riemann surface on which period matrices are computed:
# the general algorithm (RiemannSurfaceModel) or the one for superelliptic
# curves y^m = p(x) (SuperellipticModel).
abstract type AbstractRiemannSurfaceModel end

mutable struct RiemannSurfaceModel <: AbstractRiemannSurfaceModel
  #A polynomial f(x,y) in K[x,y] for some number field K defining the Riemann
  #surface (or equivalently) a not necessarily smooth plane curve in P_2
  defining_polynomial::AbstractAlgebra.Generic.MPoly{AbsSimpleNumFieldElem}

  homogeneous_defining_polynomial::AbstractAlgebra.Generic.MPoly{AbsSimpleNumFieldElem}

  genus::Int
  function_field::AbstractAlgebra.Generic.AbsSimpleFunctionField

  #The degree of the field extension K(x,y)/f over K(x).
  degree::Vector{Int}

  #The small period matrix of X
  small_period_matrix::AcbMatrix
  big_period_matrix::AcbMatrix

  #The embedding used to embed X
  embedding::Union{PosInf, InfPlc}

  #The points P for which disc(f(P,y)) = 0. This includes the ramification
  #points and the singular points of the curve
  discriminant_points::Vector{AcbFieldElem}
  # the points for the paths (precision _path_point_precision), and the same
  # points at the much higher precision needed by the Abel-Jacobi map
  # (computed only when the Abel-Jacobi map asks for them, see
  # discriminant_points_high_prec)
  discriminant_points_internal::Vector{AcbFieldElem}
  discriminant_points_high_prec::Vector{AcbFieldElem}
  safe_radii::Vector{ArbFieldElem}

  disc_factor_data::Vector{DiscriminantFactorData}

  # (factors of disc_y(f), factors of the leading coefficient of f in y),
  # polynomials in K[x], computed once (see _discriminant_factors)
  discriminant_factors::Any

  #Special points
  infinite_points
  y_infinite_points

  #Coordinates of the points of the form (x:y:0) in homogeneous coordinates.
  infinity_coords::Vector{Vector{AcbFieldElem}}

  #x-coordinates of critical points
  critical_values::Vector{AcbFieldElem}

  #Critical points
  critical_points

  #Singular points of the underlying model. (Not of the Riemann surface)
  singular_points::Vector{Vector{AcbFieldElem}}
  finite_singularities::Vector{Vector{AcbFieldElem}}
  infinite_singularities::Vector{Vector{AcbFieldElem}}

  #Abel-Jacobi Map
  ajm_starting_points::Vector{AcbFieldElem}
  ajm_discriminant_points::Vector{CChain}
  ajm_infinite_points::CPath
  sheet_to_sheet_integrals::AcbMatrix
  base_point

  swapped_surface::RiemannSurfaceModel

  # The RiemannSurface this model belongs to (not set for internal helper
  # models such as swapped_surface), and the projective transformation from
  # the coordinates of the input curve to the coordinates of this model: the
  # point (x : y : z) of the input curve corresponds to transform * (x, y, z).
  surface::Any
  transform::Any

  #A set of generators of the fundamental group pi_1 of P^1/D where D is the set
  #of discriminant points.
  #It consists of a tuple (L, G) where
  # - L is a list of paths
  # - G consists of generators for pi_1. Each generator is encoded by a
  #sequence of indices. These indices refer to the paths in L.
  #
  # If for example G[1] = [1, 23, 12, -1]. Then the first
  # generator is given by composing the paths L[1], L[23], L[12] and
  # reverse(L[1]).
  fundamental_group_of_P1::Tuple{Vector{CPath}, Vector{Vector{Int}}}
  # discriminant point circled by each generator (same order as the generators)
  pi1_ordered_disc_points::Vector{AcbFieldElem}
  pi1_chains::Vector{CChain}

  closed_chains::Vector{CChain}
  inf_chain::CChain
  # direct_infinity: [line from the base point to the big circle, circle]
  direct_inf_paths::Vector{CPath}
  # 1: the direct loop around infinity agrees with the composed one,
  # -1: it does not, 0: not checked
  infinity_check::Int

  #The permutations of the sheets that correspond to walking along the chains
  #of paths that are generators of the fundamental group of P1. 
  # where (1,3) is the permutation.
  
  monodromy_representation::Vector{Perm{Int}}

  #Data encoding the homology basis.
  # We encode homology cycles in H_1(RS, Z) in the following way:
  # Each cycle Gamma_i in L is given as a sequence of integers
  # [s_i1, b_i1, s_i2, b_i2, ..., s_in, b_in ].
  # Here each s_ij gives the index of the sheet we start or end up in
  # and each b_ij gives the index of the branch point we circle around to get
  # there.

  # As an example, the cycle [1, 3, 5, 2, 1] means that we start in sheet 1,
  # circle around branch point nr 3 to move to sheet 5, circle around branch
  # point number 2 to finish in sheet 1 again and complete a full circle.

  homology_basis::Tuple{Vector{Vector{Int}}, ZZMatrix, ZZMatrix}

  # A basis of differential forms computed by either
  # - Riemann-Roch computations
  # - Using Baker's Theorem. Baker's Theorem says that if the number of
  # interior points of the Newton polygon associated to the defining polynomial
  # is equal to g, a basis of differential forms is given by
  # the set of all x^iy^jdx/Df_y where (i,j) is an interior point of the
  # Newton polygon.
  basis_of_differentials::Vector{FunFldDiff}

  #A boolean that checks whether a Baker basis was used or not.
  baker_basis::Bool

  # The basis of differential forms often shares common factors.
  # We can reduce the number of polynomial evaluations we need to do
  # by evaluating all of the factors at every abscissa and taking products of
  # the computed values.
  #
  # differential_form_data = (factor_set, factor_matrix, min_pows, range_pows):
  # - factor_set: the n common factors of the differentials
  # - factor_matrix: the n x g matrix of exponents: g_k = prod_l factor_l^factor_matrix[l, k]
  # - min_pows: the smallest exponent of every factor (minimum of its row)
  # - range_pows: largest minus smallest exponent of every factor
  # (see Integrand.jl).
  #
  # Example: basis x^3*(x^2-5), (x^2-5)^10*(x-7)^3, x*(x-7), x^5*(x^2-5)
  #  factor_set = [x, x-7, x^2-5]
  #  factor_matrix =
  #  [3, 0, 1, 5]
  #  [0, 3, 1, 0]
  #  [1, 10, 0, 1]
  #  min_pows = [0, 0, 0]
  #  range_pows = [5, 3, 10]

  differential_form_data::Tuple{Vector{mpoly_type(AbsSimpleNumFieldElem)}, Matrix{Int}, Vector{Int}, Vector{Int}}

  # A list of integration schemes used for computations. An integration scheme
  # consists of a list of abscissae, weights and a bunch of parameters.
  # For efficiency we want to reuse integrations schemes as much as possible.
  # Every path we integrate over gets assigned one of these integrations schemes.
  integration_schemes_GL::Vector{IntegrationSchemeGL}
  integration_schemes_DE::Vector{IntegrationSchemeDE}

  # A list of bounds used duting computations
  bounds::Vector{ArbFieldElem}

  # The equation as given by the user (before QQ is turned into a number field).
  input_polynomial::MPolyRingElem

  # Integration parameters as set by the user (may contain :auto), and the
  # concrete values used once the computation has started. Once
  # resolved_parameters is set, the parameters cannot be changed anymore.
  parameters::IntegrationParameters
  resolved_parameters::IntegrationParameters
  # set if big_period_matrix threw; later calls refuse to retry
  computation_failure::Any

  #A collection of fields and error bounds needed to ensure correctness
  #TODO: Check which ones are actually used and necessary. Optimize this.

  initial_precision::Int
  computational_precision::Int
  internal_precision::Int

  target_error::ArbFieldElem
  computational_error::ArbFieldElem
  # the integrals are computed for errors 2^-target_precision (see _quadrature_guard_bits)
  target_precision::Int
  # lower bound for the target precision (set by a precision retry)
  min_target_precision::Int
  # number of precision retries of the period computation (0 or 1)
  precision_retries::Int

  real_reduction_matrix::ArbMatrix
  complex_reduction_matrices::Vector{AcbMatrix}

  inner_faces::Vector{Vector{Int}}

  #The constructor for a Riemann surface object

  function RiemannSurfaceModel()
    RS = new()
    return RS
  end

  function RiemannSurfaceModel(f::MPolyRingElem, v::T, prec::Int = 100;
                          parameters::IntegrationParameters = IntegrationParameters()) where T<:Union{PosInf, InfPlc}
    # Only cheap data is computed here. The basis of differentials, the period
    # matrix and the special points are computed when they are first needed
    # (see _ensure_differentials!, big_period_matrix, _ensure_special_points!).
    RS = new()
    RS.input_polynomial = f
    RS.parameters = copy(_check_integration_parameters(parameters))

    k = base_ring(f)
    if k == QQ
      old_k = parent(f)
      k = rationals_as_number_field()[1]
      kx, s = polynomial_ring(k, old_k.S)
      f = f(s[1], s[2])
    end
    kx, x = rational_function_field(k, "x")
    kxy, y = polynomial_ring(kx, "y")
    F, a = function_field(f(x, y))

    @req v.field == k "The given place does not belong to the field."

    RS.homogeneous_defining_polynomial = homogenization_RS(f)
    RS.defining_polynomial = f
    RS.initial_precision = prec
    RS.embedding = v
    RS.function_field = F

    # quadrature target T and working precision W = T + guard (see
    # _quadrature_guard_bits). (Before: W = prec + (4 + max degree) digits and
    # quadrature errors 10^-(digits of W + 10), i.e. far beyond prec.)
    # (estimate with K = 1024 subpaths; fixed in _set_target_precision!)
    target_precision = _initial_target_precision(prec)
    computational_precision = target_precision + _rounding_guard_bits()
    RS.target_precision = target_precision
    RS.computational_precision = computational_precision
    RS.min_target_precision = 0
    RS.infinity_check = 0
    RS.precision_retries = 0

    initial_precision_digits = floor(Int, prec*log(2)/log(10))

    RR = ArbField(computational_precision)

    RS.target_error = RR(10)^(-initial_precision_digits - 1)
    RS.computational_error = RR(2)^(-target_precision)

    RS.bounds = ArbFieldElem[]
    RS.degree = reverse(degrees(f))

    return RS
  end
end

mutable struct RiemannSurfacePoint
  coordx::AcbFieldElem 
  coordy::AcbFieldElem 
  homog_coords::Vector{AcbFieldElem}
  parent::RiemannSurfaceModel 
  is_singular::Bool
  is_finite::Bool
  ramification_index::Int
  index::Int
  sheets::Vector{Int}

  function RiemannSurfacePoint(RS::RiemannSurfaceModel) 
    P = new()
    P.parent = RS
    return P
  end
end

#The class RiemannSurfaceDivisor represents a divisor on a Riemann surface

mutable struct RiemannSurfaceDivisor

  #The core data of the divisor is stored by two arrays:
  #the points in the support and the corresponding multiplicities.
  points::Vector{RiemannSurfacePoint}
  mults::Vector{Int}

  degree::Int
  abel_jacobi_value::AcbMatrix
  riemann_surface::RiemannSurfaceModel


  function RiemannSurfaceDivisor(RS::RiemannSurfaceModel) 
    D = new()
    D.riemann_surface = RS
    D.degree = 0
    D.points = RiemannSurfacePoint[]
    D.mults = Int[]
    return D
  end

  function RiemannSurfaceDivisor(S::Vector{RiemannSurfacePoint}, V::Vector{Int}) 
    D = new()
    number_of_points = length(S)
    @req number_of_points == length(V) "Length of the array of points should match the array of multiplicities."
    @req number_of_points >= 0 "Array of points should not be empty."

    D.riemann_surface = parent(S[1])

    D.degree = sum(V;init = 0)
    D.points = RiemannSurfacePoint[]
    D.mults = Int[]
    for k in (1:number_of_points)
      if V[k] != 0
        i = findfirst(x -> x == S[k], D.points)
        if i == nothing
          push!(D.points, S[k])
          push!(D.mults,V[k])
        else
          D.mults[i]+=V[k]
        end
      end
    end
    return D
  end
end


################################################################################
#
#  Superelliptic curves y^m = p(x)
#
################################################################################

# An edge of the spanning tree between the branch points: from branch point a
# (already in the tree) to branch point b. method: :chebyshev (m = 2) or :de.
# r: its quadrature parameter (ellipse parameter resp. half width of the strip
# for double exponential integration), computed in Float64.
mutable struct SuperellipticEdge
  a::Int
  b::Int
  method::Symbol
  r::Float64
  N::Int                       # number of nodes (Chebyshev) resp. 2N+1 (DE)
  h::Float64                   # step size (DE)
  log2_bound::Float64          # log2 of the bound for the integrand
  function SuperellipticEdge(a::Int, b::Int)
    E = new()
    E.a = a
    E.b = b
    return E
  end
end

@doc raw"""
    SuperellipticModel

The model y^m = p(x) of a superelliptic curve (p separable of degree n >= 3)
on which the period matrices are computed with the algorithm of Molin and
Neurohr: integrals along the edges of a spanning tree between the branch
points, with an explicit branch of y = p(x)^(1/m) on each edge.
"""
mutable struct SuperellipticModel <: AbstractRiemannSurfaceModel
  surface::Any                 # the RiemannSurface it belongs to
  transform::Any               # identity or swap (3x3 over the base field)
  defining_polynomial::MPolyRingElem   # y^m - p(x)
  p::PolyRingElem              # p(x) over the base field
  m::Int
  n::Int
  delta::Int                   # gcd(m, n)
  genus::Int
  embedding::Union{PosInf, InfPlc}
  initial_precision::Int
  target_precision::Int        # the quadrature is chosen for errors 2^-target_precision
  computational_precision::Int
  min_target_precision::Int    # raised by a precision retry
  precision_retries::Int
  parameters::IntegrationParameters
  resolved_parameters::IntegrationParameters

  # the basis of differentials x^i dx / y^j as pairs (i, j)
  differentials::Vector{Tuple{Int, Int}}
  basis_of_differentials::Vector{FunFldDiff}

  branch_points::Vector{AcbFieldElem}
  tree::Vector{SuperellipticEdge}
  # integrals of the differentials along the edges on the reference branch
  # (needed for the Abel-Jacobi map)
  elementary_integrals::Vector{Vector{AcbFieldElem}}
  intersection_matrix::ZZMatrix
  symplectic_transform::ZZMatrix
  big_period_matrix::AcbMatrix
  small_period_matrix::AcbMatrix
  complex_reduction_matrices::Vector{AcbMatrix}
  real_reduction_matrix::ArbMatrix

  # for the Abel-Jacobi map
  low_branch_points::Vector{ComplexF64}  # the branch points in Float64 (same order)
  log_lc::Float64                        # log |leading coefficient of p|
  lc_root::AcbFieldElem                  # lc^(1/m) (the branch used for all edges)
  tree_paths::Vector{Vector{Int}}        # edges from the root to each branch point
  abel_jacobi_branch_points::Vector{Vector{AcbFieldElem}}  # AJ(P_k - P_root)

  # points of the curve as given, created by this model (see _se_point)
  infinite_points::Vector{RiemannSurfacePoint}
  ramification_points::Vector{RiemannSurfacePoint}

  function SuperellipticModel()
    C = new()
    C.min_target_precision = 0
    C.precision_retries = 0
    return C
  end
end

@doc raw"""
    RiemannSurface

The compact Riemann surface of a plane curve f(x, y) = 0 over a number field,
embedded into the complex numbers. Create it with `riemann_surface`.

The numerical work is done on plane models of the curve (see
`RiemannSurfaceModel`): the *original* model is the curve as given, the
*computational* model is the one the period matrices are computed on. See
`riemann_surface` for how the computational model is chosen.
"""
mutable struct RiemannSurface
  # the equation as given by the user, the embedding and the precision
  input_polynomial::MPolyRingElem
  embedding::Union{PosInf, InfPlc}
  precision::Int

  # integration parameters for the computational model
  parameters::IntegrationParameters

  # type of the numerical output of the public functions (period matrices,
  # Abel-Jacobi map, discriminant points, ...): :acb (AcbField/ArbField of
  # the precision) or :complex (ComplexField/RealField). Internally always
  # AcbField. See riemann_surface(f, ::ComplexField).
  output::Symbol

  # :auto, :original, :swapped, :superelliptic, or an invertible 3x3 matrix
  # (see riemann_surface)
  model::Any

  # the curve as given (identity transformation), and the model used for the
  # period matrices; the same object if the original model is used
  original::RiemannSurfaceModel
  computational::AbstractRiemannSurfaceModel

  # model = :auto: the criterion values of the candidate models (see _choose_model)
  model_costs::Vector{Tuple{Symbol, Float64}}

  # for a curve given in P^n (riemann_surface(F::Vector, prec)): the named
  # tuple (equations, projection), see space_curve
  space_curve::Any

  function RiemannSurface(f::MPolyRingElem, v::Union{PosInf, InfPlc}, prec::Int,
                          parameters::IntegrationParameters, model)
    RS = new()
    RS.input_polynomial = f
    RS.embedding = v
    RS.precision = prec
    RS.parameters = copy(_check_integration_parameters(parameters))
    RS.output = _default_output()
    RS.model = model
    return RS
  end
end
