################################################################################
#
#          RieSrf/RiemannSurface.jl : Riemann surfaces
#
# (C) 2025 Jeroen Hanselman
# This is a port of the Riemann surfaces package written by
# Christian Neurohr. It is based on his Phd thesis
# https://www.researchgate.net/publication/329100697_Efficient_integration_on_Riemann_surfaces_applications
# Neurohr's package can be found on https://github.com/christianneurohr/RiemannSurfaces
#
################################################################################

#=
Example code:
using Hecke.RiemannSurfaces
K = rationals_as_number_field()[1]

Kxy, (x,y) = polynomial_ring(K, ["x","y"])
f = x^5 + x^4 +x^3 -x + 4 -y^2

v = real_places(K)[1]
RS = RiemannSurface(f, v)
tau = small_period_matrix(RS)
=#


#A class defining a Riemann surface X.

mutable struct RiemannSurface
  #A polynomial f(x,y) in K[x,y] for some number field K defining the Riemann
  #surface (or equivalently) a not necessarily smooth plane curve in P_2
  defining_polynomial::AbstractAlgebra.Generic.MPoly{AbsSimpleNumFieldElem}

  homogeneous_defining_polynomial::AbstractAlgebra.Generic.MPoly{AbsSimpleNumFieldElem}

  genus::Int
  function_field::AbstractAlgebra.Generic.FunctionField

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
  discriminant_points_high_prec::Vector{AcbFieldElem}
  safe_radii::Vector{ArbFieldElem}

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

  swapped_surface::RiemannSurface


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

  closed_chains::Vector{CChain}
  inf_chain::CChain

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
  # The variable differential_form_data consists of four parts:
  # - factor_set: The set of n common factors used for integration
  # - factor_matrix: A g by n matrix storing the exponents of the n factors
  # for the g differential forms.
  # - min_pows: A list of smallest exponents occurring in the factor set
  # for every given factor
  # - range_pows: The number of different powers we need to compute
  #
  # Example: Basis is x^3*(x^2-5), (x^2-5)^10*(x-7)^3, x*(x-7), x^5*(x^2-5)
  #  factor_set = [x, x-7, x^2-5]
  #  factor_matrix is
  #  [3, 0, 1, 5]
  #  [0, 3, 1, 0]
  #  [1, 10, 0, 1]
  #  min_pows = [1,1,1]
  #  range_pows = [4, 2, 9]

  differential_form_data::Tuple{Vector{mpoly_type(AbsSimpleNumFieldElem)}, Matrix{Int}, Vector{Int}, Vector{Int}}

  #Evaluate differential_differential_factors_matrix is a function that
  # takes as its input
  # - a list of factors
  # - The point x0 we want to integrate at
  # - a list of m ys such that f(y) = x0 for every y in ys.
  # As output it gives an m by g matrix A such that A_ij = g_j(x0, y_i)
  # where the omega_j = g_jdx are the basis of differential forms.
  # The function is constructed by using differential forms data.
  # The factors are given as input to allow us to choose the precision of the
  # input factors.
  #evaluate_differential_factors_matrix::Any

  # A list of integration schemes used for computations. An integration scheme
  # consists of a list of abscissae, weights and a bunch of parameters.
  # For efficiency we want to reuse integrations schemes as much as possible.
  # Every path we integrate over gets assigned one of these integrations schemes.
  integration_schemes::Vector{IntegrationScheme}

  # A list of bounds used duting computations
  bounds::Vector{ArbFieldElem}

  #String specifying the integration method used when integrating differential forms.
  #The options are "heuristic" and "rigorous". It is set to "heuristic" by default
  integration_method::String

  #A collection of fields and error bounds needed to ensure correctness
  #TODO: Check which ones are actually used and necessary. Optimize this.
  prec::Int
  weak_error::ArbFieldElem
  error::ArbFieldElem
  extra_error::ArbFieldElem
  real_field::ArbField
  complex_field::AcbField
  complex_field2::AcbField
  computational_precision_complex_field::AcbField
  extra_prec::Int
  max_prec::Int

  real_reduction_matrix::ArbMatrix
  complex_reduction_matrices::Vector{AcbMatrix}

  inner_faces::Vector{Vector{Int}}

  #The constructor for a Riemann surface object

  function RiemannSurface()
    RS = new()
    return RS
  end

  function RiemannSurface(f::MPolyRingElem, v::T, prec::Int = 100; integration_method::String = "rigorous") where T<:Union{PosInf, InfPlc}

    k = base_ring(f)
    kx, x = rational_function_field(k, "x")
    kxy, y = polynomial_ring(kx, "y")
    f_new = f(x, y)
    F, a = function_field(f_new)
    diff_base = basis_of_differentials(F)

    RS = new()
    if k == QQ
      old_k = parent(f)
      k = rationals_as_number_field()[1]
      kx, s = polynomial_ring(k, old_k.S)
      f = f(s[1], s[2])
      kx, x = rational_function_field(k, "x")
      kxy, y = polynomial_ring(kx, "y")
      f_new = f(x, y)
      F, a = function_field(f_new)
      #diff_base = map(t -> t(s[1],s[2]), diff_base)
    end

    @req v.field == k "The given place does not beling to the field."



    RS.homogeneous_defining_polynomial = homogenization_RS(f)

  
    RS.defining_polynomial = f
    RS.prec = prec
    RS.embedding = v
    RS.function_field = F
    RS.basis_of_differentials = diff_base
    g = length(diff_base)
    RS.genus = g

    if g == 0
      error("Cannot construct Riemann surface of genus 0.")
    end
   

    if integration_method != "heuristic" && integration_method != "rigorous"
      error("invalid integration method. Valid options are \"rigorous\" or \"heuristic\"")
    end
    RS.integration_method = integration_method

    mpoly_kxy = parent(f)
    mpoly_x, mpol_y = gens(mpoly_kxy)

    #Computed a Newton polygon and decide whether we can use a Baker basis or not.
    inner_fac = inner_faces(f)
    RS.inner_faces = inner_fac
    if length(inner_fac) == g
      RS.baker_basis = true
      x, y = gens(parent(f))
      factor_set = [x, y, derivative(f, 2)]
      n = length(factor_set)
      min_x = minimum([t[1] for t in inner_fac])
      max_x = maximum([t[1] for t in inner_fac])
      min_y = minimum([t[2] for t in inner_fac])
      max_y = maximum([t[2] for t in inner_fac])
      min_pows = [min_x - 1, min_y - 1, -1]
	    range_pows = [max_x - 1, max_y - 1, -1] - min_pows

      factor_matrix = zeros(Int, n, g)

      baker_diffs = FunFldDiff[]

      for i in (1:g)
        factor_matrix[1, i] = inner_fac[i][1] - 1
        factor_matrix[2, i] = inner_fac[i][2] - 1
        factor_matrix[3, i] = -1

        s = gen(base_ring(F))
        t = gen(F)
        #omega = (factor_set[1](s,t)^(inner_fac[i][1] - 1) * factor_set[2](s,t)^(inner_fac[i][2] - 1) //factor_set[3](s,t))*differential(F(s))
        #push!(baker_diffs, omega)
      end
      #RS.basis_of_differentials = baker_diffs

    else
      RS.baker_basis = false
      RS.basis_of_differentials = diff_base
      #Compute the differential forms data mentioned above.
      factor_set = Set{MPolyRingElem}()
      factored_nums = Dict{AbstractAlgebra.Generic.MPoly{AbsSimpleNumFieldElem}, Int64}[]
      factored_denoms = Dict{AbstractAlgebra.Generic.MPoly{AbsSimpleNumFieldElem}, Int64}[]
      #Gather all the factors occurring in the basis of differential forms
      for i in 1:g
        num_diff_i_fac = Dict(p => e for (p,e) in factor(to_mpoly(mpoly_kxy, numerator(diff_base[1].f))))
        denom_diff_i_fac = Dict(p => e for (p,e) in factor(denominator(diff_base[1].f)(mpoly_x)))

        union!(factor_set, Set(keys(num_diff_i_fac)), Set(keys(denom_diff_i_fac)))

        push!(factored_nums, num_diff_i_fac)
        push!(factored_denoms, denom_diff_i_fac)
      end

      #Turn set into sequence so we can enumerate
      factor_set = collect(factor_set)
      number_of_factors = length(factor_set)
      n = length(factor_set)
      factor_matrix = zero_matrix(Int, n, g)
      for j in 1:g
        for i in 1:n
          if haskey(factored_nums[j], factor_set[i])
            factor_matrix[i,j] = get(factored_nums[j], factor_set[i], 0)
          end

          if haskey(factored_denoms[j], factor_set[i])
            factor_matrix[i,j] = -get(factored_denoms[j], factor_set[i], 0)
          end
        end
      end

		  min_pows= [minimum( factor_matrix[j, 1:g]) for j in 1:n]
	    range_pows= [maximum( factor_matrix[j, 1:g]) for j in 1:n] - min_pows
    end
#=
    function evaluate_differential_factors_matrix(factors, x0, ys)
      Kxy = parent(factors[1])
      Ky, y = polynomial_ring(base_ring(Kxy), "y")
      CC = base_ring(factors[1])
      m = length(ys)

      result = matrix(CC, m , g, [one(CC) for t in (1:m*g)])
      for l in 1:length(factors)
        f = factors[l]
        fx0 = f(x0, y)
        for s in 1:m
          fx0ys = CC(fx0(ys[s]))
          factor_at_xys = [fx0ys^min_pows[l] ]
          for k in (1:range_pows[l])
            push!(factor_at_xys, factor_at_xys[k]*fx0ys)
          end
          for k in 1:g
            #Let omega_i = g_i * dx where the omega form a basis of
            #differentials. Then result[s][k] = g_k(x0, ys) where the
            #ys are the m preimages in the fiber f^(-1)(x0).
            result[s, k] *= factor_at_xys[factor_matrix[l, k] - min_pows[l]+1]
          end
        end
      end
      return result
    end
=#
    RS.differential_form_data = (factor_set, factor_matrix, min_pows, range_pows)
    #RS.evaluate_differential_factors_matrix = evaluate_differential_factors_matrix

    b10_prec = floor(Int, prec*log(2)/log(10))
    b10_extra_prec = b10_prec + 3 + max(degree(f, 1), degree(f, 2))
    extra_prec = prec + floor(Int, (4 + max(degree(f, 1), degree(f, 2)) )*log(10)/log(2))
    RS.complex_field = AcbField(prec)
    RR = ArbField(prec + extra_prec)
    RS.real_field = RR

    RS.extra_prec = extra_prec


    RS.weak_error = RR(10)^(-(2//3) *b10_prec)
    RS.error = RR(10)^(-b10_prec - 1)
    RS.extra_error = RR(10)^(-b10_extra_prec - 10)
    RS.bounds = ArbFieldElem[]
    RS.degree = reverse(degrees(f))

    big_period_matrix(RS)
    analyze_special_points(RS)

    return RS
  end
end

@doc raw"""
function riemann_surface(f::MPolyRingElem, prec::Int = 100) -> RiemannSurface

Construct the Riemann surface S corresponding to the desingularization of the
plane curve model defined by f(x,y) = 0 embedded into P^2 over CC with initial
precision equal to prec bits.

When a Riemann surface is created the following data is computed:
- The monodromy group of the cover S -> P^1, (x:y:z) -> (x:z)
- A basis of the homology of the Riemann surface
- The period matrix associated to the Riemann surface

"""
function riemann_surface(f::MPolyRingElem, prec::Int = 100; integration_method::String = "heuristic")
  k = base_ring(f)
  if k == QQ
    k = rationals_as_number_field()[1]
  end
  v = infinite_places(k)[1]
  RS = riemann_surface(f, v, prec, integration_method = integration_method)
  return RS
end

@doc raw"""
function riemann_surface(f::MPolyRingElem, v::Union{PosInf, InfPlc},
   prec::Int = 100) -> RiemannSurface

Construct the Riemann surface S corresponding to the desingularization of the
plane curve model defined by f(x,y) = 0 embedded into P^2 over CC by the 
embedding corresponding to the place v, and with initial precision equal to 
prec bits.

When a Riemann surface is created the following data is computed:
- The monodromy group of the cover S -> P^1, (x:y:z) -> (x:z)
- A basis of the homology of the Riemann surface
- The period matrix associated to the Riemann surface

"""
function riemann_surface(f::MPolyRingElem, v::T, prec::Int = 100; 
  integration_method::String = "rigorous") where T<:Union{PosInf, InfPlc}
  return RiemannSurface(f, v, prec, integration_method = integration_method) 
end


function swapped_surface(RS::RiemannSurface)
#Compute the Riemann surface obtained by projecting y to P1 instead of x.
  if !isdefined(RS, :swapped_surface)
    g = genus(RS)
    RS_swap = RiemannSurface()
    RS_swap.embedding = RS.embedding
    RS_swap.genus = g
    RS_swap.prec = RS.prec
    RS_swap.extra_prec = RS.extra_prec
    RS_swap.error = RS.error
    RS_swap.weak_error = RS.weak_error
    RS_swap.extra_error = RS.extra_error
    RS_swap.integration_method = RS.integration_method
    RS_swap.integration_schemes = IntegrationScheme[]
    RS_swap.bounds = ArbFieldElem[]

    f = defining_polynomial(RS)
    Kxy = parent(f)
    K = base_ring(Kxy)
    x, y = gens(Kxy)
    f = f(y,x)
    RS_swap.defining_polynomial = f
    RS_swap.homogeneous_defining_polynomial = homogenization_RS(f)
    RS_swap.degree = reverse(RS.degree)
    F = function_field(RS)
    RS_swap.function_field = F

    #Change differentials
    RS_swap.baker_basis = RS.baker_basis
    if RS_swap.baker_basis
      RS_swap.inner_faces = [ [s[2],s[1]] for s in RS.inner_faces ]
      inner_fac = RS_swap.inner_faces 
      x, y = gens(parent(f))
      factor_set = [x, y, derivative(f, 2)]
      n = length(factor_set)
      min_x = minimum([t[1] for t in inner_fac])
      max_x = maximum([t[1] for t in inner_fac])
      min_y = minimum([t[2] for t in inner_fac])
      max_y = maximum([t[2] for t in inner_fac])
      min_pows = [min_x - 1, min_y - 1, -1]
	    range_pows = [max_x - 1, max_y - 1, -1] - min_pows

      factor_matrix = zeros(Int, n, g)

      baker_diffs = []

      for i in (1:g)
        factor_matrix[1, i] = inner_fac[i][1] - 1
        factor_matrix[2, i] = inner_fac[i][2] - 1
        factor_matrix[3, i] = -1

        s = gen(base_ring(F))
        t = gen(F)
        omega = (factor_set[1](s,t)^(inner_fac[i][1] - 1) * factor_set[2](s,t)^(inner_fac[i][2] - 1) //factor_set[3](s,t))*differential(F(s))
        push!(baker_diffs, omega)
      end
      RS_swap.basis_of_differentials = baker_diffs
    else
      RS_swap.basis_of_differentials = RS.basis_of_differentials

      FF = function_field(RS)
      y = gen(FF)
      x = separating_element(FF)
      dx = differential(x)

      factor_set = Set{MPolyRingElem}()
      factored_nums = MPolyRingElem[]
      factored_denoms = MPolyRingElem[]

      dfy = derivative(f,2)(x,y)
      dfx = derivative(f,1)(x,y)
      dfydfx = dfy/dfx

      diff_base = RS_swap.basis_of_differentials * dfydfx

      #Let's see what this does.
      for i in 1:g
        num_diff_i_fac = Dict(p => e for (p,e) in factor(to_mpoly(mpoly_kxy, numerator(diff_base[1].f))))
        denom_diff_i_fac = Dict(p => e for (p,e) in factor(denominator(diff_base[1].f)(mpoly_x)))

        union!(factor_set, Set(keys(num_diff_i_fac)), Set(keys(denom_diff_i_fac)))

        push!(factored_nums, num_diff_i_fac)
        push!(factored_denoms, denom_diff_i_fac)
      end


       #Turn set into sequence so we can enumerate
      factor_set = collect(factor_set)
      number_of_factors = length(factor_set)
      n = length(factor_set)
      factor_matrix = zero_matrix(Int, n, g)
      for j in 1:g
        for i in 1:n
          if haskey(factored_nums[j], factor_set[i])
            factor_matrix[i,j] = get(factored_nums[j], factor_set[i], 0)
          end

          if haskey(factored_denoms[j], factor_set[i])
            factor_matrix[i,j] = -get(factored_denoms[j], factor_set[i], 0)
          end
        end
      end

		  min_pows= [minimum( factor_matrix[j, 1:g]) for j in 1:n]
	    range_pows= [maximum( factor_matrix[j, 1:g]) for j in 1:n] - min_pows

    end

    #=function evaluate_differential_factors_matrix(factors, x0, ys)
        Kxy = parent(factors[1])
        Ky, y = polynomial_ring(base_ring(Kxy), "y")
        CC = base_ring(factors[1])
        m = length(ys)

        result = matrix(CC, m , g, [one(CC) for t in (1:m*g)])
        for l in 1:length(factors)
          f = factors[l]
          fx0 = f(x0, y)
          for s in 1:m
            fx0ys = CC(fx0(ys[s]))
            factor_at_xys = [fx0ys^min_pows[l] ]
            for k in (1:range_pows[l])
              push!(factor_at_xys, factor_at_xys[k]*fx0ys)
            end
            for k in 1:g
              #Let omega_i = g_i * dx where the omega form a basis of
              #differentials. Then result[s][k] = g_k(x0, ys) where the
              #ys are the m preimages in the fiber f^(-1)(x0).
              result[s, k] *= factor_at_xys[factor_matrix[l, k] - min_pows[l]+1]
            end
          end
        end
        return result
      end
      =#
    RS_swap.differential_form_data = (factor_set, factor_matrix, min_pows, range_pows)
    #RS_swap.evaluate_differential_factors_matrix = evaluate_differential_factors_matrix


    big_period_matrix(RS_swap)

    analyze_special_points(RS_swap)
    RS_swap.swapped_surface = RS
    RS.swapped_surface = RS_swap
  end
end

function fiber(f::MPolyRingElem, x0::AcbFieldElem)
  #Compute fiber
  CC = base_ring(f)
  CCz, z = polynomial_ring(CC)
  roots, mults = find_roots_with_mult(f(x0, z))
  B =  sortperm(roots, lt = sheet_ordering)
  fiber_x = AcbFieldElem[]
  for i in (1:length(mults))
    for j in (1:mults[B[i]])
      push!(fiber_x, roots[B[i]])
    end
  end
  return fiber_x
end

function evaluate_differential_factors_matrix(RS::RiemannSurface, factors::Vector{ AbstractAlgebra.Generic.MPoly{AcbFieldElem}}, x0::AcbFieldElem, ys::Vector{AcbFieldElem})
  Kxy = parent(factors[1])
  Ky, y = polynomial_ring(base_ring(Kxy), "y")
  CC = base_ring(factors[1])
  m = length(ys)

  g = genus(RS)

  _, factor_matrix, min_pows, range_pows = RS.differential_form_data

  result = matrix(CC, m, g, [one(CC) for t in (1:m*g)])
  for l in 1:length(factors)
    f = factors[l]
    fx0 = f(x0, y)
    for s in 1:m
      fx0ys = fx0(ys[s])
      factor_at_xys = Vector{AcbFieldElem}(undef, range_pows[l]+1)
      factor_at_xys[1] = fx0ys^min_pows[l] 
      for k in (1:range_pows[l])
        factor_at_xys[k+1] = factor_at_xys[k]*fx0ys
      end
      for k in 1:g
        #Let omega_i = g_i * dx where the omega form a basis of
        #differentials. Then result[s][k] = g_k(x0, ys) where the
        #ys are the m preimages in the fiber f^(-1)(x0).
        result[s, k] *= factor_at_xys[factor_matrix[l, k] - min_pows[l]+1]
      end
    end
  end
  return result
end

mutable struct RiemannSurfacePoint
  coordx::AcbFieldElem 
  coordy::AcbFieldElem 
  homog_coords::Vector{AcbFieldElem}
  parent::RiemannSurface 
  is_singular::Bool
  is_finite::Bool
  ramification_index::Int
  index::Int
  sheets::Vector{Int}

  function RiemannSurfacePoint(RS::RiemannSurface) 
    P = new()
    P.parent = RS
    return P
  end
end

function ==(X::RiemannSurface, Y::RiemannSurface)
  if precision(X)!=precision(Y)
    return false
  end
  return (defining_polynomial(X) == defining_polynomial(Y)) && (embedding(X) == embedding(Y))
end



#Coerce univariate polynomial over univariate polynomial ring to R.
function to_mpoly(R, h)
  kxy = R
  x, y = gens(R)
  return sum([coeff(h, i)(x)*y^i for i in (0:degree(h))])
end

#Nicer printing
function Base.show(io::IO, rs::RiemannSurface)
  if is_terse(io)
    print(io, "Riemann surface")
  else
    print(io, "Riemann surface of genus $(rs.genus) defined by $(rs.defining_polynomial) = 0")
  end
end


################################################################################
#
#  Constants
#
################################################################################

function max_radius(RS::RiemannSurface)
  return (1/4)
end

function radius_factor(RS::RiemannSurface)
  return (2/5)
end


################################################################################
#
#  Getter functions
#
################################################################################

@doc raw"""
function defining_polynomial(RS::RiemannSurface) -> MPolyRingElem

Return the defining polynomial of the Riemann surface.
"""
function defining_polynomial(RS::RiemannSurface)
  return RS.defining_polynomial
end

@doc raw"""
function defining_polynomial(RS::RiemannSurface)
  -> PolyRingElem{PolyRingElem}

Return the defining polynomial of the Riemann surface as a univariate
polynomial over k[x].
"""
function defining_polynomial_univariate(RS::RiemannSurface)
  f = defining_polynomial(RS)
  K = base_ring(f)
  Kx, x = polynomial_ring(K, "x")
  Kxy, y = polynomial_ring(Kx, "y")

  return f(x, y)
end

@doc raw"""
function complex_defining_polynomial(RS::RiemannSurface, prec::Int=RS.prec)
  -> MPolyRingElem{AcbFieldElem}
Return the defining polynomial of the Riemann surface after embedding
its coefficients into CC using the embedding chosen when creating
the Riemann surface. 

The variable prec determines the precision used for the embedding.

"""
function complex_defining_polynomial(RS::RiemannSurface, prec::Int=RS.prec)
  return embed_mpoly(RS.defining_polynomial, RS.embedding, prec)
end

@doc raw"""
function genus(RS::RiemannSurface) -> Int

Return genus of the Riemann surface
"""
function genus(RS::RiemannSurface)
  return RS.genus
end

@doc raw"""
function embedding(RS::RiemannSurface) -> Union{PosInf, InfPlc}

Return the place used to embed the Riemann surface into CC.
"""
function embedding(RS::RiemannSurface)
  return RS.embedding
end

@doc raw"""
function precision(RS::RiemannSurface) -> Int

Return the initial precision ued to construct the Riemann surface.
"""
function precision(RS::RiemannSurface)
  return RS.prec
end

@doc raw"""
function function_field(RS::RiemannSurface) -> FunctionField

Return the function field of the underlying plane curve.
"""
function function_field(RS::RiemannSurface)
  return RS.function_field
end

@doc raw"""
function basis_of_differentials(RS::RiemannSurface) -> Vector{FunFldDiff}

Return the basis of differentials of the underlying curve.
"""
function basis_of_differentials(RS::RiemannSurface)
  return RS.basis_of_differentials
end

@doc raw"""
function infinite_points(RS::RiemannSurface) -> Vector{RiemannSurfacePoint}

Return the points above infinity of the Riemann surface.
"""
infinite_points(RS::RiemannSurface) = RS.infinite_points::Vector{RiemannSurfacePoint}

@doc raw"""
function infinite_points(RS::RiemannSurface) -> Vector{RiemannSurfacePoint}

Return the points on the Riemann surface for which the y-coordinate is infinity.
"""
y_infinite_points(RS::RiemannSurface) = RS.y_infinite_points::Vector{RiemannSurfacePoint}

@doc raw"""
function critical_points(RS::RiemannSurface) -> Vector{RiemannSurfacePoint}

Let f be the defining polynomial of the Riemann surface RS. 
Return the points on RS for which df/dy(x,y) = 0.
"""
critical_points(RS::RiemannSurface) = RS.critical_points::Vector{RiemannSurfacePoint}

@doc raw"""
function singular_points(RS::RiemannSurface) ->Vector{Vector{AcbFieldElem}}

Return the coordinates of the singular points of the underlying model of the 
Riemann surface
"""
singular_points(RS::RiemannSurface) = RS.singular_points
  
  
@doc raw"""
function base_point(RS::RiemannSurface) -> RiemannSurfacePoint

Return the internal base point of the Riemann surface. 
"""
base_point(RS::RiemannSurface) = RS.base_point::RiemannSurfacePoint
  
@doc raw"""
function complex_field(RS::RiemannSurface) -> AcbField

Return the field over which the Riemann surface is defined.
"""
complex_field(RS::RiemannSurface) = RS.complex_field

function assure_has_discriminant_points(RS::RiemannSurface)
  if isdefined(RS, :discriminant_points)
    return nothing
  else

    f = defining_polynomial_univariate(RS)
    Kxy = parent(f)
    Kx = base_ring(f)

    v = embedding(RS)

    g = genus(RS)
    a0 = leading_coefficient(f)
    RR = ArbField(precision(RS))
    D_points, D1, D2 = _discriminant_points_to_prec(RS, 660)
    RS.discriminant_points = D_points
    v = embedding(RS)

    XB = maximum(abs(P) for P in D_points) + RR(max_radius(RS))

    if length(D2) == 0
      L0_safe_radius = RR(1)
    else
      D2_distance = minimum([closest_point(P, collect(setdiff(D_points, Set([P]))) )[1] for P in D2])
      L0_safe_radius = minimum([radius_factor(RS)*D2_distance, RR(max_radius(RS))])
    end

    low_prec = 66
    f_low_prec = embed_mpoly(defining_polynomial(RS), v, low_prec)
    C_low_prec = AcbField(low_prec)
    R_low_prec = ArbField(low_prec)
    R, x = polynomial_ring(C_low_prec, "x")

    #Bounds |y(x)| on f(x,y) = 0 for |x| < xb and |x-x_0| > dist for all zeros x_0 of LC */
    function bound_y_values(xb, dist)
      coeffs_y = reverse(coefficients(f_low_prec,2))
      coeffs_y = [ c(x, 0) for c in coeffs_y ]
      max_y_abs = R_low_prec(0)
      max_x_abs = R_low_prec(0)
      for k in (1:RS.degree[1]-1)
        coeffs_x = coefficients(coeffs_y[k+1])
        if length(coeffs_x) >= 0
                Ak = sum([ abs(coeffs_x[j]) * xb^(j) for j in (0:length(coeffs_x)-1) ]; init = R_low_prec(0))
                max_y_abs = maximum([max_y_abs, Ak/(abs(evaluate(leading_coefficient(a0), v.embedding, low_prec)*dist^degree(a0)))^(1/k)])
                max_x_abs = maximum([max_x_abs, Ak])
        end
      end
      return maximum([2*max_y_abs, max_x_abs])
    end
    YB = bound_y_values(XB, (100/101)*L0_safe_radius)
    DF_data = RS.differential_form_data
    DFF = DF_data[1]
    DFF_emb = [embed_mpoly(g, v, low_prec) for g in DFF]
    max_diff_abs = ArbFieldElem[]
    for k in (1:length(DFF))
      omega = DFF_emb[k]
      coeffs = collect(coefficients(omega))
      mons = collect(monomials(omega))
      val = abs(sum([ abs(coeffs[j]) * mons[j](XB,YB) for j in (1:length(coeffs))];init = R_low_prec(0)))
      push!(max_diff_abs, maximum([val,R_low_prec(1)]))
    end
    one_vec = [R_low_prec(1) for i in (1:g)]
    for l in (1:length(DFF))
      val = max_diff_abs[l]
      fac_xys = [R_low_prec(1) for i in (1:DF_data[4][l]+1)]
      for k in (0:DF_data[4][l])
        if DF_data[3][l]+k <= 0 
          fac_xys[k+1] = R_low_prec(1)
        else
          fac_xys[k+1] = max_diff_abs[l]^(DF_data[3][l]+k)
        end
      end
      for k in (1:g)
        one_vec[k] *= fac_xys[DF_data[2][l, k]-DF_data[3][l]+1]
      end
    end
    bound = maximum(vcat(max_diff_abs, [YB], one_vec))

    additional_prec = ceil(Int, log(bound)/log(2))
    max_prec = RS.extra_prec + maximum([additional_prec, 67])
    RS.max_prec = max_prec

    precision_for_DP = RS.degree[1] * max_prec

    if precision_for_DP > 660
      D_points = _discriminant_points_to_prec(RS, precision_for_DP)[1]
    end

    RS.discriminant_points_high_prec = D_points

    RS.ajm_discriminant_points = Vector{CChain}(undef, length(D_points))

    return nothing
  end
end

@doc raw"""
function discriminant_points(RS::RiemannSurface, copy::Bool = true) -> Vector{AcbFieldElem}

Let f be the defining polynomial of the Riemann surface RS. 
Return the set of roots of the discriminant (and the leading coeﬃcients) of f as
a polynomial in y.
"""
function discriminant_points(RS::RiemannSurface, copy::Bool = true)
  assure_has_discriminant_points(RS)
  if copy
    return deepcopy(RS.discriminant_points)
  else
    return RS.discriminant_points
  end
end

function internal_discriminant_points(RS::RiemannSurface, copy::Bool = true)
  assure_has_discriminant_points(RS)
  if copy
    return deepcopy(RS.discriminant_points_high_prec)
  else
    return RS.discriminant_points_high_prec
  end
end


function _discriminant_points_to_prec(RS::RiemannSurface, prec::Int)
    f = defining_polynomial_univariate(RS)
    Kxy = parent(f)
    Kx = base_ring(f)

    v = embedding(RS)

    RR = ArbField(prec)
    g = genus(RS)
    a0 = leading_coefficient(f)
    disc_y_factors = AcbPolyRingElem[]
    a0_factors = AcbPolyRingElem[]


    for (f,e) in factor(discriminant(f))
      push!(disc_y_factors, embed_poly(f, v, prec))
    end

    for (f,e) in factor(a0)
      push!(a0_factors, embed_poly(f, v, prec))
    end

    D1 = vcat(AcbFieldElem[],[roots(fac, initial_prec = prec) for fac in disc_y_factors]...)
    D2 = vcat(AcbFieldElem[],[roots(fac, initial_prec = prec) for fac in a0_factors]...)
    D_points = sort!(union(D1, D2), lt = sheet_ordering)
    return D_points, D1, D2
  end
  


################################################################################
#
#  Monodromy computation
#
################################################################################

@doc raw"""
function monodromy_representation(RS::RiemannSurface) 
  -> Vector{Tuple{Vector{CPath}, Perm{Int}}}

A list of generators of the monodromy group. Every
element is of the form (P, sigma) where P is a closed chain of paths and sigma
is the permutation that encodes how the sheets get permuted when moving
along the closed chain. The paths in the list correpond to the generators of 
the fundamental group of P1. 
"""
function monodromy_representation(RS::RiemannSurface)
  if !isdefined(RS, :monodromy_representation)
    big_period_matrix(RS)
  end
  return RS.monodromy_representation
end


#Commenting this out. It is technically faster than computing the monodromy
#representation during the period matrix computation, but I don't expect 
#anyone would really care about that. As the period matrix computation is
#now done automatically on creation of the Riemann surface, this method 
#became obsolete.
#=

function monodromy_representation(RS::RiemannSurface)
  if isdefined(RS, :monodromy_representation)
    return RS.monodromy_representation
  else
    return _monodromy_representation(RS)
  end
end

function _monodromy_representation(RS::RiemannSurface)

  # We first take a basis of the fundamental group.
  # paths consists of a list of paths, pi1_gens consists of a set of generators
  # of p1. Every generated is represented as a list of integers. These integers
  # tell us which elements in paths we need to concatenate to get the path
  # that corresponds to the generator of pi1.
  paths, pi1_gens = fundamental_group_of_punctured_P1(RS, true)
  f = defining_polynomial(RS)
  m = degree(f, 2)

  s_m = SymmetricGroup(m)

  for i in (1:length(paths))
    path = paths[i]
    # We compute the number of pieces we need to divide a path in in order to
    # do analytic continuation
    N = ceil(Int, length(path)) +1

    #If the path is a circle or an arc we multiply by an additional factor
    if path_type(path) in [1,2]
      N = 4*N
    end


    RR = ArbField(precision(RS))

    t = 1/N
    abscissae = [RR(n*t) for n in (-N + 1: N - 1)]

    # Perform analytic continuation along the closed loop path with
    # starting point x0. In the algorithm we start with the m ys lying
    # over x0 are first sorted according to the "sheet_ordering" function.
    # The output consists of the ys lying over x0 that we get when continuously
    # moving them along the path.
    An = analytic_continuation(RS, path, abscissae)

    # As the order of the ys lying over x0 changes after analytic continuation,
    # we can reorder using sheet_ordering again to find out how they were
    # permuted to get the corresponding element of the monodromy group.
    path_perm = sortperm(An[end][2], lt = sheet_ordering)

    # Store the permutation with the path
    assign_permutation(path, inv(s_m(path_perm)))
  end

  mon_rep = Tuple{Vector{CPath}, Perm{Int}}[]

  # Chain all permutations of all the generators of pi1 together to find
  # the monodromy of the chosen generator.
  for gamma in pi1_gens
    chain = map(t -> ((t > 0) ? paths[t] : reverse(paths[-t])), gamma)
    gamma_perm = prod(map(permutation, chain))

    if gamma_perm != one(s_m)
      push!(mon_rep, (chain, gamma_perm))
     end
  end

  inf_chain = CPath[]
  inf_perm = one(s_m)

  for g in mon_rep
    inf_chain = vcat(inf_chain, map(reverse, g[1]))
    inf_perm *= g[2]
  end

  #Additionally add the inverse of the chain around infinity.
  push!(mon_rep, (reverse(inf_chain), inv(inf_perm)))
  RS.monodromy_representation = mon_rep
  return mon_rep
end
=#

@doc raw"""
function monodromy_group(RS::RiemannSurface) -> Vector{Perm{Int64}}

Returns all the elements in the monodromy group of the finite cover
pi: RS -> P^1.
"""
function monodromy_group(RS::RiemannSurface)
  mon_rep = monodromy_representation(RS)
  gens = map(t -> t[2], mon_rep)
  return closure(gens, *)
end

@doc raw"""
fundamental_group_of_punctured_P1(RS::RiemannSurface) -> Tuple{Vector{CPath}, Vector{Vector{Int}}}

A set of generators of the fundamental group pi_1 of P^1/D where D is the set
of discriminant points.
The output consists of a tuple (L, G) where
- L is a list of paths
- G consists of generators for pi_1. Each generator is encoded by a
sequence of indices. These indices refer to the paths in L.
"""
function fundamental_group_of_punctured_P1(RS::RiemannSurface, abel_jacobi::Bool = true)
  if isdefined(RS, :fundamental_group_of_P1)
    return RS.fundamental_group_of_P1
  else
    return _fundamental_group_of_punctured_P1(RS, abel_jacobi)
  end
end

#Follows algorithm 4.3.1 in Neurohr
function _fundamental_group_of_punctured_P1(RS::RiemannSurface, abel_jacobi::Bool = true)

  #Compute the exceptional values x_i
  D_points = internal_discriminant_points(RS)
  d = length(D_points)
  CC = parent(D_points[1])
  RR = ArbField(precision(CC))
  prec = precision(RS)

  CC_low = AcbField(prec)

  #Step 1 compute a minimal spanning tree
  edges = minimal_spanning_tree(D_points)

  #Choose a suitable base point and connect it to the spanning tree

  #Multiple ways to choose the base point.
  #This one is most suitable when computing abel-jacobi maps.
  #Take some integer point to the left of the point with the smallest real part


  if abel_jacobi

    #Real part should already be minimal in D_points
    #x0 = CC(min(floor(ZZRingElem, real(D_points[1]) - 2*max_radius(RS)), -1))

    #Catch the case where flooring an arb is not ambiguous. Floor to the smallest of the two options.
    x0 = try floor(ZZRingElem, real(D_points[1]) - 2*max_radius(RS))
       catch err
       try  floor(ZZRingElem, real(D_points[1]) - 2*max_radius(RS) -0.5)
         catch err
         error("Precision too low")
       end
    end

    #Connect base point to closest point in D_points

    distance, index = closest_point(CC(x0), D_points)

    push!(D_points, CC(x0))
    push!(edges, (d +1, index))
  else
  #Here we take the one that is most suitable if one doesn't need to compute Abel-Jacobi maps according to Neurohr, i.e. we split the longest edge in the middle.
  #(Last edge should be the longest in the way we compute minimal_spanning trees right now.)

    left = edges[end][1]
    right = edges[end][2]
    pop!(edges)
    x0 = (D_points[left] + D_points[right])//2
    push!(D_points, x0)
    push!(edges, (d + 1, left))
    push!(edges, (d + 1, right))
  end
  #Now we sort the points by angle and level

  path_edges = Int[]
  past_nodes = [d + 1]
  current_node = d + 1

  left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
  right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse,edges))

  leftright = vcat(left_edges, right_edges)

  current_angle = zero(RR)

  angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
    return mod2pi(angle(D_points[t1[2]] - D_points[t1[1]]) - current_angle) < mod2pi(angle(D_points[t2[2]] - D_points[t2[1]]) - current_angle)
  end

  sort!(leftright, lt = angle_ordering)

  path_edges = vcat(path_edges, leftright)
  current_level = vcat(left_edges, right_edges)

  while length(path_edges) < length(edges)
    next_level = Int[]
    for edge in current_level

      previous_node = edge[1]
      current_node = edge[2]
      current_angle = angle(D_points[previous_node] - D_points[current_node])

      left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
      right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse, edges))
      leftright = vcat(left_edges, right_edges)

      angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
        return mod2pi(angle(D_points[t1[2]] - D_points[t1[1]]) - current_angle) < mod2pi(angle(D_points[t2[2]] - D_points[t2[1]]) - current_angle)
      end

      sort!(leftright, lt = angle_ordering)
      next_level = vcat(next_level, leftright)
      path_edges = vcat(path_edges, leftright)

      push!(past_nodes, current_node)
    end

    current_level = next_level
  end

  #Construct paths to every end point starting at x0 using a Depth-First Search

  #Paths to all nodes
  paths = [[(d+1, d+1)]]

  ordered_disc_points = Int64[]
  find_paths_to_end([(d+1, d+1)], paths, path_edges, ordered_disc_points)
  ordered_disc_points = map(t -> D_points[t], ordered_disc_points)

  radii = [min(RR(max_radius(RS)), RR(radius_factor(RS)) * minimum(map(t -> abs(t - D_points[j]), vcat(D_points[1:j-1], D_points[j+1:end])))) for j in (1:d)]
  RS.safe_radii = radii
  c_lines = CPath[]


  #Find the line pieces of the paths.
  for edge in path_edges
    a = D_points[edge[1]]
    b = D_points[edge[2]]
    ab_length = b - a


    #Base point is not a discriminant point, so we don't need to circle around it
    if edge[1] == d + 1
      new_start_point = a
    else
      #Intersect the line between a and b with the circle of radius r_a around a
      new_start_point = a + (radii[edge[1]])*ab_length//(abs(ab_length))
    end
    #Intersect the line between a and b with the circle of radius r_b around b
    new_end_point = b - (radii[edge[2]])*ab_length//(abs(ab_length))
    push!(c_lines, c_line(new_start_point, new_end_point, CC_low))
  end

  paths = map(t -> t[2:end], paths[2:end])
  path_indices = map(path -> map(t -> findfirst(x -> x == t, path_edges), path), paths)

  c_arcs = CPath[]
  paths_with_arcs = Vector{Int}[]

  #We reconstruct the paths
  for path in reverse(path_indices)

    i = path[end]
    loop = Int[]

    arc_start = arc_end = c_lines[i].end_point_high
    center = D_points[path_edges[i][end]]

    #We need to loop around the end of the path, but we may
    #have already constructed parts of the loop when constructing previous paths
    #We therefore find these first and add them.

    n = length(c_arcs)
    for j in (1:n)
      arc = c_arcs[j]
      if contains(arc_end, end_point(arc)) && contains(end_point(arc), arc_end)
        push!(loop, j + d)
        arc_end = arc.start_point_high
      end
    end

    push!(c_arcs, c_arc(arc_start, arc_end, center, CC_low))
    push!(loop, d + n + 1)

    path_to_loop = Int[]

    #Now we attach the line piece
    push!(path_to_loop, i)

    #We add the inverse arcs as moving towards the points we want to encircle we move clockwise
    for k in (length(path)-1:-1:1)

      arc_buffer = Int[]
      old_line_piece = c_lines[path[k+1]]
      new_line_piece = c_lines[path[k]]
      arc_start = old_line_piece.start_point_high
      arc_end = new_line_piece.end_point_high
      center = D_points[path_edges[path[k]][end]]

     #Similar to before. Maybe make a function out of it
      n = length(c_arcs)
      for j in (1:n)
        arc = c_arcs[j]
        if contains(arc_end, end_point(arc)) && contains(end_point(arc), arc_end)
          push!(arc_buffer, -j - d)
          arc_end = arc.start_point_high
        end
      end

      if arc_start != arc_end
        push!(c_arcs, c_arc(arc_start, arc_end, center, CC_low))
        push!(arc_buffer, - d - n - 1)
      end

      path_to_loop = vcat(path_to_loop, reverse(arc_buffer))
      push!(path_to_loop, path[k])
    end
    push!(paths_with_arcs, vcat(reverse(path_to_loop), reverse(loop), -path_to_loop))
  end
  paths = vcat(c_lines, c_arcs)
  pi1 = paths, reverse(paths_with_arcs)
  ys = fiber(complex_defining_polynomial(RS), CC(x0))
  base_point = RiemannSurfacePoint(RS)
  base_point.coordx = CC(x0)
  base_point.index = 1
  base_point.sheets = [1]
  base_point.is_finite = true
  base_point.coordy = ys[1] 
  base_point.homog_coords = [base_point.coordx, base_point.coordy, CC(1)]
  RS.base_point = base_point
  RS.fundamental_group_of_P1 = pi1
  RS.ajm_starting_points = [ start_point(p) for p in paths]
  return paths, reverse(paths_with_arcs), ordered_disc_points
end

function find_paths_to_end(path, paths, edges, ordered_disc_points)
  end_path = path[end][2]
  temp_paths = paths
  for (start_edge, end_edge) in edges
    if start_edge == end_path
      push!(ordered_disc_points, end_edge)
      newpath = vcat(path, [(start_edge, end_edge)])
      push!(paths, newpath)
      find_paths_to_end(newpath, paths, edges, ordered_disc_points)
    end
  end
end


#Could be optimized probably. Kruskal's algorithm
function minimal_spanning_tree(v::Vector{AcbFieldElem})

  edge_weights = Tuple{ArbFieldElem, Tuple{Int64, Int64}}[]

  N = length(v)

  #Compute the weights for all the edges
  for i in (1:N)
    for j in (i+1: N)
      push!(edge_weights, (abs(v[i] - v[j]), (i, j)))
    end
  end

  sort!(edge_weights)

  tree = Tuple{Int, Int}[]

  disjoint_trees = [Set([i]) for i in (1:N)]

  i = 1

  while length(tree) < N - 1

    (s1, s2) = edge_weights[i][2]

    s1_index = findfirst(t -> s1 in t, disjoint_trees)

    s1_tree = disjoint_trees[s1_index]

    if s2 in s1_tree
      #continue
    else
      s2_tree = popat!(disjoint_trees, findfirst(t -> s2 in t, disjoint_trees))
      push!(tree, (s1, s2))
      union!(s1_tree, s2_tree)
    end
    i+= 1
  end

  return tree
end


################################################################################
#
#  Analytic Continuation
#
################################################################################

#Let gamma be the path [-1,1] -> P^1 and let pi: RS -> P^1 
#be the projection given by (x,y) -> x
#This function performs analytic continuation along the path gamma
#by iteratively lifting the path along pi. It keeps track of all the
#different lifts y. 
#The output will be returned as a list of tuples 
#[(x0, [y_i]_0), ... (xn, [y_i]_n)] where the y_i correspond to all the lifts 
#over the respective x value. The xj correspond to the preimages of the input
#abscissae

function analytic_continuation(RS::RiemannSurface, path::CPath, abscissae::Vector{ArbFieldElem},
  start_ys::Vector{AcbFieldElem}=AcbFieldElem[], prec = 0)
  v = embedding(RS)
  if prec < precision(RS)
    prec = precision(RS)
  end

  RR = ArbField(prec)

  #Embed the polynomial in CC
  f = embed_mpoly(defining_polynomial(RS), v, prec)
  CC = base_ring(f)

  f = change_base_ring(CC, f, parent = parent(f))

  m = degree(f, 2)

  #Add start and end point to the abscissae
  u = vcat([-one(RR)], abscissae, [one(RR)])
  N = length(u)

  x_vals = Vector{AcbFieldElem}(undef, N)
  y_vals = [Vector{AcbFieldElem}(undef, m) for i in (1:N)]

  z = Vector{AcbFieldElem}(undef, m)

  #Compute x0
  x_vals[1] = evaluate(path, u[1])

  Kxy = parent(f)
  Ky, y = polynomial_ring(base_ring(Kxy), "y")

  # If we are given initial values we use those. If we don't we compute the
  # roots of f(x0, y)  0 and sort them.
  if length(start_ys) == 0
    y_vals[1] = sort!(roots(f(x_vals[1], y), initial_prec = prec), lt = sheet_ordering)
  else
    y_vals[1] = start_ys
  end

  # For every tiny path piece from x_vals[l-1] to x_vals[l] we compute how
  # the ys that we lifted move along with them using recursive continuation.
  # We do this until we reach the end of the path
  for l in (2:N)
    x_vals[l] = evaluate(path, u[l])
    z .= y_vals[l-1]

    y_vals[l] .= recursive_continuation(f, x_vals[l-1], x_vals[l], z)
  end
  return x_vals, y_vals
end

#Recursive continuation used for analytic continuation
function recursive_continuation(f::AbstractAlgebra.Generic.MPoly{AcbFieldElem}, x1::AcbFieldElem, x2::AcbFieldElem, z::Vector{AcbFieldElem})
  Kxy = parent(f)
  Ky, y = polynomial_ring(base_ring(Kxy), "y")
  CC = base_ring(f)
  prec = precision(CC)
  m = degree(f, 2)
  temp_vec = acb_vec(m)
  temp_vec_res = acb_vec(m)

  #Following Algorithm 4.5.1 in Neurohr's thesis page 75. W, w and d are as in (4.19)
  ff = f(x2, y)
  ff = ff/leading_coefficient(ff)
  W = [ ff(z[i]) for i in (1:m)]
  d = ArbFieldElem[]
  for i in (1:m)
    for j in (1:i)
      if i != j
        zij = z[i] - z[j]
        push!(d, abs(zij))
        W[i]/= zij
        W[j]/= -zij
      end
    end
  end

  d = reduce(min, d)

  #d = reduce(min, [abs(z[i] - z[j]) for (i, j) in filter(t-> t[1] != t[2], [a for a in Iterators.product((1:m), (1:m))])])

  #W = [ ff(z[i]) // prod([z[i] - z[j] for j in vcat((1:i - 1), i+1:m)];init = one(CC)) for i in (1:m)]
  w = reduce(max, map(t -> real(t)^2 +imag(t)^2, W))
  
  if w < d // (2*m) 
    fillacb!(temp_vec, z)
    dd = ccall((:acb_poly_find_roots, libflint), Cint, (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Ptr{acb_struct}, Int, Int), temp_vec_res, evaluate(f,[Ky(x2), y]), temp_vec, 0, prec)
    @assert dd == m
    z .= array(CC, temp_vec_res, m)

    acb_vec_clear(temp_vec, m)
    acb_vec_clear(temp_vec_res, m)

    return z
  else
    midpoint = (x1 + x2)//2
    return recursive_continuation(f, midpoint, x2, recursive_continuation(f, x1, midpoint, z))
  end
end

#Recursive continuation without checking the proper bound that ensures
#we are close enough to ensure we are able to isolate roots properly
#and without using arb for the analytic continuation.
#This is useful when values start converging to infinity and checking
#bounds would get us into an infinite loop.
function recursive_continuation_manual(f::AbstractAlgebra.Generic.MPoly{AcbFieldElem}, x1::AcbFieldElem, x2::AcbFieldElem, z::Vector{AcbFieldElem}, err::ArbFieldElem, target_error::ArbFieldElem = parent(err)(-1))
  Kxy = parent(f)
  Ky, y = polynomial_ring(base_ring(Kxy), "y")
  CC = base_ring(f)
  prec = precision(CC)
  RR = ArbField(prec)
  m = degree(f, 2)
  temp_vec = acb_vec(m)
  temp_vec_res = acb_vec(m)

  ff = f(x2, y)
  ff = ff/leading_coefficient(ff)
  W = [ ff(z[i]) // prod([z[i] - z[j] for j in vcat((1:i - 1), i+1:m)];init = one(CC)) for i in (1:m)]
  w0 = reduce(max, map(t -> real(t)^2 +imag(t)^2, W))
  next_error = w0
  last_error = RR(1/0)

  while next_error > err && next_error < last_error
    z = [ z[i] - W[i] for i in (1:m) ]
    W = [ ff(z[i]) // prod([z[i] - z[j] for j in vcat((1:i - 1), i+1:m)];init = one(CC)) for i in (1:m)]
    last_error = next_error
    next_error = reduce(max, map(t -> real(t)^2 +imag(t)^2, W))
  end

  fillacb!(temp_vec, z)
  if target_error > RR(0)
    if next_error > target_error && next_error >= last_error
      return z, true
    end
  end

  dd = ccall((:acb_poly_find_roots, libflint), Cint, (Ptr{acb_struct}, Ref{AcbPolyRingElem}, Ptr{acb_struct}, Int, Int), temp_vec_res, evaluate(f,[Ky(x2), y]), temp_vec, 0, prec)
  @assert dd == m
  z .= array(CC, temp_vec_res, m)
  acb_vec_clear(temp_vec, m)
  acb_vec_clear(temp_vec_res, m)
  return z, false
end

################################################################################
#
#  Homology basis
#
################################################################################

# 
@doc raw"""
function homology_basis(RS::RiemannSurface) 
  -> Tuple{Vector{Vector{Int}}, ZZMatrix, ZZMatrix}

Computes a hoology basis for the Riemann surface RS.
Assuming the map C -> P1 is m to 1, the output consists of
- a list of cycles L corresponding to r := 2g + m - 1 cycles circling 
around at least 2 ramification points. There will be m - 1 related 
cycles in here.
- An r x r matrix K encoding the intersection pairing between the r cycles.
Its entries are either 1, 0. or -1 depending on whether the cycles intersect
and how their orientation is when they do intersect.
- A symplectic matrix S that ensure that S^T K S is equal to a matrix
where the upper left block consists of the normalized polarization and the
rest consists of zeros. I.e.:
[I  0 0 ... 0]
[0 -I 0 ... 0]
[|  | | ... 0]
[0  0 0 ... 0]
"""
function homology_basis(RS::RiemannSurface)
  if isdefined(RS, :homology_basis)
    return RS.homology_basis
  end
  return _homology_basis(RS)
end

# The homology basis is computed using the Tretkoff algorithm described
# in Neurohr's thesis 4.6.1 on page 82 and in the Appendix of the thesis.
# Assuming the map C -> P1 is m to 1, the output consists of
# - a list of cycles L corresponding to r := 2g + m - 1 cycles circling around at least
# 2 ramification points. There will be m - 1 related cycles in here
# - An r x r matrix K encoding the intersection pairing between the r cycles.
# Its entries are either 1, 0. or -1 depending on whether the cycles intersect
# and how their orientation is when they do intersect.
# - A symplectic matrix S that ensure that S^T K S is equal to a matrix
# where the upper left block consists of the normalized polarization and the
# rest consists of zeros.
# [I  0 0 ... 0]
# [0 -I 0 ... 0]
# [|  | | ... 0]
# [0  0 0 ... 0]
# This ensures that any period matrix P computed using L will have the
# property that P * S = [P1, P2, O_{m-1}]
# where [P1, P2] forms the big period matrix and O_{m-1} is supposed to be the
# zero matrix. This matrix O_{m-1} can be used as a sanity check for the
#numerical computations.

# REMARK: The choice of the polarization is a convention. We could also opt
# to adopt a different convention if we want to.
function _homology_basis(RS::RiemannSurface)
  gens = monodromy_representation(RS)
  s_n = parent(gens[1])
  n = s_n.n
  d = length(gens)

  ramification_points = Tuple{Int, SubArray{Int, 1, Vector{Int}, Tuple{UnitRange{Int}}, true}, Perm{Int}}[]
  ramification_indices = Int[]

  for i in (1:d)
    for cyc in cycles(gens[i])
      push!(ramification_points, (i, cyc, s_n("("*string(cyc)[2:end-1]*")")))
      push!(ramification_indices, length(cyc) - 1)
    end
  end

  genus = -n + 1 + divexact(sum(ramification_indices;init = zero(Int)), 2)

  all_branches_terminated = false
  ram_pts_nr = length(ramification_points)
  vertices = Set([ram_pts_nr+1])
  edges_on_level = Vector{TretkoffEdge}[]
  terminated_edges = TretkoffEdge[]

  level = 1
  push!(edges_on_level, [])

  for i in (1:ram_pts_nr)
    if 1 in ramification_points[i][2]
      edge = TretkoffEdge(ram_pts_nr + 1, i, level, [ram_pts_nr + 1, i])
      push!(vertices, i)
      push!(edges_on_level[level], edge)
    end
  end
  while !all_branches_terminated
    level += 1
    push!(edges_on_level, [])

    s = 0

    for edge in edges_on_level[level - 1]
      if !is_terminated(edge)
        start_perm = ramification_points[end_point(edge)][3]
        perm = start_perm
        start_sheet = start_point(edge) - ram_pts_nr
        while !is_one(perm)
          new_sheet = perm[start_sheet] + ram_pts_nr
          if !(new_sheet in branch(edge))
            new_edge = TretkoffEdge(end_point(edge), new_sheet, level, vcat(branch(edge), new_sheet))
            s+=1
            set_position(new_edge, s)
            push!(edges_on_level[level], new_edge)
          end
          perm *= start_perm
        end
      end
    end

    sorted_edges = sort(edges_on_level[level], lt = (a,b) -> start_point(a) < start_point(b))
    for edge in sorted_edges
      if end_point(edge) in vertices
        terminate(edge)
        push!(terminated_edges, edge)
      else
        push!(vertices, end_point(edge))
      end
    end

    level += 1
    push!(edges_on_level, [])

    s = 0

    for edge in edges_on_level[level - 1]
      if !is_terminated(edge)
        l = end_point(edge) - ram_pts_nr
        k = mod(start_point(edge), ram_pts_nr) + 1

        for i in (1:ram_pts_nr)
          if (l in ramification_points[k][2]) && !(k in branch(edge))
            new_edge = TretkoffEdge(end_point(edge), k, level, vcat(branch(edge), k))
            s+=1
            set_position(new_edge, s)
            push!(edges_on_level[level], new_edge)
          end
          k = mod(k, ram_pts_nr) + 1
        end
      end
    end

    sorted_edges = sort(edges_on_level[level], lt = (a,b) -> end_point(a) < end_point(b))
    for edge in sorted_edges
      if end_point(edge) in vertices
        terminate(edge)
        push!(terminated_edges, edge)
      else
        push!(vertices, end_point(edge))
      end
    end

    all_branches_terminated = true
    for edge in edges_on_level[level]
      if !is_terminated(edge)
        all_branches_terminated = false
      end
    end

  end

  terminated_edges_nr = (4*genus + 2*n - 2)
  PQ_size = divexact(terminated_edges_nr, 2)
  @req length(terminated_edges) == terminated_edges_nr "The number of terminated edges is wrong. There is a bug in the code."

  function compare_branches(e1::TretkoffEdge, e2::TretkoffEdge)
    l1 = edge_level(e1)
    l2 = edge_level(e2)
    if l1 == l2
      return get_position(e1) < get_position(e2)
    elseif l1 < l2

      e_temp = TretkoffEdge(branch(e2)[l1], branch(e2)[l1 + 1])
      i = findfirst(is_equal(e_temp), edges_on_level[l1])
      return compare_branches(e1, edges_on_level[l1][i])
    else
      return !compare_branches(e2, e1)
    end
  end

  sort!(terminated_edges, lt = compare_branches)

  reverse!(terminated_edges)

  P = TretkoffEdge[]
  QQ = TretkoffEdge[]
  Q = Vector{TretkoffEdge}(undef, PQ_size)
  l = 1

  for k in (1:terminated_edges_nr)
    edge = terminated_edges[k]
    set_position(edge, k)
    if PQ(edge)
      push!(P, edge)
      set_label(edge, l)
      l +=1
    else
      push!(QQ,edge)
    end
  end

  for edge in QQ
    l = findfirst(is_equal(reverse(edge)), P)
    set_label(edge, l)
    Q[l] = edge
  end

  cycles_list = Vector{Int}[]

  for i in (1:PQ_size)
    cycle = vcat(branch(P[i]), reverse(branch(Q[i])[1:end-2]))
    k = 1
    while k <= length(cycle) - 1
      cycle[k] -= ram_pts_nr
      cycle[k+1] = ramification_points[cycle[k+1]][1]
      k +=2
    end

    cycle[k] -= ram_pts_nr
    push!(cycles_list, cycle)
  end


  A = zeros(Int, PQ_size, PQ_size)
  for i in (1:PQ_size)
    j = mod(get_position(P[i]), terminated_edges_nr) + 1
    while true
      next_edge = terminated_edges[j]
      if PQ(next_edge)
        A[get_label(next_edge), i] +=1
      else
        if get_label(next_edge) == i
          break
        else
          A[get_label(next_edge), i] -=1
        end
      end
      j = mod(j, terminated_edges_nr) + 1
    end
  end

  @req rank(A) == 2*genus "Computed matrix has the wrong rank. There is a bug in the code."
  K = matrix(ZZ, A)

  RS.homology_basis = cycles_list, K, symplectic_reduction(K)
  return RS.homology_basis
end

# Given an input K this computes S as mentioned in the homology_basis function
# i,e. the output is a symplectic matrix S that ensure that S K S^T is equal to
# a matrix where the upper left block consists of the normalized polarization
# and the rest consists of zeros.
# [0  I 0 ... 0]
# [-I 0 0 ... 0]
# [|  | | ... 0]
# [0  0 0 ... 0]
function symplectic_reduction(K::ZZMatrix)

  @req is_zero(K + transpose(K)) "Matrix needs to be skew-symmetric"
  @req nrows(K) == ncols(K) "Matrix needs to be square"

  n = nrows(K)

  function find_one_above_pivot(K::ZZMatrix, pivot::Int)
    for i in (pivot:n)
      for j in (pivot:n)
        if K[i, j] == 1
          return [i, j]
        end
      end
    end
    return [0, 0]
  end

  A = deepcopy(K)
  B = one(parent(K))

  ind1 = Vector{ZZRingElem}[]
  ind2 = ZZRingElem[]
  pivot = 1

  while pivot <= n
    next = find_one_above_pivot(A, pivot)
    if next == [0,0]
      push!(ind2, pivot)
      pivot +=1
      continue
    end
    move_to_positive_pivot(next[2], next[1], pivot, A, B)
    zeros_only = true
    pivot_plus = pivot + 1
    for j in (pivot + 2:n)
      v = -A[pivot, j]
      if v != 0
        #The version with ! gave different results for some reason.

        add_row!(A, v, pivot_plus, j)
        add_column!(A,v, pivot_plus, j)
        add_row!(B, v, pivot_plus, j)

        zeros_only = false
      end
      v = A[pivot_plus, j]
      if v != 0
        add_row!(A, v, pivot, j)
        add_column!(A, v, pivot, j)
        add_row!(B, v, pivot, j)
        zeros_only = false
      end
    end
    if zeros_only
      push!(ind1, [A[pivot_plus, pivot], pivot])
      pivot += 2
    end
  end
  sort!(ind1)
  reverse!(ind1)
  new_rows_ind = vcat([i[2] for i in ind1], [i[2] + 1 for i in ind1], ind2)
  return matrix(ZZ, vcat([B[Int(i), 1:n] for i in new_rows_ind]))
end

function move_to_positive_pivot(i::Int, j::Int, pivot::Int, A::ZZMatrix, B::ZZMatrix)
  pivot_plus = pivot + 1
  v = A[i, j]
  is_pivot = false
  if [i,j] == [pivot_plus, pivot] && A[pivot_plus, pivot] != v
    is_pivot = true
    swap_rows!(B, pivot, pivot_plus)
    swap_rows!(A, pivot, pivot_plus)
    swap_cols!(A, pivot, pivot_plus)
  elseif [i,j] == [pivot, pivot_plus]
    swap_rows!(B, pivot, pivot_plus)
    swap_rows!(A, pivot, pivot_plus)
    swap_cols!(A, pivot, pivot_plus)
  elseif j != pivot && j != (pivot_plus) && i != pivot && i != (pivot_plus)
    swap_rows!(B, pivot, j)
    swap_rows!(B, pivot_plus, i)
    swap_rows!(A, pivot, j)
    swap_rows!(A, pivot_plus, i)
    swap_cols!(A, pivot, j)
    swap_cols!(A, pivot_plus, i)
  elseif j == pivot
    swap_rows!(B, pivot_plus, i)
    swap_rows!(A, pivot_plus, i)
    swap_cols!(A, pivot_plus, i)
  elseif j == pivot_plus
    swap_rows!(B, pivot, i)
    swap_rows!(A, pivot, i)
    swap_cols!(A, pivot, i)
  elseif i == pivot
    swap_rows!(B, pivot_plus, j)
    swap_rows!(A, pivot_plus, j)
    swap_cols!(A, pivot_plus, j)
  elseif i == pivot_plus
    swap_rows!(B, pivot, j)
    swap_rows!(A, pivot, j)
    swap_cols!(A, pivot, j)
  end
  if A[pivot_plus, pivot] != v && !is_pivot
    swap_rows!(B, pivot, pivot_plus)
    swap_rows!(A, pivot, pivot_plus)
    swap_cols!(A, pivot, pivot_plus)
  end
end

