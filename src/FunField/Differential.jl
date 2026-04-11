################################################################################
#
#  Constructors
#
################################################################################

struct FunFldDiff{T <: Generic.FunctionFieldElem}
  f::T
end

@doc raw"""
    differential(f::Generic.FunctionFieldElem) -> Differential

Return the differential df.
"""
function differential(f::T) where {T <: Generic.FunctionFieldElem}
  F = parent(f)
  @req is_separable(defining_polynomial(F)) "Currently assumes separable extension"

  # note that gen(F) currently has inferred type Any, so we add an explicit type annotation
  y = gen(F)::T

  # our polynomials are polynomial in y with coefficients polynomials in x
  # note that denominators are polynomials in x!
  # d(f) = [df/dx - (df/dy * dp/dx) / dp/dy] dx, where p is defining polynomial
  #
  # further: write p = g/h
  # dp/dx = (dg/dx * h - g * dh/dx)/h^2, and dp/dy = dg/dy / h
  # since we are in F, g(x,y) = 0 and we obtain (dp/dx) / (dp/dy) = (dg/dx) / (dg/dy)

  # we want to stay in F, this is simple helper to go from k[x][y] to F
  function toF(p::Generic.Poly{<:PolyRingElem})
    return evaluate(map_coefficients(F, p), y)
  end

  g_poly = numerator(F)
  dg_dx     = toF(map_coefficients(derivative, g_poly))
  dg_dy     = toF(derivative(g_poly))
  df_dx_dy  = dg_dx // dg_dy

  fnum_poly, fden_poly = numerator(f), denominator(f)
  fnum      = toF(fnum_poly)
  dfnum_dx  = toF(map_coefficients(derivative, fnum_poly))
  dfnum_dy  = toF(derivative(fnum_poly))
  # denominator is already in k[x]
  fden      = F(fden_poly)
  dfden_dx  = F(derivative(fden_poly))

  df_dx = (dfnum_dx * fden - fnum * dfden_dx) // fden^2
  df = df_dx - (dfnum_dy // fden) * df_dx_dy

  return FunFldDiff(df)
end

################################################################################
#
#  IO
#
################################################################################

@enable_all_show_via_expressify FunFldDiff

function AbstractAlgebra.expressify(d::FunFldDiff; context = nothing)
  # Expr(:row, a, b) gives a b
  F = function_field(d)
  return Expr(:row, expressify(d.f, context = context),
                    Expr(:call,
                         Symbol("d"),
                         expressify(separating_element(F), context = context)))
end

################################################################################
#
#  Properties
#
################################################################################


function is_zero(df::FunFldDiff)
  return is_zero(df.f)
end

function function_field(df::FunFldDiff)
  return parent(df.f)
end

################################################################################
#
#  Equality
#
################################################################################

function Base.:(==)(df::FunFldDiff, dg::FunFldDiff)
  return function_field(df) === function_field(dg) && df.f == dg.f
end

function Base.hash(df::FunFldDiff, h::UInt)
  h = hash(function_field(df), h)
  h = hash(df.f, h)
  return h
end

################################################################################
#
#  Arithmetic
#
################################################################################

function Base.:+(df::FunFldDiff, dg::FunFldDiff)
  @assert function_field(df) == function_field(dg)
  return FunFldDiff(df.f + dg.f)
end

function Base.:-(df::FunFldDiff, dg::FunFldDiff)
  @assert function_field(df) == function_field(dg)
  return FunFldDiff(df.f - dg.f)
end

function Base.:-(df::FunFldDiff)
  return FunFldDiff(-df.f)
end

function Base.:*(r::Generic.FunctionFieldElem, df::FunFldDiff)
  @assert parent(r) == function_field(df)
  return FunFldDiff(r*df.f)
end

function Base.:*(r::GenOrdElem, df::FunFldDiff)
  F = function_field(df)
  return F(r) * df
end

function Base.:*(r::IntegerUnion, df::FunFldDiff)
  F = function_field(df)
  return F(r) * df
end

Base.:*(df::FunFldDiff, r::Generic.FunctionFieldElem) = r*df
Base.:*(df::FunFldDiff, r::GenOrdElem) = r*df
Base.:*(df::FunFldDiff, r::IntegerUnion) = r*df

@doc raw"""
    //(df::FunFldDiff, dg::FunFldDiff) -> FunctionFieldElem

Return the function r such that r*dg = df.
"""
function Base.://(df::FunFldDiff, dg::FunFldDiff)
  return df.f//dg.f
end

function Base.://(df::FunFldDiff, r::Generic.FunctionFieldElem)
  @assert parent(r) == function_field(df)
  return FunFldDiff(df.f//r)
end

function Base.://(df::FunFldDiff, r::GenOrdElem)
  F = function_field(df)
  return df//F(r)
end

function Base.://(df::FunFldDiff, r::IntegerUnion)
  F = function_field(df)
  return df//(F(r))
end

################################################################################
#
#  Divisor
#
################################################################################

@doc raw"""
    divisor(df::FunFldDiff) -> Divisor

Return the divisor corresponding to the differential form.
"""
function divisor(df::FunFldDiff)
  F = function_field(df)
  x = separating_element(F)
  return divisor(df.f) - 2*pole_divisor(F(x)) + different_divisor(F)
end

@doc raw"""
    valuation(df::FunFldDiff, p::GenOrdIdl) -> Int

Return the valuation of the differential form at a prime.
"""
function valuation(df::FunFldDiff, p::GenOrdIdl)
  return valuation(divisor(df), p)
end

################################################################################
#
#  Basis of differentials
#
################################################################################

@doc raw"""
    basis_of_differentials(F::FunctionField) -> Vector{FunFldDiff}

Return a basis of the first order differential forms of F.
"""
function basis_of_differentials(F::AbstractAlgebra.Generic.FunctionField)
  dx = differential(separating_element(F))
  x = separating_element(F)
  codiff_divisor = divisor(codifferent(finite_maximal_order(F)), codifferent(infinite_maximal_order(F)))
  D = (-divisor(dx.f) + 2*pole_divisor(F(x)) + codiff_divisor)
  J_fin, J_inf = ideals(D)
  F = function_field(D)
  RR = _riemann_roch_space(J_fin, J_inf, F)
  map(t-> FunFldDiff(t), RR)
  #return map(t-> FunFldDiff(t), riemann_roch_space(canonical_divisor(F)))
end
