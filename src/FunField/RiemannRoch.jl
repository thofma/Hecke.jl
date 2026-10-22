################################################################################
#
#  Riemann-Roch computation
#
#  implements Riemann-Roch computation from Hess'
#  "Computing Riemann-Roch Spaces in Algebraic Function Fields and Related Topics"
#
################################################################################
@doc raw"""
    riemann_roch_space(D::Divisor) -> Vector{FunFieldElem}

Return a basis of the Riemann-Roch space L(D).
"""
function riemann_roch_space(D::Divisor)
  I_fin, I_inf = ideals(D)
  return _riemann_roch_space(inv(I_fin), inv(I_inf), function_field(D))
end

# we have two functions: _riemann_roch_space to compute Riemann-Roch space itself
#   and _riemann_roch_dim to compute its dimension
# Their inputs are:
#   J_fin is the inverse of the finite ideal
#   J_inf is the inverse of the infinite ideal
#   F is the ambient function field

# common setup for Riemann-Roch
# B_fin and B_inf are coordinate matrices (basis elements in the power basis)
function _riemann_roch_common_setup(B_fin, B_inf)
  # express B_fin in terms of B_inf
  M = solve(B_inf, B_fin; side = :left)

  # clear denominators
  d = mapreduce(denominator, lcm, M)

  return change_base_ring(parent(d), d*M), degree(d)
end

# computes the basis of the Riemann-Roch space
function _riemann_roch_space(J_fin, J_inf, F)
  x = gen(base_ring(F))
  n = degree(F)

  B_fin = _coordinate_matrix(J_fin)
  B_inf = _coordinate_matrix(J_inf)
  dM, d_deg = _riemann_roch_common_setup(B_fin, B_inf)

  # weak Popov reduction of dM (no denominators)
  T, U = _weak_popov_with_transform!(dM)

  # v_i in Hess paper: rows have v_i coordinates in power basis
  basis_gens = change_base_ring(base_ring(B_fin), U) * B_fin

  RR_basis = elem_type(F)[]
  for i in 1:n
    d_i = maximum(degree(T[i, k]) for k in 1:n)
    g = F(vec(collect(basis_gens[i, :])))
    for _ in 0:(d_deg - d_i)
      push!(RR_basis, g)
      g = x*g # this is x^j * basis_gens[i] for j = 0 .. d_deg - d_i
    end
  end
  return RR_basis
end

# computes the dimension of the Riemann-Roch space
function _riemann_roch_dim(J_fin, J_inf, F)
  n = degree(F)

  dM, d_deg = _riemann_roch_common_setup(_coordinate_matrix(J_fin), _coordinate_matrix(J_inf))

  # we need only weak Popov form itself, without transform
  T = _weak_popov!(dM)

  # same as above, but instead of constructing basis vectors we just count them
  dim = 0
  for i in 1:n
    d_i = maximum(degree(T[i, k]) for k in 1:n)
    dim += max(0, d_deg - d_i + 1)
  end

  return dim
end

@doc raw"""
    dimension(D::Divisor) -> Int

Return the dimension l(D) of the Riemann-Roch space L(D).
"""
function dimension(D::Divisor)
  I_fin, I_inf = ideals(D)
  return _riemann_roch_dim(inv(I_fin), inv(I_inf), function_field(D))
end

@doc raw"""
    index_of_speciality(D::Divisor) -> Int

Return the index of speciality of D, which is the dimension Riemann-Roch space
L(K - D), where K is the canonical divisor of the function field of D.
"""
function index_of_speciality(D::Divisor)
  F = function_field(D)
  @req _is_separable(F) "Currently assumes separable extension"

  return dimension(canonical_divisor(F) - D)
end

################################################################################
#
#  New riemann roch space with context
#
################################################################################

mutable struct RiemannRochCtx
 RR_basis::Vector{Generic.FunctionFieldElem} #K-basis
 basis_gens::Generic.MatSpaceElem #v_i via coordinates in power basis
 dlist::Vector{Int}
 map::Generic.MapWithSection
 D::Divisor
 function RiemannRochCtx(RR_basis, basis_gens, dlist)
    return new(RR_basis, basis_gens, dlist)
  end
end

function Base.show(io::IO, RRCtx::RiemannRochCtx)
  @show_name(io, RRCtx)
  @show_special(io, RRCtx)
  io = pretty(io)
  print(io, "Riemann Roch space of ", Lowercase())
  print(io, RRCtx.D)
  print(io, " over ", Lowercase(), defining_constant_field(function_field(RRCtx.D)))
end

function Base.show(io::IO, ::MIME"text/plain",  RRCtx::RiemannRochCtx)
  @show_name(io, RRCtx)
  @show_special(io, RRCtx)
  io = pretty(io)
  println(io, "Riemann Roch space")
  print(io, Indent(), "of ", Lowercase())
  print(io, RRCtx.D)
  println(io, Dedent())
  println(io, "of dimension ", length(RRCtx.RR_basis))
  println(io, " over ", Lowercase(), defining_constant_field(function_field(RRCtx.D)))
end

function in(a, RRCtx::RiemannRochCtx)
  mu = RRCtx.map
  return mu(preimage(mu, a)) == a
end

#Riemann roch space of D over constant field K with map from K-vectorspace to function field F. 
function riemann_roch_space_with_ctx(D::Divisor)
  I_fin, I_inf = ideals(D)
  return _riemann_roch_space_with_ctx(inv(I_fin), inv(I_inf), function_field(D))
end

function _riemann_roch_space_with_ctx(J_fin, J_inf, F)
  x = gen(base_ring(F))
  n = degree(F)

  B_fin = Hecke._coordinate_matrix(J_fin)
  B_inf = Hecke._coordinate_matrix(J_inf)
  dM, d_deg = Hecke._riemann_roch_common_setup(B_fin, B_inf)

  # weak Popov reduction of dM (no denominators)
  T, U = Hecke.weak_popov_with_transform(dM)

  # v_i in Hess paper
  basis_gens = change_base_ring(base_ring(B_fin), U) * B_fin

  RR_basis = elem_type(F)[]
  dlist = Int[]
  for i in 1:n
    d_i = maximum(degree(T[i, k]) for k in 1:n)
    push!(dlist, d_deg - d_i)
    g = F(vec(collect(basis_gens[i, :])))
    for _ in 0:(d_deg - d_i)
      push!(RR_basis, g)
      g = x*g # this is x^j * basis_gens[i] for j = 0 .. d_deg - d_i
    end
  end

  ctx = RiemannRochCtx(RR_basis, basis_gens, dlist)
  
  #disclog
  Uinv = inv(U) #basis(J_fin) = Uinv * basis_gens
  M = inv(B_fin) #basis(F) = M * basis(J_fin)
  coordinates_in_basis_gens = a -> coordinates(a) * M * Uinv

  K = defining_constant_field(F)
  V = vector_space(K, length(RR_basis))

  #RR space -> K-vectorspace
  function disclog_RR(a, dlist, V)
    y = coordinates_in_basis_gens(a)
    len = length(y)
    v = [coeff(numerator(y[i]), j) for i in 1:len for j in 0:dlist[i]]
    return V(v)
  end

  #K-vectorspace
  function V_to_RR(v, RR_basis)
    z = 0
    len = length(v.v)
    @assert len == length(RR_basis)
    for i in 1:len
      z += v[i]*RR_basis[i]
    end
    return z
  end
  
  ctx.map = map_with_preimage_from_func(v->V_to_RR(v, RR_basis), a -> disclog_RR(a, dlist, V), V, F)
  ctx.D = divisor(inv(J_fin), inv(J_inf)) #TODO: update as soon as new divisor type is included
  return ctx
end