add_assert_scope(:ModLattice)

@attributes mutable struct ModAlgAss{S, T, U}
  base_ring::S
  dim::Int
  is_irreducible::Int # 0 not know
                     # 1 true
                     # 2 false
  degree_splitting_field::Int
                     # same as above
  algebra::U
  action_of_gens::Vector{T}
  action_of_basis::Vector{T}

  function ModAlgAss{T, U}(algebra::U; action_of_basis::Vector{T} = T[], action_of_gens::Vector{T} = T[]) where {T, U}
    S = typeof(base_ring(algebra))
    z = new{S, T, U}()
    if length(action_of_basis) > 0
      z.action_of_basis = action_of_basis
      z.dim = nrows(action_of_basis[1])
    end
    if length(action_of_gens) > 0
      z.action_of_gens = action_of_gens
      if !isdefined(z.dim)
        z.dim = nrows(action_of_gens[1])
      end
    end
    z.algebra = algebra
    z.base_ring = base_ring(algebra)
    if z.dim == 1
      z.is_irreducible = 1
      z.degree_splitting_field = 1
    else
      z.is_irreducible = 0
      z.degree_splitting_field = 0
    end
    return z
  end

  function ModAlgAss{T}(;action_of_gens::Vector{T} = T[]) where {T}
    K = base_ring(action_of_gens[1])
    U = matrix_algebra_type(K)
    S = typeof(K)
    z = new{S, T, U}()
    z.action_of_gens = action_of_gens
    z.base_ring = base_ring(action_of_gens[1])
    z.dim = nrows(action_of_gens[1])
    if z.dim == 1
      z.is_irreducible = 1
      z.degree_splitting_field = 1
    else
      z.is_irreducible = 0
      z.degree_splitting_field = 0
    end

    return z
  end
end

function Base.show(io::IO, V::ModAlgAss)
  print(io, "Module over field of dimension ", V.dim)
  if has_algebra(V)
    print(io, " (with algebra defined))")
  end
end

################################################################################
#
#  Field access
#
################################################################################

function algebra(V::ModAlgAss)
  if !isdefined(V, :algebra)
    error("Algebra of module not defined")
  else
    return V.algebra
  end
end

Markdown.doc"""
    coefficient_ring(V::ModAlgAss) -> Field

Returns the coefficient ring of the module.
"""
coefficient_ring(V::ModAlgAss) = V.base_ring


function dim(V::ModAlgAss)
  return V.dim
end

@doc Markdown.doc"""
    Module(A::AbsAlgAss, M::Vector{<:MatElem})

Given an algebra $A$ over a field $K$ and a list of $\dim(A)$ of square
matrices over $K$, construct the $A$-module with `basis(A)[i]` acting
via `M[i]` from the right.
"""
function Module(A::AbsAlgAss, M::Vector{<:MatElem})
  @assert length(M) == length(basis(A))
  return ModAlgAss{eltype(M), typeof(A)}(A, action_of_basis = M)
end

@doc Markdown.doc"""
    Module(M::Vector{<:MatElem})

Given a list `M` of square matrices over a field $K$, construct the module
for the free algebra with the generators acting via `M[i]` from the right.

Note that the free algebra will not be constructed and the resulting
object has no assocated algebra.
"""
function Module(M::Vector{<:MatElem})
  return ModAlgAss{eltype(M)}(action_of_gens = M)
end

################################################################################
#
#  Predicates
#
################################################################################

@doc Markdown.doc"""
    has_algebra(V::ModAlgAss) -> Bool

Returns whether the module was defined explicitely using an algebra.
"""
has_algebra(V::ModAlgAss) = isdefined(V, :algebra)

@doc Markdown.doc"""
    has_matrix_action(V::ModAlgAss) -> Bool

Returns whether the action on the module is given by matrices.
"""
function has_matrix_action(V::ModAlgAss{S, T, U}) where {S, T, U}
  if T <: MatElem
    return true
  else
    return false
  end
end

################################################################################
#
#  Action
#
################################################################################

function action_of_basis(V::ModAlgAss)
  if isdefined(V, :action_of_basis)
    return V.action_of_basis
  else
    throw(NotImplemented())
  end
end

function action_of_basis(V::ModAlgAss, i::Int)
  if isdefined(V, :action_of_basis)
    return V.action_of_basis[i]
  else
    throw(NotImplemented())
  end
end

@doc Markdown.doc"""
    action(V::ModAlgAss{_, MatElem, _}, x::AbsAlgAssElem)

Given a $A$-module $V$ for an algebra $A$ with action given by matrices, and an
element $x$ of $A$, returns the action of $x$.
"""
function action(V::ModAlgAss{<:Any, <: MatElem, <:Any}, x::AbsAlgAssElem)
  @req parent(x) == algebra(V) "Algebra of module must be parent of element"
  cx = coefficients(x)
  M = cx[1] * action_of_basis(V, 1)
  for i in 2:length(cx)
    N = cx[i] * action_of_basis(V, i)
    M = add!(M, M, N)
  end
  return M
end

@doc Markdown.doc"""
    action(V::ModAlgAss) -> Vector

Given a module $V$, returns the action on $V$. If no algebra is defined,
these will be generators, otherwise these will be the action of `basis(A)`.
"""
function action(V::ModAlgAss)
  if !has_algebra(V)
    return V.action_of_Gens
  else
    return action_of_basis(V)
  end
end

function action_of_order_basis(V::ModAlgAss{S, T, U}, O::AlgAssAbsOrd) where {S, T, U}
  s = get_attribute(V, :order_action) 
  if s === nothing
    t = Dict{typeof(O), Vector{T}}()
    set_attribute!(V, :order_action => t)
  else
    t = s::Dict{typeof(O), Vector{T}}
    if haskey(t, O)
      return t[O]::Vector{T}
    end
  end
  z = T[action(V, elem_in_algebra(y)) for y in basis(O, copy = false)]
  t[O] = z
  return z
end

# Internal function to give the action in a consistent way
# If there is no algebra, just returns the action
# If there is an algebra, the minimal number of generators
# is returned.
function consistent_action(V::T, W::T) where {T <: ModAlgAss}
  if !has_algebra(V)
    @assert !has_algebra(W)
  else
    @assert has_algebra(W)
    @assert algebra(V) === algebra(W)
  end

  if !has_algebra(V)
    @assert length(V.action_of_gens) == length(W.action_of_gens)
    return (V.action_of_gens, W.action_of_gens)
  end

  if !isdefined(V.action_of_gens) || !isdefined(W.action_of_gens)
    return (V.action_of_basis, W.action_of_basis)
  else
    return (V.action_of_gens, W.action_of_gens)
  end
end

################################################################################
#
#  Irreducibility
#
################################################################################

function is_irreducible_known(M::ModAlgAss)
  return M.is_irreducible != 0
end

function is_irreducible(M::ModAlgAss)
  if M.is_irreducible != 0
    return M.is_irreducible == 1
  else
    if !(coefficient_ring(M) isa FinField)
      error("Coefficient ring must be a finite field")
    end
    fl, N = meataxe(M)
    if fl
      M.is_irreducible = 1
    else
      M.is_irreducible = 2
    end
    return fl
  end
end

#function composition_factors(V::ModAlgAss{<:FinField})
#  act = V.action_of_gens
#
#  cf = stub_composition_factors(act)
#
#  return [Module(c) for c in cf]
#end

function basis_of_hom(V, W)
  x, y = consistent_action(V, W)
  return stub_basis_hom_space(x, y)
end

################################################################################
#
#  Function stubs, filled in by Oscar
#
################################################################################

stub_composition_factors(a) = error("Load Oscar (or GAP) and try again")

stub_basis_hom_space(a, b) = error("Load Oscar (or GAP) and try again")

