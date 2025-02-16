@attributes mutable struct ModAlgAss{S, T, U}
  base_ring::S
  dim::Int
  is_irreducible::Int # 0 not know
                     # 1 true
                     # 2 false
  is_abs_irreducible::Int
  degree_splitting_field::Int
                     # same as above
  algebra::U
  action_of_gens::Vector{T}
  action_of_gens_inverse::Vector{T}
  action_of_basis::Vector{T}
  isfree::Int
  free_rank::Int

  function ModAlgAss{T, U}(algebra::U; action_of_basis::Vector{T} = T[], action_of_gens::Vector{T} = T[]) where {T, U}
    S = typeof(base_ring(algebra))
    z = new{S, T, U}()
    z.isfree = 0
    z.free_rank = -1
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
      z.is_abs_irreducible = 1
      z.degree_splitting_field = 1
    else
      z.is_irreducible = 0
      z.is_abs_irreducible = 0
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
    z.isfree = 0
    z.free_rank = -1
    if z.dim == 1
      z.is_irreducible = 1
      z.is_abs_irreducible = 1
      z.degree_splitting_field = 1
    else
      z.is_irreducible = 0
      z.is_abs_irreducible = 0
      z.degree_splitting_field = 0
    end

    return z
  end
end

struct ModAlgAssElem{P, T}
  parent::P
  coordinates::Vector{T}
end

parent(x::ModAlgAssElem) = x.parent

function (V::ModAlgAss)(x::Vector)
  if parent(x[1]) === V.base_ring
    return ModAlgAssElem(V, x)
  else
    return ModAlgAssElem(V, convert(Vector{elem_type(V.base_ring)}, map(V.base_ring, x)))
  end
end

function Base.show(io::IO, v::ModAlgAssElem)
  io = pretty(io)
  print(io, "[")
  join(io, coordinates(v), ", ")
  print(io, "]")
end

function Base.show(io::IO, ::MIME"text/plain", v::ModAlgAssElem)
  io = pretty(io)
  println(io, "Amodule element with")
  print(io, Indent())
  println(IOContext(io, :compact => true), "parent ", parent(v))
  print(io, "and coordinates [")
  join(io, coordinates(v), ", ")
  print(io, "]")
  print(io, Dedent())
end

zero(V::ModAlgAss) = V([zero(V.base_ring) for i in 1:dim(V)])

coordinates(x::ModAlgAssElem) = x.coordinates

function Base.:(+)(x::ModAlgAssElem, y::ModAlgAssElem)
  return parent(x)(coordinates(x) + coordinates(y))
end

function Base.:(*)(x::ModAlgAssElem, y::AbstractAssociativeAlgebraElem)
  @assert parent(y) === parent(x).algebra
  return parent(x)(coordinates(x) * action(parent(x), y))
end

function Base.:(*)(x::FieldElem, y::ModAlgAssElem)
  return parent(y)(x * coordinates(y))
end

function Base.:(==)(x::ModAlgAssElem{P, T}, y::ModAlgAssElem{P, T}) where {P, T}
  return parent(x) === parent(y) && coordinates(x) == coordinates(y)
end

function Base.hash(x::ModAlgAssElem, h::UInt)
  h = hash(parent(x), h)
  h = hash(coordinates(x), h)
  return h
end

function Base.show(io::IO, ::MIME"text/plain", V::ModAlgAss)
  io = pretty(io)
  println(io, LowercaseOff(), "Amodule of dimension ", V.dim)
  print(io, Indent(), "over ")
  if has_algebra(V)
    print(IOContext(io, :compact => true), Lowercase(), algebra(V))
  else
    print("given by matrix action")
  end
  print(io, Dedent())
end

function Base.show(io::IO, V::ModAlgAss)
  io = pretty(io)
  if is_terse(io)
    print(io, LowercaseOff(), "Amodule of dimension ", dim(V))
  else
    print(io, LowercaseOff(), "Amodule of dimension ", dim(V))
    print(io, Indent())
    if !has_algebra(V)
      print(io, "given by action matrices")
    else
      print(io, "over ")
      print(IOContext(io, :compact => true), Lowercase(), algebra(V))
    end
    print(io, Dedent())
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

@doc raw"""
    coefficient_ring(V::ModAlgAss) -> Field

Returns the coefficient ring of the module.
"""
coefficient_ring(V::ModAlgAss) = V.base_ring


function dim(V::ModAlgAss)
  return V.dim
end

@doc raw"""
    Amodule(A::AbstractAssociativeAlgebra, M::Vector{<:MatElem})

Given an algebra $A$ over a field $K$ and a list of $\dim(A)$ of square
matrices over $K$, construct the $A$-module with `basis(A)[i]` acting
via `M[i]` from the right.
"""
function Amodule(A::AbstractAssociativeAlgebra, M::Vector{<:MatElem})
  @assert length(M) == length(basis(A))
  return ModAlgAss{eltype(M), typeof(A)}(A, action_of_basis = M)
end

@doc raw"""
    Amodule(M::Vector{<:MatElem})

Given a list `M` of square matrices over a field $K$, construct the module
for the free algebra with the generators acting via `M[i]` from the right.

Note that the free algebra will not be constructed and the resulting
object has no associated algebra.
"""
function Amodule(M::Vector{<:MatElem})
  return ModAlgAss{eltype(M)}(action_of_gens = M)
end

################################################################################
#
#  Predicates
#
################################################################################

@doc raw"""
    has_algebra(V::ModAlgAss) -> Bool

Returns whether the module was defined explicitly using an algebra.
"""
has_algebra(V::ModAlgAss) = isdefined(V, :algebra)

@doc raw"""
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

function action_of_gens(V::ModAlgAss{<: Any, <: Any, <: GroupAlgebra})
  if !isdefined(V, :action_of_gens)
    A = algebra(V)
    V.action_of_gens = [action(V, g) for g in gens(A)]
  end
  return V.action_of_gens
end

function action_of_gens(V::ModAlgAss)
  return V.action_of_gens
end

function action_of_gens_inverse(V::ModAlgAss)
  if isdefined(V, :action_of_gens_inverse)
    return V.action_of_gens_inverse
  else
    V.action_of_gens_inverse = inv.(V.action_of_gens)
    return V.action_of_gens_inverse
  end
end

@doc raw"""
    action(V::ModAlgAss{_, MatElem, _}, x::AbstractAssociativeAlgebraElem)

Given a $A$-module $V$ for an algebra $A$ with action given by matrices, and an
element $x$ of $A$, returns the action of $x$.
"""
function action(V::ModAlgAss{<:Any, <: MatElem, <:Any}, x::AbstractAssociativeAlgebraElem)
  @req parent(x) == algebra(V) "Algebra of module must be parent of element"
  cx = coefficients(x)
  M = cx[1] * action_of_basis(V, 1)
  for i in 2:length(cx)
    N = cx[i] * action_of_basis(V, i)
    M = add!(M, M, N)
  end
  return M
end

function action_of_word(V::ModAlgAss{<: Any, <: MatElem}, w::Vector{Int})
  gens = action_of_gens(V)
  gens_inv = action_of_gens_inverse(V)
  v = V.action_of_gens[1]^0
  for k in w
    if k > 0
      v = v * gens[k]
    else
      v = v * gens_inv[-k]
    end
  end
  return v
end

@doc raw"""
    action(V::ModAlgAss) -> Vector

Given a module $V$, returns the action on $V$. If no algebra is defined,
these will be generators, otherwise these will be the action of `basis(A)`.
"""
function action(V::ModAlgAss)
  if !has_algebra(V)
    return V.action_of_gens
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

  # Now V has an algebra
  @assert algebra(V) === algebra(W)

  A = algebra(V)

  if A isa GroupAlgebra
    return (action_of_gens(V), action_of_gens(W))
  end

  if !isdefined(V, :action_of_gens) || !isdefined(W, :action_of_gens)
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

# TODO: make this check absolute irreducibility before
function is_irreducible_known(M::ModAlgAss)
  return M.is_irreducible != 0
end

function is_irreducible(M::ModAlgAss)
  if M.is_irreducible != 0
    return M.is_irreducible == 1
  else
    if !(coefficient_ring(M) isa FinField)
      error("NotImplemented: Coefficient ring must be a finite field")
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

function is_absolutely_irreducible_known(V::ModAlgAss)
  return V.is_abs_irreducible != 0
end

function is_absolutely_irreducible(V::ModAlgAss)
  if V.is_abs_irreducible != 0
    return V.is_abs_irreducible == 1
  end
  throw(NotImplemented())
end

#function composition_factors(V::ModAlgAss{<:FinField})
#  act = V.action_of_gens
#
#  cf = stub_composition_factors(act)
#
#  return [Amodule(c) for c in cf]
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

################################################################################
#
#  Homomorphism spaces
#
################################################################################

function trivial_module(A::AbstractAssociativeAlgebra)
  K = base_ring(A)
  B = basis(A)
  action_of_basis = [identity_matrix(K, 1) for b in B]
  V = Amodule(A, action_of_basis)
  return V
end

function regular_module(A::AbstractAssociativeAlgebra)
  K = base_ring(A)
  n = dim(A)
  B = basis(A)
  action_of_basis = [representation_matrix(b, :right) for b in B]
  M = Amodule(A, action_of_basis)
  M.isfree = 1
  M.free_rank = 1
  return M
end

function regular_module(A::AbstractAssociativeAlgebra, p)#::AbsAlgAssMor)
  K = base_ring(A)
  action_of_basis = [representation_matrix(p(b), :right) for b in basis(A)]
  M = Amodule(A, action_of_basis)
  # We do some more, because we know the endomorphism algbera
  B, f = endomorphism_algebra(M)
  C = codomain(p)
  @assert dim(B) == dim(C)
  imgs = elem_type(B)[]
  for c in basis(C)
    d = preimage(f, hom(M, M, representation_matrix(c, :left)))
    push!(imgs, d)
  end
  # This is a bit of a hack
  Cop, CtoCop = opposite_algebra(C)
  h = hom(Cop, B, basis_matrix(imgs))
  for c in basis(Cop)
    for cc in basis(Cop)
      @assert h(c * cc) == h(c) * h(cc)
    end
  end
  _assert_has_refined_wedderburn_decomposition(A)
  _transport_refined_wedderburn_decomposition_forward(CtoCop, is_anti = true)
  _transport_refined_wedderburn_decomposition_forward(p)
  _transport_refined_wedderburn_decomposition_forward(h)
  return M
end

function free_module(A::AbstractAssociativeAlgebra, r::Int)
  K = base_ring(A)
  n = dim(A)
  B = basis(A)
  action_of_basis = Vector{dense_matrix_type(K)}()
  for b in B
    rm = representation_matrix(b, :right)
    push!(action_of_basis, block_diagonal_matrix([rm for i in 1:r]))
  end
  M = Amodule(A, action_of_basis)
  M.isfree = 1
  M.free_rank = r
  return M
end

function _element_of_standard_free_module(V::ModAlgAss, v::Vector)
  #@assert V.isfree == 1 && V.free_rank == length(v)
  @assert all(x -> parent(x) === algebra(V), v)
  return V(reduce(vcat, coefficients.(v)))
end

# submodule of A^k generated by B
function Amodule(A::AbstractAssociativeAlgebra, B::Vector{<:Vector}; is_basis::Bool = true)
  @assert is_basis
  # I first need to flatten those vectors to elements of K^n
  K = base_ring(A)
  BB = Vector{Vector{elem_type(K)}}()
  for b in B
    push!(BB, reduce(vcat, (coefficients(x) for x in b)))
  end
  bmat = matrix(BB)
  basA = basis(A)
  BBB = Vector{Vector{elem_type(K)}}()
  action_matrices = dense_matrix_type(elem_type(K))[]
  for b in basA
    empty!(BBB)
    for bb in B
      push!(BBB, reduce(vcat, [coefficients(b * bb[i]) for i in 1:length(bb)]))
    end
    fl, X = can_solve_with_solution(bmat, matrix(BBB), side = :left)
    @assert fl
    push!(action_matrices, transpose(X))
  end
  return Amodule(A, action_matrices)
end

################################################################################
#
#  Galois module
#
################################################################################

# Type to represent a Q[Gal(K)]-linear map K -> V
mutable struct NfToModAlgAssMor{S, T, U} <: Map{AbsSimpleNumField, ModAlgAss{S, T, U}, HeckeMap, NfToModAlgAssMor}
  K::AbsSimpleNumField
  mG::GrpGenToNfMorSet{_AbsSimpleNumFieldAut, AbsSimpleNumField}
  V::ModAlgAss{S, T, U}
  M::QQMatrix
  Minv::QQMatrix

  function NfToModAlgAssMor{S, T, U}() where {S, T, U}
    return new{S, T, U}()
  end
end

function Base.show(io::IO, M::NfToModAlgAssMor)
   if is_terse(io)
      print(io, "Galois module map")
   else
      io = pretty(io)
      print(io, "Galois module map: ")
      print(terse(io), Lowercase(), domain(M), " -> ")
      print(terse(io), Lowercase(), codomain(M))
   end
end

function (f::NfToModAlgAssMor)(O::Union{AbsNumFieldOrder, AbsNumFieldOrderIdeal})
  V = codomain(f)
  B = basis(O)
  A = algebra(V)
  G = group(A)
  ZG = Order(A, collect(G))
  return lattice(V, ZG, [f(elem_in_nf(b)) for b in B])
end

automorphism_map(f::NfToModAlgAssMor) = f.mG

function galois_module(K::AbsSimpleNumField, aut::Map = automorphism_group(K)[2]; normal_basis_generator = normal_basis(K))
  G = domain(aut)
  A = QQ[G]
  return _galois_module(K, A, aut, normal_basis_generator = normal_basis_generator)
end

function _galois_module(K::AbsSimpleNumField, A, aut::Map = automorphism_group(K)[2]; normal_basis_generator = normal_basis(K))
  G = domain(aut)
  alpha = normal_basis_generator

  basis_alpha = Vector{elem_type(K)}(undef, dim(A))
  for (i, g) in enumerate(G)
    f = aut(g)
    basis_alpha[A.group_to_base[g]] = f(alpha)
  end

  M = zero_matrix(base_field(K), degree(K), degree(K))
  for i = 1:degree(K)
    a = basis_alpha[i]
    for j = 1:degree(K)
      M[i, j] = coeff(a, j - 1)
    end
  end

  invM = inv(M)

  z = NfToModAlgAssMor{QQField, QQMatrix, typeof(A)}()
  V = regular_module(A)
  z.K = K
  z.mG = aut
  z.V = V
  z.M = M
  z.Minv = invM
  V.isfree = 1
  V.free_rank = 1

  return V, z
end

domain(f::NfToModAlgAssMor) = f.K

codomain(f::NfToModAlgAssMor) = f.V

function image(f::NfToModAlgAssMor, x::AbsSimpleNumFieldElem)
  K = domain(f)
  @assert parent(x) === K
  V = codomain(f)

  t = zero_matrix(base_field(K), 1, degree(K))
  for i = 1:degree(K)
    t[1, i] = coeff(x, i - 1)
  end
  y = t*f.Minv
  return V([ y[1, i] for i = 1:degree(K) ])
end

function preimage(f::NfToModAlgAssMor, x::ModAlgAssElem)
  K = domain(f)
  y = coordinates(x)*f.M
  return K(y)
end

################################################################################
#
#  Isomorphism
#
################################################################################

# Implement V \cong W <=> tr(V) == tr(W) if V and W are semisimple
# (e.g. if A is semisimple), Lam, "Introduction to noncommutative algebra",
#
#function is_isomorphic(V::ModAlgAss, W::ModAlgAss)
#  @req algebra(V) === algebra(W) "Modules must be defined over same algebra"
#  A = algebra(V)
#end

function is_isomorphic_with_isomorphism(V::ModAlgAss, W::ModAlgAss)
  B = _basis_of_hom(W, V)
  if length(B) == 0
    return false, hom(V, W, basis(W))
  end
  l = length(B)
  for i in 1:50
    c = sum(c * b for (c, b) in zip(rand(-1:1, l), B))
    if !iszero(det(c))
      return true, hom(V, W, c)
    end
  end
  return false, hom(V, W, basis(W))
end

function is_free(V::ModAlgAss)
  dV = dim(V)
  A = algebra(V)
  dA = dim(A)
  if !is_divisible_by(dV, dA)
    return false
  end
  d = div(dV, dA)
  fl = is_isomorphic_with_isomorphism(V, free_module(algebra(V), d))[1]
  if !fl
    return false
  end
  V.isfree = 1
  V.free_rank = d
  return true
end

################################################################################
#
#  Twists
#
################################################################################

function _twists(V::ModAlgAss)
  A = algebra(V)
  @req A isa GroupAlgebra "Algebra must be a group algebra"
  G = group(A)
  A = outer_automorphisms(G)
  res = typeof(V)[]
  for a in A
    push!(res, _twist(V, hom(a)))
  end
  return res
end

function _twist(V::ModAlgAss, a::Map)
  A = algebra(V)
  @req A isa GroupAlgebra "Algebra must be a group algebra"
  G = group(A)
  @req domain(a) == G == codomain(a) "Map must be an endomorphism of the group"
  B = basis(A)
  rep2 = QQMatrix[]
  for i in 1:length(B)
    g = A.base_to_group[i]
    @assert A(g) == B[i]
    push!(rep2, action(V, A(a(g))))
  end
  W = Amodule(A, rep2)
end

function _change_group(V::ModAlgAss, a::Map; algebra = nothing)
  A = Hecke.algebra(V)
  @req A isa GroupAlgebra "Algebra must be a group algebra"
  G = group(A)
  @req G == codomain(a) "Map must be an endomorphism of the group"
  @assert algebra !== nothing
  H = domain(a)
  QH = group_algebra(base_field(A), H)
  B = basis(A)
  rep2 = QQMatrix[]
  for i in 1:length(B)
    g = A.base_to_group[i]
    push!(rep2, action(V, A(a(g))))
  end
  W = Amodule(QH, rep2)
  return W
end
