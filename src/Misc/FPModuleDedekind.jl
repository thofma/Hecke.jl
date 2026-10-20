# A direct sum of fractional ideals modulo the relations in a pseudo-matrix.
# Each relation row comes with a coefficient ideal, and its ideal multiples
# must lie in the direct sum of the numerator ideals. The base ring must be
# a maximal number-field or function-field order.
#
# We copy the matrix and ideal vectors, but share the ideals themselves. Don't
# change the presentation afterwards: reduction uses a cached pseudo-HNF.
# Element coordinates lie in the numerator ideals and represent their classes.
@attributes mutable struct FPModuleDedekind{
    T <: RingElem, S <: FieldElem, RingT <: Ring, FieldT <: Field, IdealT
  } <: AbstractAlgebra.Module{T}
  ring::RingT
  fraction_field::FieldT
  numerator_ideals::Vector{IdealT}
  relations::PMat{S, IdealT}
  pivot_columns::Vector{Int} # Zero marks a zero row of the relation pseudo-HNF.

  function FPModuleDedekind(R::Ring, A::AbstractVector, P::PMat; check::Bool = true)
    K = field(R)
    I = fractional_ideal_type(R)
    @req length(A) == ncols(P) "Wrong number of numerator ideals"
    @req length(coefficient_ideals(P)) == nrows(P) "Wrong number of relation ideals"
    @req all(a -> order(a) === R, A) "Numerator ideals must belong to the base ring"
    @req all(b -> order(b) === R, coefficient_ideals(P)) "Relation ideals must belong to the base ring"
    a = I[fractional_ideal(x) for x in A]
    b = I[fractional_ideal(x) for x in coefficient_ideals(P)]
    @req all(x -> !iszero(x), a) "Numerator ideals must be nonzero"
    @req all(x -> !iszero(x), b) "Relation ideals must be nonzero"
    C = deepcopy(change_base_ring(K, matrix(P)))
    if check
      @req is_maximal(R) "The base ring must be a maximal order"
      for j in 1:nrows(C), i in 1:ncols(C)
        iszero(C[j, i]) && continue
        @req is_integral((C[j, i]*b[j])//a[i]) "Relations must belong to the numerator module"
      end
    end
    M = new{elem_type(R), elem_type(K), typeof(R), typeof(K), I}(
      R, K, a, pseudo_matrix(R, C, b), Int[])
    H = matrix(_fp_module_relations_hnf(M))
    M.pivot_columns = Int[something(findlast(j -> !iszero(H[i, j]), 1:ncols(H)), 0) for i in 1:nrows(H)]
    return M
  end
end

mutable struct FPModuleDedekindElem{
    T <: RingElem, S <: FieldElem, ModuleT <: FPModuleDedekind{T, S}
  } <: AbstractAlgebra.ModuleElem{T}
  parent::ModuleT
  representative::Vector{S}
  is_reduced::Bool

  function FPModuleDedekindElem(M::FPModuleDedekind{T, S}, v::Vector{S},
                               reduced::Bool = false) where {T, S}
    return new{T, S, typeof(M)}(M, v, reduced)
  end
end

function FPModuleDedekind(R::Ring, A::AbstractVector, C::MatElem,
                         B::AbstractVector; check::Bool = true)
  @req length(B) == nrows(C) "Wrong number of relation ideals"
  K = field(R)
  return FPModuleDedekind(R, A, pseudo_matrix(R, change_base_ring(K, C), collect(B)); check)
end

function FPModuleDedekind(R::Ring, P::PMat; check::Bool = true)
  A = [fractional_ideal(ideal(R, one(R))) for _ in 1:ncols(P)]
  return FPModuleDedekind(R, A, P; check)
end

base_ring(M::FPModuleDedekind) = M.ring
ring(M::FPModuleDedekind) = M.ring
overring(M::FPModuleDedekind) = M.fraction_field
base_ring_type(::Type{FPModuleDedekind{T, S, R, K, I}}) where {T, S, R, K, I} = R
parent(x::FPModuleDedekindElem) = x.parent
parent_type(::Type{FPModuleDedekindElem{T, S, M}}) where {T, S, M} = M
elem_type(::Type{M}) where {T, S, M <: FPModuleDedekind{T, S}} = FPModuleDedekindElem{T, S, M}
elem_type(M::FPModuleDedekind) = elem_type(typeof(M))

coefficient_ideals(M::FPModuleDedekind; copy::Bool = true) = copy ? Base.copy(M.numerator_ideals) : M.numerator_ideals

function relations(M::FPModuleDedekind; copy::Bool = true)
  P = M.relations
  return copy ? pseudo_matrix(base_ring(M), deepcopy(matrix(P)), Base.copy(coefficient_ideals(P))) : P
end

@attr Int rank(M::FPModuleDedekind) = length(M.numerator_ideals) - rank(matrix(M.relations))

function show(io::IO, M::FPModuleDedekind)
  io = pretty(io)
  print(io, "Finitely presented module over ", Lowercase(), base_ring(M),
        " with ", length(M.numerator_ideals), " pseudo-generators and ",
        nrows(M.relations), " pseudo-relations")
end

@attr PMat{S, I} function _fp_module_relations_hnf(M::FPModuleDedekind{T, S, R, K, I}) where {T, S, R, K, I}
  P = M.relations
  if iszero(nrows(P)) || iszero(ncols(P)) || iszero(matrix(P))
    return P
  end
  return pseudo_hnf(P, :lowerleft)
end

function _fp_module_reduce!(x::FPModuleDedekindElem)
  x.is_reduced && return x
  M = parent(x)
  H = _fp_module_relations_hnf(M)
  A = matrix(H)
  v = x.representative
  for i in nrows(A):-1:1
    p = M.pivot_columns[i]
    iszero(p) && continue
    c = v[p]//A[i, p]
    d = c - mod(c, coefficient_ideals(H)[i])
    for j in 1:p
      v[j] = v[j] - d*A[i, j]
    end
  end
  x.is_reduced = true
  return x
end

function (M::FPModuleDedekind{T, S})(v::AbstractVector; check::Bool = true) where {T, S}
  @req length(v) == length(M.numerator_ideals) "Wrong number of coordinates"
  w = S[overring(M)(c) for c in v]
  if check
    @req all(i -> w[i] in M.numerator_ideals[i], eachindex(w)) "Coordinates must belong to the numerator ideals"
  end
  return FPModuleDedekindElem(M, deepcopy(w))
end

function (M::FPModuleDedekind)(v::MatElem; check::Bool = true)
  @req nrows(v) == 1 "The coordinate matrix must have one row"
  return M(v[1, :]; check)
end

function (M::FPModuleDedekind)(x::FPModuleDedekindElem)
  @req parent(x) === M "Element must belong to this module"
  return x
end

(M::FPModuleDedekind)() = zero(M)
zero(M::FPModuleDedekind) = M([zero(overring(M)) for _ in M.numerator_ideals]; check = false)
zero(x::FPModuleDedekindElem) = zero(parent(x))

function coordinates(x::FPModuleDedekindElem; copy::Bool = true)
  _fp_module_reduce!(x)
  return copy ? deepcopy(x.representative) : x.representative
end

function show(io::IO, x::FPModuleDedekindElem)
  print(io, coordinates(x))
end

function Base.deepcopy_internal(x::FPModuleDedekindElem, dict::IdDict)
  haskey(dict, x) && return dict[x]
  y = FPModuleDedekindElem(parent(x), Base.deepcopy_internal(x.representative, dict), x.is_reduced)
  dict[x] = y
  return y
end

Base.copy(x::FPModuleDedekindElem) = deepcopy(x)

function +(x::FPModuleDedekindElem, y::FPModuleDedekindElem)
  @req parent(x) === parent(y) "Elements must have the same parent"
  return FPModuleDedekindElem(parent(x), x.representative + y.representative)
end

-(x::FPModuleDedekindElem) = FPModuleDedekindElem(parent(x), -x.representative)
-(x::FPModuleDedekindElem, y::FPModuleDedekindElem) = x + (-y)

function *(a::Union{Integer, Rational, RingElem}, x::FPModuleDedekindElem)
  M = parent(x)
  K = overring(M)
  c = K(base_ring(M)(K(a)))
  return FPModuleDedekindElem(M, c .* x.representative)
end

*(x::FPModuleDedekindElem, a::Union{Integer, Rational, RingElem}) = a*x

function ==(x::FPModuleDedekindElem, y::FPModuleDedekindElem)
  parent(x) === parent(y) || return false
  return coordinates(x; copy = false) == coordinates(y; copy = false)
end

Base.isequal(x::FPModuleDedekindElem, y::FPModuleDedekindElem) = x == y
Base.iszero(x::FPModuleDedekindElem) = all(iszero, coordinates(x; copy = false))
Base.hash(x::FPModuleDedekindElem, h::UInt) = hash(coordinates(x; copy = false), hash(objectid(parent(x)), h))
