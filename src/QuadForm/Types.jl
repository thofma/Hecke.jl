################################################################################
#
#  Abstract types
#
################################################################################

# abstract spaces
abstract type AbsSpace{S} end

# abstract lattices
abstract type AbsLat{S} end

################################################################################
#
#  Quadratic spaces
#
################################################################################

mutable struct QuadSpace{S, T} <: AbsSpace{S}
  K::S
  gram::T
  @declare_other

  function QuadSpace(K::S, G::T) where {S, T}
    # I also need to check if the gram matrix is Hermitian
    if dense_matrix_type(elem_type(S)) === T
      z = new{S, T}(K, G)
    else
      try
        Gc = change_base_ring(K, G)
        if typeof(Gc) !== dense_matrix_type(elem_type(S))
          throw(error("Cannot convert entries of the matrix to the number field"))
        end
        @assert base_ring(Gc) === K
        z = new{S, dense_matrix_type(elem_type(S))}(K, Gc)
        return z
      catch e
        rethrow(e)
        throw(error("Cannot convert entries of the matrix to the number field"))
      end
    end
  end
end

################################################################################
#
#  Hermitian spaces
#
################################################################################

mutable struct HermSpace{S, T, U, W} <: AbsSpace{S}
  E::S
  K::T
  gram::U
  involution::W
  @declare_other

  function HermSpace(E::S, gram::U) where {S, U}
    # I also need to check if the gram matrix is Hermitian
    if dense_matrix_type(elem_type(S)) === U
      gramc = gram
    else
      try
        gramc = change_base_ring(E, gram)
        if typeof(gramc) !== dense_matrix_type(elem_type(S))
          throw(error("Cannot convert entries of the matrix to the number field"))
        end
      catch e
        throw(error("Cannot convert entries of the matrix to the number field"))
      end
    end

    @assert degree(E) == 2
    A = automorphisms(E)
    a = gen(E)
    if A[1](a) == a
      involution = A[2]
    else
      involution = A[1]
    end

    K = base_field(E)

    z = new{S, typeof(K), dense_matrix_type(elem_type(S)), typeof(involution)}(E, K, gramc, involution)
    return z
  end
end
