mutable struct AlgAss{T} <: Ring
  base_ring::Ring
  mult_table::Array{T, 3} # e_i*e_j = sum_k mult_table[i, j, k]*e_k
  one::Array{T, 1}

  function AlgAss{T}(R::Ring) where {T}
    A = new{T}()
    A.base_ring = R
    return A
  end

  function AlgAss{T}(R::Ring, mult_table::Array{T, 3}, one::Array{T, 1}) where {T}
    A = new{T}()
    A.base_ring = R
    A.mult_table = mult_table
    A.one = one
    return A
  end

  function AlgAss{T}(R::Ring, mult_table::Array{T, 3}) where {T}
    A = new{T}()
    A.base_ring = R
    A.mult_table = mult_table
    return A
  end
end

mutable struct AlgAssElem{T} <: RingElem
  parent::AlgAss{T}
  coeffs::Array{T, 1}

  function AlgAssElem{T}(A::AlgAss{T}) where {T}
    z = new{T}()
    z.parent = A
    z.coeffs = Array{T, 1}(size(A.mult_table, 1))
    for i = 1:length(z.coeffs)
      z.coeffs[i] = A.base_ring()
    end
    return z
  end

  # This does not make a copy of coeffs
  function AlgAssElem{T}(A::AlgAss{T}, coeffs::Array{T, 1}) where{T}
    z = new{T}()
    z.parent = A
    z.coeffs = coeffs
    return z
  end
end
