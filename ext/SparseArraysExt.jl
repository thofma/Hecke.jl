module SparseArraysExt

using Hecke, SparseArrays

SparseArrays.nnz(A::SMat) = Hecke.nnz(A)

@doc raw"""
    sparse(A::SMat) -> SparseMatrixCSC

The same matrix, but as a sparse matrix of julia type `SparseMatrixCSC`.
"""
function SparseArrays.sparse(A::SMat{T}) where T
  I = zeros(Int, A.nnz)
  J = zeros(Int, A.nnz)
  V = Vector{T}(undef, A.nnz)
  i = 1
  for r = 1:nrows(A)
    for j=1:length(A.rows[r].pos)
      I[i] = r
      J[i] = A.rows[r].pos[j]
      V[i] = A.rows[r].values[j]
      i += 1
    end
  end
  return SparseArrays.sparse(I, J, V)
end

end # module
