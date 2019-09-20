#= basic support for sparse matrices, more Magma style than Julia
  a sparse matrix is a collection (Array) of sparse rows (SRow)
  A SRow is two Arrays, one (pos) containing the columns, values
  contains the values.
  A[i,j] = A.rows[i].values[A.rows[i].pos[j]]
  to be formal

  The upper_triangular stuff performs very elementary transformations
  until the matrix becomes dense. At this point, the dense bit is extraced and
  converted to an fmpz_mat which is then hnf'ed.

  Missing:
   full HNF, Howell, modular and not
   better elemination strategy

  TODO: sort out the various upper_triangular implementations.
  One (+one with trafo) is probably enough
=#

import Base.push!, Base.max, Nemo.nbits, Base.Array,
       Base.hcat,
       Base.vcat, Base.max, Base.min

export vcat!, show, sub, SMat, SRow,
       fmpz_mat, copy, push!, mul, mul!, toNemo, sparse,
       valence_mc, swap_rows!, elementary_divisors,
       rand_row, hcat, hcat!, vcat, vcat!, mod!, mod_sym!

include("Sparse/Matrix.jl")
include("Sparse/Row.jl")
include("Sparse/Module.jl")
include("Sparse/Trafo.jl")
include("Sparse/HNF.jl")
include("Sparse/Solve.jl")
include("Sparse/UpperTriangular.jl")
