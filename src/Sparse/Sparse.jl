#= basic support for sparse matrices, more Magma style than Julia
  a sparse matrix is a collection (Array) of sparse rows (SRow)
  A sparse matrix cannot have 0 rows!
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

export upper_triangular, vcat!, show, sub, SMat, SRow, random_SMatSLP,
       fmpz_mat, rows, cols, copy, push!, mul, mul!, toNemo, sparse,
       valence_mc, swap_rows!, elementary_divisors,
       randrow, hcat, hcat!, vcat, vcat!, mod!, mod_sym!



function SLP_AddRow(i::Int, j::Int, v::T) where T
  assert(v != 0)
  slp = TrafoAddScaled(i, j, v)
  return slp
end

function SLP_SwapRows(i::Int, j::Int)
  slp = TrafoSwap{fmpz}(i, j)
  return slp
end

# function mul!{T}(a::Array{T, 1}, s::SMatSLP_swap_row)
#   t = a[s.row]
#   a[s.row] = a[s.col]
#   a[s.col] = t
# end
# 
# function mul!{T}(a::Array{T, 1}, s::SMatSLP_add_row{T})
#   a[s.row] = a[s.row]*s.val + a[s.col]
# end
# 
# function mul_t!{T}(a::Array{T, 1}, s::SMatSLP_swap_row)
#   t = a[s.row]
#   a[s.row] = a[s.col]
#   a[s.col] = t
# end
# 
# function mul_t!{T}(a::Array{T, 1}, s::SMatSLP_add_row{T})
#   a[s.col] = a[s.col]*s.val + a[s.row]
# end
# 
# 
# function apply!{T}(a::Array{T}, b::Array{SMatSLP_add_row{T}, 1})
#   for i=length(b):-1:1
#     mul!(a, b[i])
#   end
#   return a
# end
# 
# function apply_t!{T}(a::Array{T}, b::Array{SMatSLP_add_row{T}, 1})
#   for i=1:length(b)
#     mul_t!(a, b[i])
#   end
#   return a
# end
# 
function random_SMatSLP(A::SMat{T}, i::Int, v::UnitRange) where T
  a = Array{SMatSLP_add_row{Int}}(i)
  for j=1:i
    c = rand(v)
    while c==0
      c = rand(v)
    end
    i1 = rand(1:rows(A))
    i2 = rand(1:rows(A))
    while i1==i2
      i1 = rand(1:rows(A))
      i2 = rand(1:rows(A))
    end
    a[j] = SLP_AddRow(i1, i2, Int(c))
  end
  return a
end

