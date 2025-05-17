function content(x::MatrixElem{T}) where T <: Hecke.LocalFieldValuationRingElem
  d = typemax{Int}
  for i = 1:nrows(x)
     for j = 1:ncols(x)
       if !is_zero_entry(x, i, j)
         d = min(valuation(x[i,j]), d) 
         is_zero(d) && return one(base_ring(x))
       end
     end
  end
  return uniformizer(base_ring(x))^d
end

#=
#wrong sign - possibly
function det(M::MatrixElem{T}) where {T <: Hecke.LocalFieldValuationRingElem}
   !is_square(M) && error("Not a square matrix in det")
   if nrows(M) == 0
      return one(base_ring(M))
   end
   h = hnf(M)
   return prod_diagonal(h)
end
=#

###############################################################################
#
#   Hermite Normal Form
#
###############################################################################

#  Hermite normal form for arbitrary matrices via a modification of the
#  Kannan-Bachem algorithm

# Reduces the entries above H[pivot[c], c]

function AbstractAlgebra.kb_reduce_column!(H::MatrixElem{T}, U::MatrixElem{T}, pivot::Vector{Int}, c::Int, with_trafo::Bool, start_element::Int = 1) where {T <: Hecke.LocalFieldValuationRingElem}

   # Let c = 4 and pivot[c] = 4. H could look like this:
   # ( 0 . * # * )
   # ( . * * # * )
   # ( 0 0 0 0 . )
   # ( 0 0 0 . * )
   # ( * * * * * )
   #
   # (. are pivots, we want to reduce the entries marked with #)
   # The #'s are in rows whose pivot is in a column left of column c.

   r = pivot[c]
   R = base_ring(H)
   t = R()
   for i = start_element:c - 1
      p = pivot[i]
      if p == 0
         continue
      end
      # So, the pivot in row p is in a column left of c.
      if is_zero_entry(H, p, c)
         continue
      end
      q = -div(H[p, c], H[r, c])
      q = setprecision(q, precision(R))
      for j = c:ncols(H)
         t = mul!(t, q, H[r, j])
         H[p, j] += t
      end
      if with_trafo
         for j = 1:ncols(U)
            t = mul!(t, q, U[r, j])
            U[p, j] += t
         end
      end
   end
   return nothing
end

# Multiplies row r by a unit such that the entry H[r, c] is "canonical"
function AbstractAlgebra.kb_canonical_row!(H::MatrixElem{<:Hecke.LocalFieldValuationRingElem}, U, r::Int, c::Int, with_trafo::Bool)
   cu = canonical_unit(H[r, c])
   R = base_ring(H)
   if !isone(cu)
     cu = setprecision(cu, precision(R))
      for j = c:ncols(H)
         H[r, j] = divexact(H[r, j], cu)
      end
      if with_trafo
         for j = 1:ncols(U)
            U[r, j] = divexact(U[r, j], cu)
         end
      end
   end
   return nothing
end

function AbstractAlgebra.hnf_kb!(H::MatrixElem{T}, U::MatrixElem{T}, with_trafo::Bool = false, start_element::Int = 1) where T <: Hecke.LocalFieldValuationRingElem
#   IN = deepcopy(H)
#   @assert isone(U)
#   @assert minimum(map(precision, H)) > 20
#   @assert minimum(map(precision, U)) > 20
   m = nrows(H)
   n = ncols(H)
   pivot = zeros(Int, n) # pivot[j] == i if the pivot of column j is in row i

   # Find the first non-zero entry of H
   row1, col1 = AbstractAlgebra.kb_search_first_pivot(H, start_element)
   if row1 == 0
      return nothing
   end
   pivot[col1] = row1
   AbstractAlgebra.kb_canonical_row!(H, U, row1, col1, with_trafo)
#   @assert (!with_trafo) || U*IN == H
   pivot_max = col1
   t = base_ring(H)()
   t1 = base_ring(H)()
   t2 = base_ring(H)()
   for i = row1 + 1:m
      new_pivot = false
      for j = start_element:n
         if is_zero_entry(H, i, j)
            continue
         end
         if pivot[j] == 0
            # We found a non-zero entry in a column without a pivot: This is a
            # new pivot
            pivot[j] = i
            pivot_max = max(pivot_max, j)
            new_pivot = true
         else
            # We have a pivot for this column: Use it to write 0 in H[i, j]
            p = pivot[j]
            d, u, v, b, a = AbstractAlgebra.gcdxx(H[p, j], H[i, j])
#            @show map(precision, [d, u, v, b, a])
#            @assert u*a-b*v == 1
            for c = j:n
               t = deepcopy(H[i, c])
               t1 = mul_red!(t1, a, H[i, c], false)
               t2 = mul_red!(t2, b, H[p, c], false)
               H[i, c] = reduce!(t1 + t2)
               t1 = mul_red!(t1, u, H[p, c], false)
               t2 = mul_red!(t2, v, t, false)
               H[p, c] = reduce!(t1 + t2)
            end
            if with_trafo
               for c = 1:m
                  t = deepcopy(U[i, c])
                  t1 = mul_red!(t1, a, U[i, c], false)
                  t2 = mul_red!(t2, b, U[p, c], false)
                  U[i, c] = reduce!(t1 + t2)
                  t1 = mul_red!(t1, u, U[p, c], false)
                  t2 = mul_red!(t2, v, t, false)
                  U[p, c] = reduce!(t1 + t2)
               end
#   @assert U*IN == H
#   @assert minimum(map(precision, H)) > 20
#   @assert minimum(map(precision, U)) > 20
   pivot_max = col1
            end
         end

         # We changed the pivot of column j (or found a new one).
         # We have do reduce the entries marked with # in
         # ( 0 0 0 . * )
         # ( . # # * * )
         # ( 0 0 . * * )
         # ( 0 . # * * )
         # ( * * * * * )
         # where . are pivots and i = 4, j = 2. (This example is for the
         # "new pivot" case.)
         AbstractAlgebra.kb_canonical_row!(H, U, pivot[j], j, with_trafo)
#   @assert minimum(map(precision, H)) > 20
#   @assert minimum(map(precision, U)) > 20
         for c = j:pivot_max
            if pivot[c] == 0
               continue
            end
            AbstractAlgebra.kb_reduce_column!(H, U, pivot, c, with_trafo, start_element)
#   @assert minimum(map(precision, H)) > 20
#   @assert minimum(map(precision, U)) > 20
         end
         if new_pivot
            break
         end
      end
   end
   AbstractAlgebra.kb_sort_rows!(H, U, pivot, with_trafo, start_element)
   return nothing
end

###############################################################################
#
#   Smith Normal Form
#
###############################################################################

function AbstractAlgebra.kb_clear_row!(S::MatrixElem{T}, K::MatrixElem{T}, i::Int, with_trafo::Bool) where {T <: Hecke.LocalFieldValuationRingElem}
   m = nrows(S)
   n = ncols(S)
   t = base_ring(S)()
   t1 = base_ring(S)()
   t2 = base_ring(S)()
   for j = i+1:n
      if is_zero_entry(S, i, j)
         continue
      end
      d, u, v, b, a = AbstractAlgebra.gcdxx(S[i, i], S[i, j])
#      @assert u*S[i,i] + v*S[i,j] == d
#      @assert is_one(u*a-v*b)
#      @assert is_zero(b*S[i,i] + a*S[i,j])
      for r = i:m
         t = deepcopy(S[r, j])
         t1 = mul_red!(t1, a, S[r, j], false)
         t2 = mul_red!(t2, b, S[r, i], false)
         S[r, j] = reduce!(t1 + t2)
         t1 = mul_red!(t1, u, S[r, i], false)
         t2 = mul_red!(t2, v, t, false)
         S[r, i] = reduce!(t1 + t2)
      end
      if with_trafo
         for r = 1:n
            t = deepcopy(K[r,j])
            t1 = mul_red!(t1, a, K[r, j], false)
            t2 = mul_red!(t2, b, K[r, i], false)
            K[r, j] = reduce!(t1 + t2)
            t1 = mul_red!(t1, u, K[r, i], false)
            t2 = mul_red!(t2, v, t, false)
            K[r, i] = reduce!(t1 + t2)
         end
      end
   end
   return nothing
end

function AbstractAlgebra.snf_kb!(S::MatrixElem{T}, U::MatrixElem{T}, K::MatrixElem{T}, with_trafo::Bool = false) where {T <: Hecke.LocalFieldValuationRingElem}
   R = base_ring(S)
   m = nrows(S)
   n = ncols(S)
   l = min(m, n)
   i = 1
   t = base_ring(S)()
   t1 = base_ring(S)()
   t2 = base_ring(S)()
   while i <= l
      AbstractAlgebra.kb_clear_row!(S, K, i, with_trafo)
      AbstractAlgebra.hnf_kb!(S, U, with_trafo, i)
      c = i + 1
      while c <= n && is_zero_entry(S, i, c)
         c += 1
      end
      if c != n + 1
         continue
      end
      i+=1
   end
   for i = 1:l-1
      for j = i + 1:l
         if isone(S[i, i])
           break
         end
         if is_zero_entry(S, i, i) && is_zero_entry(S, j, j)
            continue
         end
         d, u, v, q1, q2 = AbstractAlgebra.gcdxx(S[i, i], S[j, j])
#         @assert d == u*S[i,i] +v*S[j,j]
#         @assert u*q2+v*q1 == 1
#         @assert q1*S[i,i] + q2*S[j,j] == 0
         if with_trafo
            q = -divexact(S[j, j], d)
            t1 = mul!(t1, q, v)
            for c = 1:m
               t = deepcopy(U[i, c])
               U[i, c] += U[j, c]
               t2 = mul_red!(t2, t1, U[j, c], false)
               U[j, c] += t2
               t2 = mul_red!(t2, t1, t, false)
               U[j, c] = reduce!(U[j, c] + t2)
            end
            for r = 1:n
               t = deepcopy(K[r, i])
               t1 = mul_red!(t1, K[r, i], u, false)
               t2 = mul_red!(t2, K[r, j], v, false)
               K[r, i] = reduce!(t1 + t2)
               t1 = mul_red!(t1, t, q1, false)
               t2 = mul_red!(t2, K[r, j], q2, false)
               K[r, j] = reduce!(t1 + t2)
            end
         end
         S[j, j] = setprecision(S[i, i]*divexact(S[j, j], d), precision(R))
         S[i, i] = d
      end
   end
   return nothing
end


