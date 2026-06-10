mutable struct data_PartRef{T}
 A::SMat{T}
 R
 det_factor::T #tracks change in det
 single_row_limit::Int64 #idx first row after rows with one light entry
 base::Int64 #idx for first row after ref
 dense_start::Int64 #last row before dense part
 nlight::Int64 #number of light cols
 nsingle::Int64 #number of rows in part ref
 light_weight::Vector{Int64} #number of entries in light cols for all rows in A (current ordering)
 col_list::Vector{Vector{Int64}} #lists entries outside of triangular form column-wise
 col_list_perm::Vector{Int64} #perm gives new ordering of original A[i] via their indices
 col_list_permi::Vector{Int64} #A[permi[i]]=A[i] before permutation = list of sigma(i) (recent position of former A[i])
 is_light_col::Vector{Bool}
 is_single_col::Vector{Bool}
 single_col::Vector{Int64} #single_col[i] = c >= 0 if col c has its only entry in row i, i always recent position
 heavy_ext::Int64
 heavy_col_idx::Vector{Int64}
 heavy_col_len::Vector{Int64}
 heavy_mapi::Vector{Int64}
 heavy_map::Vector{Int64}

 function data_PartRef(A::SMat{T}) where T
  col_list = _col_list(A)
  return new{T}(A,
  base_ring(A),
  one(base_ring(A)),
  1,
  1,
  nrows(A),
  ncols(A),
  0,
  [length(A[i]) for i in 1:nrows(A)],
  col_list,
  collect(1:nrows(A)),
  collect(1:nrows(A)),
  fill(true, ncols(A)),
  fill(false, ncols(A)),
  fill(0, nrows(A)),
  0,
  Int[],
  Int[],
  Int[],
  fill(0, ncols(A)))
 end
end

function _col_list(A)
 n = nrows(A)
 m = ncols(A)
 col_list = [Array{Int64}([]) for i = 1:m]
 for i in 1:n
  for c in A[i].pos
   col = col_list[c]
   push!(col, i)
  end
 end
 return col_list
end

################################################################################
#
#  Compute determinant - given matrix in part ref
#
################################################################################

function PR_det(A)
 PR = part_ref!(A)
 D = compose_dense_matrix(PR)
 d = det(D)
 for i = 1:PR.nsingle
  d*=PR.A[i, PR.single_col[i]]
 end
 return div(d, PR.det_factor)
end

################################################################################
#
#  Partial Echolonization with determinant tracking
#
################################################################################

#Build an upper triangular matrix for as many columns as possible compromising
#the loss of sparsity during this process. 
#Goal: det computation

function part_ref!(A)
 n = nrows(A)
 m = ncols(A) 
 PR = data_PartRef(A)
 #for determinant calculations:
 @assert n == m
 #look for zero_rows:
 for i = 1:n
  if iszero(length(A))
   PR.det_factor = zero(PR.R)
   println("determinant is zero")
   return PR
  end
 end

 single_rows_to_top!(PR)

 while PR.nlight > 0 && PR.base <= PR.dense_start
  build_part_ref!(PR)
  for i = 1:m
   PR.is_light_col[i] && @assert length(PR.col_list[i]) != 1
  end
  (PR.nlight == 0 || PR.base > n) && break
  best_single_row = find_best_single_row(PR)
  best_single_row < 0 && @assert(PR.base == PR.single_row_limit)
  
  if best_single_row < 0
   find_dense_cols(PR)
   turn_heavy(PR)
   continue #while PR.nlight > 0 && PR.base <= PR.dense_start
  end
  eliminate_and_update!(best_single_row, PR)
 end

 #assert that zero rows have been catched before:
 for i = 1:PR.A.r
  @assert !iszero(length(PR.A[i]))
 end

 return PR
end

function single_rows_to_top!(PR)
 for i = 1:nrows(PR.A)
  len = length(PR.A[i])
  @assert !iszero(len)
  if len == 1
   @assert PR.single_row_limit <=i
   if i != PR.single_row_limit
    swap_rows_perm(i, PR.single_row_limit, PR)
   end
   PR.single_row_limit +=1
  end
 end
 return PR
end

function build_part_ref!(PR)
 queue = collect(ncols(PR.A):-1:1)
 while !isempty(queue)
  queue_new = Int[]
  for j in queue
   if length(PR.col_list[j]) == 1 && PR.is_light_col[j]
    singleton_row_origin = only(PR.col_list[j])
    singleton_row_idx = PR.col_list_permi[singleton_row_origin]
    for jj in PR.A[singleton_row_idx].pos
     if PR.is_light_col[jj]
      @assert singleton_row_origin in PR.col_list[jj]
      j_idx = findfirst(isequal(singleton_row_origin), PR.col_list[jj])
      deleteat!(PR.col_list[jj],j_idx)
      length(PR.col_list[jj]) == 1 && push!(queue_new, jj)
     end
    end
    PR.is_light_col[j] = false
    PR.is_single_col[j] = true
    PR.single_col[singleton_row_idx] = j
    PR.nlight-=1
    PR.nsingle+=1
    swap_i_into_base(singleton_row_idx, PR)
    PR.base+=1
   end
  end
  queue = queue_new
 end
end

function find_best_single_row(PR)
 best_single_row = -1
 best_col = NaN
 best_val = NaN
 best_len = -1
 best_is_one = false
 for i = PR.base:PR.single_row_limit-1
  single_row = PR.A[i]
  single_row_len = length(single_row)
  w = PR.light_weight[i]
  @assert w == 1
  j_light = find_light_entry(single_row.pos, PR.is_light_col)
  single_row_val = PR.A[i, j_light]
  @assert length(PR.col_list[j_light]) > 1
  is_one = isone(single_row_val)||isone(-single_row_val)
  if best_single_row < 0
   best_single_row = i
   best_col = j_light
   best_len = single_row_len
   best_is_one = is_one
   best_val = single_row_val
  elseif !best_is_one && is_one
   best_single_row = i
   best_col = j_light
   best_len = single_row_len
   best_is_one = true
   best_val = single_row_val
  elseif (is_one == best_is_one && single_row_len < best_len)
   best_single_row = i
   best_col = j_light
   best_len = single_row_len
   best_is_one = is_one
   best_val = single_row_val
  end
 end
 return best_single_row
end

function find_dense_cols(PR)
 m = ncols(PR.A)
 nheavy = m - (PR.nlight + PR.nsingle)
 nheavy == 0 ? PR.heavy_ext = max(div(PR.nlight,20),1) : PR.heavy_ext = max(div(PR.nlight,100),1)
 PR.heavy_col_idx = fill(-1, PR.heavy_ext) #indices (descending order for same length)
 PR.heavy_col_len = fill(-1, PR.heavy_ext)#length of cols in heavy_idcs (ascending)
 light_cols = findall(x->PR.is_light_col[x], 1:m)
 for i = m:-1:1
  if PR.is_light_col[i]
   col_len = length(PR.col_list[i])
   if col_len > PR.heavy_col_len[1]
    if PR.heavy_ext == 1
     PR.heavy_col_idx[1] = i
     PR.heavy_col_len[1] = col_len
    else
     for j = PR.heavy_ext:-1:2 
      if col_len >= PR.heavy_col_len[j]
       for k = 1:j-1
        PR.heavy_col_idx[k] = PR.heavy_col_idx[k + 1]
        PR.heavy_col_len[k] = PR.heavy_col_len[k + 1]
       end
       PR.heavy_col_idx[j] = i
       PR.heavy_col_len[j] = col_len
       break
      end 
     end
    end
   end
  end
 end
 @assert light_cols == findall(x->PR.is_light_col[x], 1:m)
end

function turn_heavy(PR)
 for j = 1:PR.heavy_ext
  c = PR.heavy_col_idx[j]
  if c<0
   continue
  end
  PR.is_light_col[c] = false
  lt2hvy_col = PR.col_list[c]
  lt2hvy_len = length(lt2hvy_col)
  @assert lt2hvy_len == length(PR.col_list[c])
  for k = 1:lt2hvy_len
   i_origin = lt2hvy_col[k]
   i_now = PR.col_list_permi[i_origin]
   @assert PR.light_weight[i_now] > 0
   PR.light_weight[i_now]-=1
   handle_new_light_weight!(i_now, PR)
  end
 end
 PR.nlight -= PR.heavy_ext
end

function handle_new_light_weight!(i, PR)
 w = PR.light_weight[i]
 if w == 0
  if iszero(length(PR.A[i]))
   PR.det_factor = zero(PR.R)
   println("determinant is zero")
   return PR
  end
  move_to_end(i, PR)
 elseif w == 1
  if i > PR.single_row_limit
   swap_rows_perm(i, PR.single_row_limit, PR)
  end
  PR.single_row_limit += 1
 end
 return PR
end

function eliminate_and_update!(best_single_row, PR)
 @assert best_single_row != 0
 best_row = deepcopy(PR.A[best_single_row])
 best_col = find_light_entry(best_row.pos, PR.is_light_col)
 @assert length(PR.col_list[best_col]) > 1
 best_val = deepcopy(PR.A[best_single_row, best_col])
 @assert !iszero(best_val)
 best_col_idces = PR.col_list[best_col]
 row_idx = 0
 while length(best_col_idces) > 1
  row_idx = find_row_to_add_on(row_idx, best_row, best_col_idces, PR)
  @assert best_col_idces == PR.col_list[best_col]
  @assert row_idx > 0
  @assert PR.col_list_perm[row_idx] in PR.col_list[best_col]
  L_row = PR.col_list_perm[row_idx]
  add_to_eliminate!(L_row, row_idx, best_row, best_col, best_val, PR)
  update_after_addition!(L_row, row_idx, best_col, PR)
  handle_new_light_weight!(row_idx, PR)
 end
 return PR
end

function find_row_to_add_on(row_idx, best_row, best_col_idces::Vector{Int64}, PR::data_PartRef)
 for L_row in best_col_idces[end:-1:1]
  row_idx = PR.col_list_permi[L_row]
  PR.A[row_idx] == best_row && continue
  row_idx < PR.base && continue
  break
 end
 return row_idx
end

function add_to_eliminate!(L_row, row_idx, best_row, best_col, best_val, PR)
 @assert L_row in PR.col_list[best_col]
 @assert !(0 in PR.A[row_idx].values)
 val = PR.A[row_idx, best_col] 
 @assert !iszero(val)
 g = gcd(val, best_val)
 val_red = divexact(val, g)
 best_val_red = divexact(best_val, g)
 @assert L_row in PR.col_list[best_col]
 for c in PR.A[row_idx].pos
  @assert !isempty(PR.col_list[c])
  if PR.is_light_col[c]
   jj = findfirst(isequal(L_row), PR.col_list[c])
   deleteat!(PR.col_list[c], jj)
  end
 end
 scale_row!(PR.A, row_idx, best_val_red)
 PR.det_factor *= best_val_red
 @assert !iszero(PR.det_factor)
 @assert !(0 in PR.A[row_idx].values)
 Hecke.add_scaled_row!(best_row, PR.A[row_idx], -val_red)
 @assert iszero(PR.A[row_idx, best_col])
 return PR
end

function update_after_addition!(L_row, row_idx::Int, best_col, PR::data_PartRef)
 PR.light_weight[row_idx] = 0
 for c in PR.A[row_idx].pos
  @assert c != best_col
  if PR.is_light_col[c]
   sort!(push!(PR.col_list[c], L_row))
   PR.is_light_col[c] && (PR.light_weight[row_idx]+=1)
  end
 end
 return PR
end

################################################################################
#
#  Small Auxiliary Functions
#
################################################################################

function swap_entries(v, i,j)
 v[i],v[j] = v[j],v[i]
end

function swap_rows_perm(i::Int64, j::Int64, PR::data_PartRef)
 if i != j
  swap_rows!(PR.A, i, j)
  swap_entries(PR.single_col, i, j)
  swap_entries(PR.col_list_perm, i, j)
  swap_entries(PR.col_list_permi, PR.col_list_perm[i], PR.col_list_perm[j])
  swap_entries(PR.light_weight, i, j)
  PR.det_factor = - PR.det_factor
 end
end 

function swap_i_into_base(i::Int64, PR::data_PartRef)
 if i < PR.single_row_limit
  swap_rows_perm(i, PR.base, PR)
 else
   if i != PR.single_row_limit 
    swap_rows_perm(PR.base, PR.single_row_limit, PR)
   end
   PR.single_row_limit +=1
   swap_rows_perm(PR.base, i, PR)
 end
end

function find_light_entry(position_array::Vector{Int64}, is_light_col::Vector{Bool})::Int64
 for j in position_array[end:-1:1]
  if is_light_col[j]
   return j
  end
 end
end

function move_to_end(i::Int64, PR::data_PartRef)
 @assert !iszero(length(PR.A[i])) 
 @assert i >= PR.base
 swap_rows_perm(i, PR.dense_start, PR)
 if i < PR.single_row_limit
  swap_rows_perm(i, PR.single_row_limit-1, PR)
  PR.single_row_limit -=1
 end
 ds_origin = PR.col_list_perm[PR.dense_start]
 for c in PR.A[PR.dense_start].pos
  if PR.is_light_col[c]
   jj = findfirst(isequal(ds_origin), PR.col_list[c])
   deleteat!(PR.col_list[c], jj)
  end
 end
 PR.dense_start -= 1
end

################################################################################
#
#  Isolate non-triangular part
#
################################################################################

function compose_dense_matrix(PR::data_PartRef)
 @assert PR.nsingle == PR.dense_start
 n = nrows(PR.A)
 m = ncols(PR.A)
 j=1
 for i = 1:m
  if !PR.is_single_col[i]
   PR.heavy_map[i] = j
   push!(PR.heavy_mapi,i)
   j+=1
  end
 end

 D = sparse_matrix(PR.R, 0, n-PR.nsingle)
 for i = PR.dense_start+1:n
  p = Int[]
  v = ZZRingElem_Array()
  sizehint!(v, length(PR.A[i]))
  for j = 1:length(PR.A[i].pos)
   push!(v, PR.A[i].values[j])
   push!(p, PR.heavy_map[PR.A[i].pos[j]])
  end
  push!(D, sparse_row(ZZ, p, v))
 end
 return D
end