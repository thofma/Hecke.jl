#TODO: declare return types
#TODO: sizehints
#TODO: pointer pointer pointer
#TODO: sizehint for heavy stuff can be given later, so don't initialize immediately
#TODO: new struct for second part

#=
PROBLEMS:
- why more nnzs in SG.A+SG.Y than in PR.A?
- maximum of PR.A greater as in SG.Y?
=#

mutable struct data_StructGauss{T}
 A::SMat{T}
 Y::SMat{T}
 R
 base::Int64
 single_row_limit::Int64
 nlight::Int64
 npivots::Int64
 light_weight::Vector{Int64}
 col_list::Vector{Vector{Int64}} 
 col_list_perm::Vector{Int64} #perm gives new ordering of original A[i] via their indices
 col_list_permi::Vector{Int64} #A[permi[i]]=A[i] before permutation = list of sigma(i) (recent position of former A[i])
 is_light_col::Vector{Bool}
 is_pivot_col::Vector{Bool}
 pivot_col::Vector{Int64} #pivot_col[i] = c >= 0 if col c has its only entry in row i, i always recent position
 #heavy_ext::Int64
 #heavy_col_idx::Vector{Int64}
 #heavy_col_len::Vector{Int64}
 #heavy_mapi::Vector{Int64}
 #heavy_map::Vector{Int64}

 function data_StructGauss(A::SMat{T}) where T
  Y = sparse_matrix(base_ring(A), 0, ncols(A))
  col_list = _col_list(A)
  return new{T}(A,
  Y,
  base_ring(A),
  1,
  1,
  ncols(A),
  0,
  [length(A[i]) for i in 1:nrows(A)],
  col_list,
  collect(1:nrows(A)),
  collect(1:nrows(A)),
  fill(true, ncols(A)),
  fill(false, ncols(A)),
  fill(0, nrows(A)),
  #0,
  #Int[],
  #Int[],
  #Int[],
  #fill(0, ncols(A))
  )
 end
end

function _col_list(A::SMat{T})::Vector{Vector{Int64}} where T
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

@doc raw"""
    structured_gauss(A::SMat{T}) where T <: RingElem

Return a tuple (\nu, N) consisting of the nullity \nu of A and a basis N
(consisting of column vectors) for the right nullspace of A, i.e. such that
AN is the zero matrix.
"""

function structured_gauss(A::SMat{T}) where T <: RingElem
 SG = part_echolonize!(A)
 return compute_kernel(SG)
end

@doc raw"""
    structured_gauss_field(A::SMat{T}) where T <: FieldElem

Return a tuple (\nu, N) consisting of the nullity \nu of A and a basis N
(consisting of column vectors) for the right nullspace of A, i.e. such that
AN is the zero matrix.
"""

function structured_gauss_field(A::SMat{T}) where T <: FieldElem
 SG = part_echolonize_field!(A)
 return compute_kernel_field(SG)
end

################################################################################
#
#  Partial Echolonization
#
################################################################################

#Build an upper triangular matrix for as many columns as possible compromising
#the loss of sparsity during this process.

function part_echolonize!(A::SMat{T})::data_StructGauss where T <: RingElem
 A = delete_zero_rows!(A)
 n = nrows(A)
 m = ncols(A)
 SG = data_StructGauss(A)
 single_rows_to_top!(SG)

 while SG.nlight > 0 && SG.base <= n
  build_part_ref!(SG)
  for i = 1:m
   SG.is_light_col[i] && @assert length(SG.col_list[i]) != 1
  end
  (SG.nlight == 0 || SG.base > n) && break
  best_single_row = find_best_single_row(SG)
  best_single_row < 0 && @assert(SG.base == SG.single_row_limit)
  
  if best_single_row < 0
   #find_dense_cols(SG)
   turn_heavy(SG)
   continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end
  eliminate_and_update2!(best_single_row, SG)
 end
 return SG
end

function part_echolonize_field!(A::SMat{T})::data_StructGauss where T <: FieldElem
 A = delete_zero_rows!(A)
 n = nrows(A)
 m = ncols(A)
 SG = data_StructGauss(A)
 single_rows_to_top!(SG)

 while SG.nlight > 0 && SG.base <= n
  build_part_ref_field!(SG)
  for i = 1:m
   SG.is_light_col[i] && @assert length(SG.col_list[i]) != 1
  end
  (SG.nlight == 0 || SG.base > n) && break
  best_single_row = find_best_single_row_field(SG)
  best_single_row < 0 && @assert(SG.base == SG.single_row_limit)
  
  if best_single_row < 0
   find_dense_cols(SG)
   turn_heavy(SG)
   continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end

  eliminate_and_update_field!(best_single_row, SG)
 end
 return SG
end

function single_rows_to_top!(SG::data_StructGauss)::data_StructGauss
 for i = 1:nrows(SG.A)
  len = length(SG.A[i])
  @assert !iszero(len)
  if len == 1
   @assert SG.single_row_limit <=i
   if i != SG.single_row_limit
    swap_rows_perm(i, SG.single_row_limit, SG)
   end
   SG.single_row_limit +=1
  end
 end
 return SG
end

function build_part_ref!(SG::data_StructGauss)
 queue = collect(ncols(SG.A):-1:1)
 while !isempty(queue)
  queue_new = Int[]
  for j in queue
   if length(SG.col_list[j])==1 && SG.is_light_col[j]
    singleton_row_origin = only(SG.col_list[j])
    singleton_row_idx = SG.col_list_permi[singleton_row_origin]
    for jj in SG.A[singleton_row_idx].pos
     if SG.is_light_col[jj]
      @assert singleton_row_origin in SG.col_list[jj]
      j_idx = findfirst(isequal(singleton_row_origin), SG.col_list[jj])
      deleteat!(SG.col_list[jj],j_idx)
      length(SG.col_list[jj]) == 1 && push!(queue_new, jj)
     end
    end
    SG.is_light_col[j] = false
    SG.is_pivot_col[j] = true
    SG.pivot_col[singleton_row_idx] = j
    SG.nlight-=1
    SG.npivots+=1
    swap_i_into_base(singleton_row_idx, SG)
    SG.base+=1
   end
  end
  queue = queue_new
 end
end

function build_part_ref_field!(SG::data_StructGauss)
 queue = collect(ncols(SG.A):-1:1)
 while !isempty(queue)
  queue_new = Int[]
  for j in queue
   if length(SG.col_list[j])==1 && SG.is_light_col[j]
    singleton_row_origin = only(SG.col_list[j])
    singleton_row_idx = SG.col_list_permi[singleton_row_origin]
    scale_row!(SG.A, singleton_row_idx, inv(SG.A[singleton_row_idx, j]))
    for jj in SG.A[singleton_row_idx].pos
     if SG.is_light_col[jj]
      @assert singleton_row_origin in SG.col_list[jj]
      j_idx = findfirst(isequal(singleton_row_origin), SG.col_list[jj])
      deleteat!(SG.col_list[jj],j_idx)
      length(SG.col_list[jj]) == 1 && push!(queue_new, jj)
     end
    end
    SG.is_light_col[j] = false
    SG.is_pivot_col[j] = true
    SG.pivot_col[singleton_row_idx] = j
    SG.nlight-=1
    SG.npivots+=1
    swap_i_into_base(singleton_row_idx, SG)
    SG.base+=1
   end
  end
  queue = queue_new
 end
end

function find_best_single_row(SG::data_StructGauss)::Int64
 best_single_row = -1
 best_col = NaN
 best_val = NaN
 best_len = -1
 best_is_one = false
 for i = SG.base:SG.single_row_limit-1
  single_row = SG.A[i]
  single_row_len = length(single_row)
  w = SG.light_weight[i]
  @assert w == 1
  light_idx = find_light_entry(single_row.pos, SG.is_light_col)
  j_light = single_row.pos[light_idx]
  single_row_val = SG.A[i, j_light]
  @assert length(SG.col_list[j_light]) > 1
  is_one = isone(single_row_val)||isone(-single_row_val)
  #TODO: look for useful equivalent in polyrings
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

function find_best_single_row_field(SG::data_StructGauss)::Int64
 best_single_row = -1
 best_len = -1
 for i = SG.base:SG.single_row_limit-1
  single_row = SG.A[i]
  single_row_len = length(single_row)
  w = SG.light_weight[i]
  @assert w == 1
  if best_single_row < 0 || single_row_len < best_len
   best_single_row = i
   best_len = single_row_len
  end
 end
 return best_single_row
end 

#=
function find_dense_cols(SG::data_StructGauss)
 m = ncols(SG.A)
 nheavy = m - (SG.nlight + SG.npivots)
 nheavy == 0 ? SG.heavy_ext = max(div(SG.nlight,20),1) : SG.heavy_ext = max(div(SG.nlight,100),1)
 SG.heavy_col_idx = fill(-1, SG.heavy_ext) #indices (descending order for same length)
 SG.heavy_col_len = fill(-1, SG.heavy_ext)#length of cols in heavy_idcs (ascending)
 light_cols = findall(x->SG.is_light_col[x], 1:m)
 for i = m:-1:1
  if SG.is_light_col[i]
   col_len = length(SG.col_list[i])
   if col_len > SG.heavy_col_len[1]
    if SG.heavy_ext == 1
     SG.heavy_col_idx[1] = i
     SG.heavy_col_len[1] = col_len
    else
     for j = SG.heavy_ext:-1:2 
      if col_len >= SG.heavy_col_len[j]
       for k = 1:j-1
        SG.heavy_col_idx[k] = SG.heavy_col_idx[k + 1]
        SG.heavy_col_len[k] = SG.heavy_col_len[k + 1]
       end
       SG.heavy_col_idx[j] = i
       SG.heavy_col_len[j] = col_len
       break
      end 
     end
    end
   end
  end
 end
 @assert light_cols == findall(x->SG.is_light_col[x], 1:m)
end
=#

function turn_heavy(SG::data_StructGauss)
 heavy_col_idx = 0
 heavy_col_len = 0
 for i = ncols(SG.A):-1:1
  if SG.is_light_col[i]
   if length(SG.col_list[i]) > heavy_col_len
    heavy_col_len = length(SG.col_list[i])
    heavy_col_idx = i
   end
  end
 end
 SG.is_light_col[heavy_col_idx] = false
 lt2hvy_col = SG.col_list[heavy_col_idx]
 for i_origin in lt2hvy_col
  i_current = SG.col_list_permi[i_origin]
  @assert SG.light_weight[i_current] > 0
  SG.light_weight[i_current]-=1
  handle_new_light_weight!(i_current, SG)
 end
 SG.nlight -= 1
end

function handle_new_light_weight!(i::Int64, SG::data_StructGauss)::data_StructGauss
 w = SG.light_weight[i]
 if w == 0
  swap_i_into_base(i, SG)
  SG.pivot_col[SG.base] = 0
  move_into_Y(SG.base, SG)
  SG.base+=1
 elseif w == 1
  if i > SG.single_row_limit
   swap_rows_perm(i, SG.single_row_limit, SG)
  end
  SG.single_row_limit += 1
 elseif SG.base <= i < SG.single_row_limit #TODO: check if necessary
  swap_rows_perm(i, SG.single_row_limit-1, SG)
  SG.single_row_limit-=1
 end
 return SG
end

function eliminate_and_update!(best_single_row::Int64, SG::data_StructGauss)::data_StructGauss
 @assert best_single_row != 0
 best_row = deepcopy(SG.A[best_single_row])
 best_col = find_light_entry(best_row.pos, SG.is_light_col)
 @assert length(SG.col_list[best_col]) > 1
 best_val = deepcopy(SG.A[best_single_row, best_col])
 @assert !iszero(best_val)
 best_col_idces = SG.col_list[best_col]
 row_idx = 0
 while length(best_col_idces) > 1
  row_idx = find_row_to_add_on(row_idx, best_row, best_col_idces, SG)
  @assert best_col_idces == SG.col_list[best_col]
  @assert row_idx > 0
  @assert SG.col_list_perm[row_idx] in SG.col_list[best_col]
  L_row = SG.col_list_perm[row_idx]
  add_to_eliminate!(L_row, row_idx, best_row, best_col, best_val, SG)
  update_after_addition!(L_row, row_idx, best_col, SG)
  handle_new_light_weight!(row_idx, SG)
 end
 return SG
end

function eliminate_and_update2!(best_single_row::Int64, SG::data_StructGauss)::data_StructGauss
 @assert !iszero(best_single_row)
 L_best = deepcopy(SG.col_list_perm[best_single_row])
 light_idx = find_light_entry(SG.A[best_single_row].pos, SG.is_light_col)
 best_col = SG.A[best_single_row].pos[light_idx]
 @assert length(SG.col_list[best_col]) > 1
 best_val = SG.A[best_single_row].values[light_idx] #test
 @assert !iszero(best_val) #test
 row_idx = 0
 while length(SG.col_list[best_col]) > 1
  best_single_row = SG.col_list_permi[L_best]
  @hassert :StructGauss SG.light_weight[best_single_row] == 1
  row_idx = find_row_to_add_on2(best_single_row, best_col, SG)
  @assert row_idx > 0
  @hassert :StructGauss L_best != SG.col_list_perm[row_idx]
  L_row = SG.col_list_perm[row_idx]
  add_to_eliminate2!(L_row, row_idx, best_single_row, best_col, SG)
  update_after_addition2(L_row, row_idx, best_col, SG)
  handle_new_light_weight!(row_idx, SG)
 end
 return SG
end

function eliminate_and_update_field!(best_single_row::Int64, SG::data_StructGauss)::data_StructGauss
 @assert best_single_row != 0
 best_col = find_light_entry(SG.A[best_single_row].pos, SG.is_light_col)
 @assert length(SG.col_list[best_col]) > 1
 best_val = SG.A[best_single_row, best_col]
 @assert !iszero(best_val)
 scale_row!(SG.A, best_single_row, inv(best_val))
 best_val = SG.A[best_single_row, best_col]
 @assert isone(best_val)
 best_row = deepcopy(SG.A[best_single_row])
 best_col_idces = SG.col_list[best_col]
 row_idx = 0
 while length(best_col_idces) > 1
  row_idx = find_row_to_add_on(row_idx, best_row, best_col_idces, SG)
  @assert best_col_idces == SG.col_list[best_col]
  @assert SG.col_list_perm[row_idx] in SG.col_list[best_col]
  @assert row_idx > 0
  L_row = SG.col_list_perm[row_idx]
  add_to_eliminate_field!(L_row, row_idx, best_row, best_col, best_val, SG)
  update_after_addition!(L_row, row_idx, best_col, SG)
  handle_new_light_weight!(row_idx, SG)
 end
 return SG
end

function find_row_to_add_on(row_idx::Int64, best_row::SRow{T}, best_col_idces::Vector{Int64}, SG::data_StructGauss)::Int64 where T <: FieldElem
 for L_row in best_col_idces[end:-1:1]
  row_idx = SG.col_list_permi[L_row]
  SG.A[row_idx] == best_row && continue
  row_idx < SG.base && continue
  break
 end
 return row_idx
end

function find_row_to_add_on2(best_single_row::Int64, best_col::Int64, SG::data_StructGauss)::Int64
 row_idx = 0
 for L_row in SG.col_list[best_col][end:-1:1]
  row_idx = SG.col_list_permi[L_row]
  row_idx == best_single_row && continue #TODO: work with origin idces here
  @assert SG.base <= row_idx
  break
 end
 return row_idx
end

function add_to_eliminate!(L_row::Int64, row_idx::Int64, best_row::SRow{T}, best_col::Int64, best_val::RingElem, SG::data_StructGauss)::data_StructGauss where T <: RingElem
 @assert L_row in SG.col_list[best_col]
 @assert !(0 in SG.A[row_idx].values)
 val = SG.A[row_idx, best_col]
 @assert !iszero(val)
 g = gcd(val, best_val)
 val_red = divexact(val, g)
 best_val_red = divexact(best_val, g)
 @assert L_row in SG.col_list[best_col]
 for c in SG.A[row_idx].pos
  @assert !isempty(SG.col_list[c])
  if SG.is_light_col[c]
   jj = findfirst(isequal(L_row), SG.col_list[c])
   deleteat!(SG.col_list[c], jj)
  end
 end
 scale_row!(SG.A, row_idx, best_val_red)
 @assert !(0 in best_row.values)
 SG.A.nnz -= length(SG.A[row_idx])
 Hecke.add_scaled_row!(best_row, SG.A[row_idx], -val_red)
 SG.A.nnz += length(SG.A[row_idx])
 @assert iszero(SG.A[row_idx, best_col])
 @assert !(0 in SG.A[row_idx].values)
 return SG
end

function add_to_eliminate2!(L_row::Int64, row_idx::Int64, best_single_row::Int64, best_col::Int64, SG::data_StructGauss)::data_StructGauss
 L_best = SG.col_list_perm[best_single_row]
 @assert L_row in SG.col_list[best_col]
 @assert !(0 in SG.A[row_idx].values)
 best_row = SG.A[best_single_row]
 bv = best_row.values[searchsortedfirst(best_row.pos, best_col)]
 for c in SG.A[row_idx].pos
  @assert !isempty(SG.col_list[c]) #TODO: check why empty dense cols exist
  if SG.is_light_col[c]
   jj = searchsortedfirst(SG.col_list[c], L_row)
   deleteat!(SG.col_list[c], jj)
  end
 end
 best_val = SG.A[best_single_row].values[searchsortedfirst(SG.A[best_single_row].pos, best_col)]
 #TODO: if best_row not changed (zerodiv), use jlight as input
 val = SG.A[row_idx].values[searchsortedfirst(SG.A[row_idx].pos, best_col)]
 @assert !iszero(val)
 fl, tmp = divides(val, best_val)
 if fl #best_val divides val
  tmp = neg!(tmp)
  SG.A.nnz -= length(SG.A[row_idx])
  SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp)
  SG.A.nnz += length(SG.A[row_idx])
 else
  fl, tmp = divides(best_val, val)
  if fl #val divides best_val
   SG.A.nnz -= length(SG.A[row_idx])
   tmp = neg!(tmp)
   scale_row!(SG.A, row_idx, tmp)
   tmp = one!(tmp)
   SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp)
   SG.A.nnz += length(SG.A[row_idx])
  else
   g, a_best, a_row = gcdx(best_val, val)
   val_red = div(val, g)
   val_red = neg!(val_red)
   best_val_red = div(best_val, g)
   SG.A.nnz -= length(SG.A[row_idx])
   Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], SG.R(1), tmp, val_red, best_val_red)
   SG.A.nnz += length(SG.A[row_idx])
  end
 end
 return SG
end

function add_to_eliminate_field!(L_row::Int64, row_idx::Int64, best_row::SRow{T}, best_col::Int64, best_val::FieldElem, SG::data_StructGauss)::data_StructGauss where T <: FieldElem
 @assert L_row in SG.col_list[best_col]
 @assert !(0 in SG.A[row_idx].values)
 val = SG.A[row_idx, best_col]
 @assert !iszero(val)
 @assert L_row in SG.col_list[best_col]
 for c in SG.A[row_idx].pos
  @assert !isempty(SG.col_list[c])
  if SG.is_light_col[c]
   jj = findfirst(isequal(L_row), SG.col_list[c])
   deleteat!(SG.col_list[c], jj)
  end
 end
 @assert !(0 in SG.A[row_idx].values)
 SG.A.nnz -= length(SG.A[row_idx])
 Hecke.add_scaled_row!(best_row, SG.A[row_idx], -val)
 SG.A.nnz += length(SG.A[row_idx])
 @assert iszero(SG.A[row_idx, best_col])
 return SG
end

function update_after_addition!(L_row::Int64, row_idx::Int64, best_col::Int64, SG::data_StructGauss)::data_StructGauss
 SG.light_weight[row_idx] = 0
 for c in SG.A[row_idx].pos
  @assert c != best_col
  if SG.is_light_col[c]
    insert!(SG.col_list[c], searchsortedfirst(SG.col_list[c], L_row), L_row)
    SG.light_weight[row_idx]+=1
  end
 end
 return SG
end

################################################################################
#
#  Small Auxiliary Functions
#
################################################################################

function swap_entries(v::Vector{Int64}, i::Int64, j::Int64)
 v[i],v[j] = v[j],v[i]
end

function swap_rows_perm(i::Int64, j, SG::data_StructGauss)
 if i != j
  swap_rows!(SG.A, i, j)
  swap_entries(SG.pivot_col, i, j)
  swap_entries(SG.col_list_perm, i, j)
  swap_entries(SG.col_list_permi, SG.col_list_perm[i], SG.col_list_perm[j])
  swap_entries(SG.light_weight, i, j)
 end
end 

function swap_i_into_base(i::Int64, SG::data_StructGauss)
 if i < SG.single_row_limit
  swap_rows_perm(i, SG.base, SG)
 else
   if i != SG.single_row_limit 
    swap_rows_perm(SG.base, SG.single_row_limit, SG)
   end
   SG.single_row_limit +=1
   swap_rows_perm(SG.base, i, SG)
 end
end

function find_light_entry(position_array::Vector{Int64}, is_light_col::Vector{Bool})::Int64
 for idx in 1:length(position_array)
   is_light_col[position_array[idx]] && return idx
 end
end

function move_into_Y(i::Int64, SG::data_StructGauss)
 @assert i == SG.base
 push!(SG.Y, deepcopy(SG.A[SG.base]))
 for base_c in SG.A[SG.base].pos
  @assert !SG.is_light_col[base_c]
  @assert !isempty(SG.col_list[base_c])
 end
 SG.A.nnz-=length(SG.A[SG.base])
 empty!(SG.A[SG.base].pos), empty!(SG.A[SG.base].values)
end

################################################################################
#
#  Kernel Computation
#
################################################################################

#Compute the kernel corresponding to the non echolonized part from above and
#insert backwards using the triangular part to get the full kernel.

function compute_kernel(SG, with_light = true)
 Hecke.update_light_cols!(SG)
 @assert SG.nlight > -1
 Hecke.collect_dense_cols!(SG)
 _nullity, _dense_kernel = Hecke.dense_kernel(SG)
 l, K = Hecke.init_kernel(_nullity, _dense_kernel, SG, with_light)
 return compose_kernel(l, K, SG)
end

function compute_kernel_field(SG, with_light = true)
 update_light_cols!(SG)
 @assert SG.nlight > -1
 collect_dense_cols!(SG)
 _nullity, _dense_kernel = dense_kernel(SG)
 l, K = init_kernel(_nullity, _dense_kernel, SG, with_light)
 return compose_kernel_field(l, K, SG)
end

function update_light_cols!(SG)
 for i = 1:ncols(SG.A)
  if SG.is_light_col[i] && !isempty(SG.col_list[i])
   SG.is_light_col[i] = false
   SG.nlight -= 1
  end
 end
 return SG
end

function collect_dense_cols!(SG)
 m = ncols(SG.A)
 nheavy = m - SG.nlight - SG.npivots
 j = 1
 for i = 1:m
  if !SG.is_light_col[i] && !SG.is_pivot_col[i]
   SG.heavy_map[i] = j
   push!(SG.heavy_mapi,i)
   j+=1
  end
 end
 @assert length(SG.heavy_mapi)==nheavy
 return
end

function dense_kernel(SG)
 ST = sparse_matrix(base_ring(SG.A), 0, nrows(SG.Y))
 YT = transpose(delete_zero_rows!(SG.Y))
 for j in SG.heavy_mapi
  push!(ST, YT[j])
 end
 S = transpose(ST)
 d, _dense_kernel = nullspace(matrix(S))
 return size(_dense_kernel)[2], _dense_kernel
end

function init_kernel(_nullity, _dense_kernel, SG, with_light=false)
 R = base_ring(SG.A)
 m = ncols(SG.A)
 if with_light
  l = _nullity+SG.nlight
 else
  l = _nullity
 end
 M = matrix_space(R, m, l)
 K = M()
 #initialisation
 ilight = 1
 for i = 1:m
  if SG.is_light_col[i]
   if with_light
    @assert ilight <= SG.nlight
    K[i, _nullity+ilight] = one(R)
    ilight +=1
   end
  else
   j = SG.heavy_map[i]
   if j>0
    for c = 1:_nullity
     K[i,c] = _dense_kernel[j, c]
    end
   end
  end
 end
 return l, K
end

function compose_kernel(l, K, SG)
 R = base_ring(SG.A)
 n = nrows(SG.A)
 for i = n:-1:1
  c = SG.pivot_col[i]
  if c>0
   x = R(0)
   y = zeros(R,l)
   for idx in 1:length(SG.A[i])
    cc = SG.A[i].pos[idx]
    xx = SG.A[i].values[idx]
    if cc == c
     x = xx
    else
     for k = 1:l
      kern_c = K[cc,k]
      !iszero(kern_c) && (y[k]-=xx*kern_c)
     end
    end
   end
   for k = 1:l
    x_inv = try
     inv(x)
    catch
     R(0)
    end
    if iszero(x_inv)
     K[:,k] *= x
     K[c, k] = y[k]
    else
     K[c, k] = y[k]*x_inv
    end
   end
  end
 end
 return l, K
end

function compose_kernel_field(l, K, SG)
 R = base_ring(SG.A)
 n = nrows(SG.A)
 for i = n:-1:1
  c = SG.pivot_col[i]
  if c>0
   y = zeros(R,l)
   for idx in 1:length(SG.A[i])
    cc = SG.A[i].pos[idx]
    xx = SG.A[i].values[idx]
    if cc == c
     @assert isone(xx)
    else
     for k = 1:l
      kern_c = K[cc,k]
      !iszero(kern_c) && (y[k]-=xx*kern_c)
     end
    end
   end
   for k = 1:l
    K[c, k] = y[k]
   end
  end
 end
 return l, K
end

function delete_zero_rows!(A::SMat{T}) where T
  for i=A.r:-1:1
    if isempty(A[i].pos)
      deleteat!(A.rows, i)
      A.r-=1
    end
  end
  return A
end


#TODO: combine field and ring version
#TODO: make computation kernel in compute_kernel faster
