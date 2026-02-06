mutable struct data_StructGauss{T}
 A::SMat{T}
 Y::SMat{T}
 R::T #correct type declaration?
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
  )
 end
end

mutable struct data_Det
 scaling #tracks scaling -> divide det by product in the end
 divisions #tracks divisions -> multiply det by product
 content #tracks reduction of polys by content -> multiply det by prod
 pivprod #product of pivot elements
 npiv #number of pivots
 function data_Det(R, _det=false)
  if _det
   return new(one(R), one(R), one(coefficient_ring(R)), one(R), 1)
  else
   return new(zero(R), zero(R), zero(coefficient_ring(R)), zero(R), 0)
  end
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

################################################################################
#
#  Partial Echolonization
#
################################################################################

#Build an upper triangular matrix for as many columns as possible compromising
#the loss of sparsity during this process.

function part_echelonize!(A::SMat{T}, _det=false; pivbound=ncols(A), trybound=ncols(A))::Tuple{data_StructGauss{ZZPolyRingElem}, data_Det} where T <: RingElem
 A = delete_zero_rows!(A)
 n = nrows(A)
 m = ncols(A)
 SG = data_StructGauss(A)
 single_rows_to_top!(SG)

 Det=Hecke.data_Det(base_ring(A), _det)

 t = ncols(SG.A) - trybound
 while SG.nlight > 0 && SG.base <= n
  build_part_ref!(SG, _det)
  #@show SG.npivots, SG.nlight
  (SG.npivots >= pivbound || t >= SG.nlight) && break
  (SG.nlight == 0 || SG.base > n) && break
  best_single_row = find_best_single_row(SG)
  best_single_row < 0 && @assert(SG.base == SG.single_row_limit)
  
  if best_single_row < 0
   mark_col_as_dense(SG)
   continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end
  eliminate_and_update2!(best_single_row, SG, Det)
 end
 return SG, Det
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

function build_part_ref!(SG::data_StructGauss, _det::Bool)
 queue = collect(ncols(SG.A):-1:1)
 while !isempty(queue)
  queue_new = Int[]
  for j in queue
   if length(SG.col_list[j])==1 && SG.is_light_col[j]
    singleton_row_origin = only(SG.col_list[j])
    singleton_row_idx = SG.col_list_permi[singleton_row_origin]
    @assert !iszero(SG.A[singleton_row_idx, j])
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
    _det && Det.pivprod*=SG.A[singleton_row_idx, j]#improve?
    SG.nlight-=1
    SG.npivots+=1
    swap_i_into_base(singleton_row_idx, SG)
    SG.base+=1
   end
  end
  queue = queue_new
 end
end

# first prio: 1 as pivot entry
# second prio: length of row
function find_best_single_row(SG::data_StructGauss{ZZRingElem})::Int64
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

#prio: shortest row
function find_best_single_row(SG::data_StructGauss{<:FieldElem})::Int64
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

#doc: Marks rightmost light column with most entries as dense.

#TODO: check for additional criteria like entry size?
function mark_col_as_dense(SG::data_StructGauss)
 dense_col_idx = 0
 dense_col_len = 0
 for i = ncols(SG.A):-1:1
  if SG.is_light_col[i]
   if length(SG.col_list[i]) > dense_col_len
    dense_col_len = length(SG.col_list[i])
    dense_col_idx = i
   end
  end
 end
 SG.is_light_col[dense_col_idx] = false
 marked_col = SG.col_list[dense_col_idx]
 for i_origin in marked_col
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
  #println("Case1")
  swap_i_into_base(i, SG)
  SG.pivot_col[SG.base] = 0
  move_into_Y(SG.base, SG)
  SG.base+=1
 elseif w == 1
  #println("Case2")
  if i > SG.single_row_limit
   swap_rows_perm(i, SG.single_row_limit, SG)
  end
  SG.single_row_limit += 1
 elseif SG.base <= i < SG.single_row_limit #TODO: check if necessary
  #println("Case3")
  swap_rows_perm(i, SG.single_row_limit-1, SG)
  SG.single_row_limit-=1
 end
 return SG
end

function eliminate_and_update!(best_single_row::Int64, SG::data_StructGauss{T}, Det::data_Det)::data_StructGauss{T}
 @assert !iszero(best_single_row)
 L_best = deepcopy(SG.col_list_perm[best_single_row])
 #L_best == 85 && @show SG.A[best_single_row].pos
 light_idx = find_light_entry(SG.A[best_single_row].pos, SG.is_light_col)
 best_col = SG.A[best_single_row].pos[light_idx]
 #@show L_best, best_col
 @assert length(SG.col_list[best_col]) > 1
 best_val = SG.A[best_single_row].values[light_idx] #test
 @assert !iszero(best_val) #test
 row_idx = 0
 while length(SG.col_list[best_col]) > 1
  best_single_row = SG.col_list_permi[L_best]
  row_idx = find_row_to_add_on2(best_single_row, best_col, SG)
  @assert row_idx > 0
  L_row = SG.col_list_perm[row_idx]
  @assert L_row != L_best
  @assert SG.col_list_perm[best_single_row] == L_best #test
  add_to_eliminate!(L_row, row_idx, best_single_row, best_col, SG, Det)
  #g = gcd(SG.A[row_idx].values)
  #Det.divisions*=g
  #SG.A[row_idx].values./=g
  @assert iszero(SG.A[row_idx, best_col])
  @assert SG.col_list_perm[best_single_row] == L_best #test
  update_after_addition2!(L_row, row_idx, best_col, SG)
  #TODO: divide (row_idx) by gcd and test time diff
  @assert SG.col_list_perm[best_single_row] == L_best #test
  #@show L_row
  #test_col_list(SG) #FAILS
  for i in 1:length(SG.col_list) #test works
    C = SG.col_list[i]
    if SG.is_light_col[i]
     L_best in C && @assert SG.A[best_single_row, i] != 0
    end
  end
  handle_new_light_weight!(row_idx, SG)
 end
 return SG
end

function update_after_addition!(L_row::Int64, row_idx::Int64, best_col::Int64, SG::data_StructGauss)::data_StructGauss
 @assert L_row == SG.col_list_perm[row_idx]
 @assert !(0 in SG.A[row_idx].values)
 SG.light_weight[row_idx] = 0
 for c_idx in 1:length(SG.A[row_idx].pos)
  c = SG.A[row_idx].pos[c_idx]
  @assert c != best_col
  @assert SG.A[row_idx].values[c_idx] != 0
  if SG.is_light_col[c]
   insert!(SG.col_list[c], searchsortedfirst(SG.col_list[c], L_row), L_row)
   SG.light_weight[row_idx]+=1
  end
 end
 return SG
end

function find_row_to_add_on(best_single_row::Int64, best_col::Int64, SG::data_StructGauss)::Int64
 row_idx = 0
 for L_row in SG.col_list[best_col][end:-1:1]
  row_idx = SG.col_list_permi[L_row]
  row_idx == best_single_row && continue #TODO: work with origin idces here
  @assert SG.base <= row_idx
  break
 end
 return row_idx
end

function add_to_eliminate!(L_row::Int64, row_idx::Int64, best_single_row::Int64, best_col::Int64, SG::data_StructGauss, Det::data_Det)::data_StructGauss
 L_best = SG.col_list_perm[best_single_row]
 @assert L_row in SG.col_list[best_col]
 @assert L_best != L_row
 @assert L_row == SG.col_list_perm[row_idx] #test
 @assert !(0 in SG.A[row_idx].values)
 #test_col_list(SG)
 for c in SG.A[row_idx].pos 
  @assert !isempty(SG.col_list[c]) #TODO: check why empty dense cols exist
  if SG.is_light_col[c]
   jj = searchsortedfirst(SG.col_list[c], L_row)
   @assert SG.col_list[c][jj] == L_row
   deleteat!(SG.col_list[c], jj)
  end
 end
 best_val = SG.A[best_single_row].values[searchsortedfirst(SG.A[best_single_row].pos, best_col)]
 #TODO: if best_row not changed (zerodiv), use jlight as input
 val = SG.A[row_idx].values[searchsortedfirst(SG.A[row_idx].pos, best_col)]
 @assert !iszero(val)
 fl, tmp = divides(val, best_val)
 if fl #best_val divides val
  #println("add Case1, $fl, $tmp")
  tmp = neg!(tmp)
  SG.A.nnz -= length(SG.A[row_idx])
  SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp)
  SG.A.nnz += length(SG.A[row_idx])
  @assert iszero(SG.A[row_idx, best_col])
 else
  fl, tmp = divides(best_val, val)
  if fl #val divides best_val
   #println("add Case2, $fl, $tmp")
   SG.A.nnz -= length(SG.A[row_idx])
   tmp = neg!(tmp)
   scale_row!(SG.A, row_idx, tmp)
   Det.scaling *= tmp
   tmp = one!(tmp)
   SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp)
   SG.A.nnz += length(SG.A[row_idx])
   @assert iszero(SG.A[row_idx, best_col])
  else
   #println("add Case3, $fl, $tmp")
   zero!(tmp)
   g = gcd(best_val, val)
   #TODO: find out why gcdx so slow
   val_red = div(val, g)
   val_red = neg!(val_red)
   best_val_red = div(best_val, g)
   SG.A.nnz -= length(SG.A[row_idx])
   #@show SG.A[best_single_row]
   Hecke.transform_row!(SG.A, best_single_row, row_idx, SG.R(1), tmp, val_red, best_val_red)
   Det.scaling*=best_val_red
   #@show SG.A[best_single_row]
   #TODO: write transform_rows for rows
   SG.A.nnz += length(SG.A[row_idx])
   @assert iszero(SG.A[row_idx, best_col])
   @assert !iszero(SG.A[best_single_row, best_col])
   @assert L_best != SG.col_list_perm[row_idx]
  end
 end
 return SG
end

################################################################################
#
#  Small Auxiliary Functions
#
################################################################################

#allTypes

function delete_zero_rows!(A::SMat{T}) where T
  filter!(!isempty, A.rows)
  A.r = length(A.rows)
  return A
end

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
 position_array[findfirst(is_light_col)]
end

function move_into_Y(i::Int64, SG::data_StructGauss)
 @assert i == SG.base
 push!(SG.Y, deepcopy(SG.A[SG.base]))
 #assert
 for base_c in SG.A[SG.base].pos
  @assert !SG.is_light_col[base_c]
  @assert !isempty(SG.col_list[base_c])
 end#
 SG.A.nnz-=length(SG.A[SG.base])
 empty!(SG.A[SG.base].pos), empty!(SG.A[SG.base].values)
end
