#TODO: declare return types
#TODO: sizehints
#TODO: pointer pointer pointer
#TODO: sizehint for heavy stuff can be given later, so don't initialize immediately
#TODO: new struct for second part
#TODO: use divides false, y to reduce elements

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
 function data_Det(R)
  return new(one(R), one(R), one(coefficient_ring(R)), one(R), 1)
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

function part_echelonize!(A::SMat{T}, Det=Hecke.data_Det(base_ring(A)); pivbound=ncols(A), trybound=ncols(A))::Tuple{data_StructGauss{ZZPolyRingElem}, data_Det} where T <: RingElem
 A = delete_zero_rows!(A)
 n = nrows(A)
 m = ncols(A)
 SG = data_StructGauss(A)
 single_rows_to_top!(SG)
 #=
 for i = 1:n
  g = gcd(SG.A[i].values)
  Det.divisions*=g
  SG.A[i].values./=g
 end
 =#
 t = ncols(SG.A) - trybound
 while SG.nlight > 0 && SG.base <= n
  build_part_ref!(SG, Det)
  #@show SG.npivots, SG.nlight
  (SG.npivots > pivbound || t > SG.nlight) && break
  for i = 1:m
   SG.is_light_col[i] && @assert length(SG.col_list[i]) != 1
  end
  (SG.nlight == 0 || SG.base > n) && break
  best_single_row = find_best_single_row(SG)
  best_single_row < 0 && @assert(SG.base == SG.single_row_limit)
  
  if best_single_row < 0
   turn_heavy(SG)
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

function build_part_ref!(SG::data_StructGauss, Det::data_Det)
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
    Det.pivprod*=SG.A[singleton_row_idx, j]#improve?
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

function eliminate_and_update2!(best_single_row::Int64, SG::data_StructGauss, Det::data_Det)::data_StructGauss
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
  add_to_eliminate2!(L_row, row_idx, best_single_row, best_col, SG, Det)
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
   #=
  r = SG.col_list_permi[L_best]
 
  @show r == best_single_row
  
  for i in 1:length(SG.col_list) #test works
    C = SG.col_list[i]
    if SG.is_light_col[i]
     L_best in C && @assert SG.A[best_single_row, i] !=0
    end
  end
  =# #TODO: check case where r != best_single_row
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

function add_to_eliminate2!(L_row::Int64, row_idx::Int64, best_single_row::Int64, best_col::Int64, SG::data_StructGauss, Det::data_Det)::data_StructGauss
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

function update_after_addition2!(L_row::Int64, row_idx::Int64, best_col::Int64, SG::data_StructGauss)::data_StructGauss
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

mutable struct data_Kernel
 heavy_mapi::Vector{Int64}
 heavy_map::Vector{Int64}

 function data_Kernel(SG::data_StructGauss, nheavy::Int64)
  return new(
  sizehint!(Int[], nheavy),
  fill(0, ncols(SG.A))
  )
 end
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

function collect_dense_cols2!(SG)
 m = ncols(SG.A)
 nheavy = m - SG.nlight - SG.npivots
 KER = data_Kernel(SG, nheavy)
 j = 1
 for i = 1:m
  if !SG.is_light_col[i] && !SG.is_pivot_col[i]
   KER.heavy_map[i] = j
   push!(KER.heavy_mapi, i)
   j+=1
  end
 end
 @assert length(KER.heavy_mapi) == nheavy
 return KER
end

function dense_matrix(SG, KER) #with Y
 D = zero_matrix(SG.R, nrows(SG.A) - SG.npivots, length(KER.heavy_mapi))
	 for i in 1:length(SG.Y)
	  for j in 1:length(KER.heavy_mapi)
    D[i,j]=SG.Y[i, KER.heavy_mapi[j]]
	   #setindex!(D, SG.Y[i], i, j, KER.heavy_mapi[j])
	  end
	 end
 return D
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


################################################################################
#
#  Determinant
#
################################################################################

function collect_pivots(SG, pivprod = one(SG.R))
 _count = 0
 while _count < SG.npivots
  for i = 1:nrows(SG.A)
   c = SG.pivot_col[i]
   if c > 0
    pivprod *= SG.A[i,c] #improve
    _count +=1
   end
  end
 end
 return pivprod
end

function extract_matrix(SG, Det)
 m, n = ncols(SG.A), nrows(SG.A)
 Det.npiv += SG.npivots
 c = m - SG.npivots
 heavy_mapi = sizehint!(Int[], c)
 heavy_map = zeros(Int, m)
 j = 1
 for i = 1:m
  if !SG.is_pivot_col[i]
   heavy_map[i] = j
   push!(heavy_mapi, i)
   j+=1
  end
 end
 @assert length(heavy_mapi) == c
 M = sparse_matrix(SG.R, 0, c)
 rowdeg = 0
 coldeg = zeros(Int, c)
 for i in SG.base:nrows(SG.A)
  g = gcd(SG.A[i].values)
  c = content(g)
  gred = divexact(g,c)
  SG.A[i].values./=g
  Det.divisions *= gred
  Det.content *= c
  _pos = sizehint!(Int[], length(SG.A[i].pos))
  rdeg = 0
  for j = 1:length(SG.A[i])
   x = heavy_map[SG.A[i].pos[j]]
   d = degree(SG.A[i].values[j])
   (d > coldeg[x]) && (coldeg[x] = d)
   (d > rdeg) && (rdeg = d)
   push!(_pos, x)
  end
  rowdeg += rdeg
  #_pos = [heavy_map[x] for x in SG.A[i].pos]
  @assert length(_pos) == length(SG.A[i])
  push!(M, sparse_row(SG.R, _pos, SG.A[i].values))
 end
 for i in 1:length(SG.Y)
  g = gcd(SG.Y[i].values)
  c = content(g)
  gred = divexact(g,c)
  SG.Y[i].values./=g
  Det.divisions *= gred
  Det.content *= c
  _pos = sizehint!(Int[], length(SG.Y[i].pos))
  rdeg = 0
  for j = 1:length(SG.Y[i])
   x = heavy_map[SG.Y[i].pos[j]]
   d = degree(SG.Y[i].values[j])
   (d > coldeg[x]) && (coldeg[x] = d)
   (d > rdeg) && (rdeg = d)
   push!(_pos, x)
  end
  rowdeg += rdeg
  #_pos = [heavy_map[x] for x in SG.Y[i].pos]
  @assert length(_pos) == length(SG.Y[i])
  push!(M, sparse_row(SG.R, _pos, SG.Y[i].values))
 end
 return M, max(rowdeg, sum(coldeg)), Det
end

function det_iter(A::SMat{T}, pbound) where T <: RingElem
 Det=Hecke.data_Det(base_ring(A))
 while true
  SG, Det = part_echelonize!(A, Det, pivbound = pbound)
  A, _, Det = extract_matrix(SG, Det)
  SG.npivots<pbound && break
 end
 return A, Det
end

function compute_det(A, Det)
 D = matrix(A)
 d = det(A)
 d*=Det.divisions;
 d*=Det.content;
 d*=Det.pivprod;
 d=div(d, Det.scaling);
 return d
end

function reduce_max(A)
 SG, Det = part_echelonize!(A)
 s = Det.scaling
 d = SG.R(1)
 KER = Hecke.collect_dense_cols2!(SG)
 D = Hecke.dense_matrix(SG, KER)
 _pivots = collect_pivots(SG)
 for i = 1:5
  A = sparse_matrix(D)
  SG, Det = part_echelonize!(A)
  g = gcd(Det.scaling, Det.divisions)
  s*=div(Det.scaling, g)
  d*=div(Det.divisions, g)
  @show SG.npivots, degree(Det.scaling)
  _pivots = collect_pivots(SG, _pivots)
  KER = Hecke.collect_dense_cols2!(SG)
  D = Hecke.dense_matrix(SG, KER)
  for i = 1:size(D)[1]
   g = gcd(D[i,:])
   d *= g
   D[i, :]./=g 
  end
 end
 return _pivots, s, d, D
end

################################################################################
#
#  Tests
#
################################################################################

function test_col_list(SG)
 T = transpose(SG.A)
 
 for j in 1:SG.A.c
  if SG.is_light_col[j]
   @assert issorted(SG.col_list[j])
   S = sort!([SG.col_list_perm[k] for k in T[j].pos])
   if S != SG.col_list[j]
    s = setdiff(S, SG.col_list[j])[1] #
    @show j, s, S, SG.col_list[j], SG.A[SG.col_list_permi[s],j], SG.A[SG.col_list_permi[59],j]
    idx = searchsortedfirst(SG.A[SG.col_list_permi[s]].pos, j)
    _row = SG.A[SG.col_list_permi[s]]
    @show idx, _row.pos, _row.values[idx], iszero(_row.values[idx])#.values[idx]
   end
   @assert S == SG.col_list[j]
  end
 end
end

function test_col_list2(SG, L_row)
 T = transpose(SG.A)
 for j in 1:SG.A.c
  if SG.is_light_col[j]
   S = sort!([SG.col_list_perm[k] for k in T[j].pos])
   @assert S == SG.col_list[j] || setdiff(S, SG.col_list[j])[1] == L_row
  end
 end
end