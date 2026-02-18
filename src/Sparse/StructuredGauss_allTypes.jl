#TODO: input/output types and return
#important types: ZZ, Fq (small q), Z/nZ (n arb. large)


#=
add_verbosity_scope(:StructGauss)
set_verbosity_level(:StructGauss, 1)

add_assertion_scope(:StructGauss)
set_assertion_level(:StructGauss, 1)
=#

mutable struct data_StructGauss{T}
 A::SMat{T}
 Y::SMat{T}
 R::Ring #TODO: type declaration
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
 unimodular_trafos::Bool

 function data_StructGauss(A::SMat{T}, unimodular_trafos::Bool) where T <: RingElem
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
  unimodular_trafos,
  )
 end
end

mutable struct data_Det
 scaling #tracks scaling -> divide det by product in the end
 divisions #tracks divisions -> multiply det by product
 sign #tracks swaps -> multiply det by -1 or do nothing
 #content #tracks reduction of polys by content -> multiply det by prod
 pivprod #product of pivot elements
 npiv #number of pivots
 function data_Det(R, _det::Bool)
  if _det
   return new(one(R), one(R), one(R), one(R), 0)
  else
   return new(zero(R), zero(R), zero(R), zero(R), -1)
  end
 end
end

function _col_list(A::SMat{<:RingElem})::Vector{Vector{Int64}}
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

function part_echelonize!(A::SMat{T}, _det=false, unimodular_trafos = false; pivbound=ncols(A), trybound=ncols(A))::Tuple{data_StructGauss{T}, data_Det} where T <: RingElem
 A = delete_zero_rows!(A) #TODO: track number or move into base
 n = nrows(A)
 m = ncols(A)
 SG = data_StructGauss(A, unimodular_trafos)
 Det = Hecke.data_Det(base_ring(A), _det)
 single_rows_to_top!(SG, Det)

 t = ncols(SG.A) - trybound
 while SG.nlight > 0 && SG.base <= n
  build_part_ref!(SG, Det)
  
  (SG.npivots >= pivbound || t >= SG.nlight) && break
  (SG.nlight == 0 || SG.base > n) && break
  best_single_row, best_col_idx = find_best_single_row(SG)
  best_single_row == 0 && @assert(SG.base == SG.single_row_limit)
  
  if best_single_row == 0
   mark_col_as_dense(SG, Det)
   continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end
  eliminate_and_update!(best_single_row, best_col_idx, SG, Det)
  for i = SG.base:SG.single_row_limit-1 #test
   test_light_weight(i, SG)
   @assert SG.light_weight[i] == 1
  end
 end
 return SG, Det
end

#assertions removed
function single_rows_to_top!(SG::data_StructGauss{T}, Det::data_Det)::data_StructGauss{T} where T<:RingElem
 for i = 1:nrows(SG.A)
  if length(SG.A[i]) == 1
   swap_rows_perm(i, SG.single_row_limit, SG, Det)
   SG.single_row_limit +=1
  end
 end
 return SG
end

function build_part_ref!(SG::data_StructGauss{<:RingElem}, Det::data_Det)
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
    if Det.npiv > -1
     mul!(Det.pivprod, Det.pivprod, SG.A[singleton_row_idx, j])
    end
    SG.nlight-=1
    SG.npivots+=1
    swap_i_into_base(singleton_row_idx, SG, Det)
    SG.base+=1
   end
  end
  queue = queue_new
 end
end

#find_best_single_row (type dependent)
#TODO: avoid copy-paste
#TODO: rename to find_elimination_pivot_row

# first prio: 1 as pivot entry
# second prio: length of row
function find_best_single_row(SG::data_StructGauss{ZZRingElem})::Tuple{Int64, Int64}
 best_single_row = 0
 best_len = 0
 best_is_one = false
 single_row_val = ZZ(0)
 best_col_idx = 0
 for i = SG.base:SG.single_row_limit-1
  single_row = SG.A[i]
  single_row_len = length(single_row)
  SG.light_weight[i] != 1 && (@show SG.col_list_perm[i])
  @assert SG.light_weight[i] == 1
  light_idx = find_light_entry(single_row.pos, SG.is_light_col)
  single_row_val = getindex!(single_row_val, SG.A[i].values, light_idx)
  is_one = is_unit(single_row_val)
  if best_single_row == 0 || (is_one == best_is_one && single_row_len < best_len)
   best_single_row = i
   best_len = single_row_len
   best_is_one = is_one
   best_col_idx = light_idx
  elseif !best_is_one && is_one
   best_single_row = i
   best_len = single_row_len
   best_is_one = true
   best_col_idx = light_idx
  end
 end
 return best_single_row, best_col_idx
end

#prio: shortest row
function find_best_single_row(SG::data_StructGauss{<:FinFieldElem})::Tuple{Int64, Int64}
 best_single_row = 0
 best_len = 0
 for i = SG.base:SG.single_row_limit-1
  single_row = SG.A[i]
  single_row_len = length(single_row)
  w = SG.light_weight[i]
  @assert w == 1
  if best_single_row == 0 || single_row_len < best_len
   best_single_row = i
   best_len = single_row_len
  end
 end
 return best_single_row, find_light_entry(best_single_row.pos, SG.is_light_col)
end

#entry size not relevant
#prio: first length or first one? TODO: test
#for now:
#1st prio: 
function find_best_single_row(SG::data_StructGauss{zzModRingElem})::Int64
 best_single_row = 0
 best_col = 0
 best_val = SG.R(0)
 best_len = 0
 best_is_one = false
 for i = SG.base:SG.single_row_limit-1
  #TODO
 end
 return best_single_row
end

#entry size is relevant
function find_best_single_row(SG::data_StructGauss{ZZModRingElem})::Int64
 best_single_row = 0
 best_col = 0
 best_val = SG.R(0)
 best_len = 0
 best_is_one = false
 for i = SG.base:SG.single_row_limit-1
  single_row = SG.A[i]
  single_row_len = length(single_row)
  w = SG.light_weight[i]
  !isone(w) && @show w, i, SG.col_list_perm[i]
  @assert w == 1
  light_idx = find_light_entry(single_row.pos, SG.is_light_col)
  j_light = single_row.pos[light_idx]
  single_row_val = SG.A[i].values[light_idx]
  @assert length(SG.col_list[j_light]) > 1
  is_one = single_row_val.data == 1 #|| single_row_val.data == R.n-1#TODO
  if best_single_row == 0
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
   #TODO: merge with first condition
  elseif (is_one == best_is_one && single_row_len < best_len) #TODO: first part unnecessary?
   best_single_row = i
   best_col = j_light
   best_len = single_row_len
   best_is_one = is_one
   best_val = single_row_val
  end
 end
 return best_single_row
end

#doc: Marks rightmost light column with most entries as dense.

#TODO: check for additional criteria like entry size?
function mark_col_as_dense(SG::data_StructGauss, Det::data_Det)
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
  handle_new_light_weight!(i_current, SG, Det)
 end
 SG.nlight -= 1
end

#unimodular: light_weight can increase! -> swap out of single_row area
function handle_new_light_weight!(i::Int64, SG::data_StructGauss, Det::data_Det)::data_StructGauss
 w = SG.light_weight[i]
 if w == 0
  @vprintln :StructGauss "Case1 (weight)"
  swap_i_into_base(i, SG, Det)
  SG.pivot_col[SG.base] = 0
  move_into_Y(SG.base, SG)
  SG.base+=1
 elseif w == 1
  @vprintln :StructGauss "Case2 (weight)"
  if i > SG.single_row_limit
   swap_rows_perm(i, SG.single_row_limit, SG, Det)
   SG.single_row_limit += 1
  end
 elseif SG.base <= i < SG.single_row_limit
  #unimodular: light_weight can increase! -> swap out of single_row area
  @vprintln :StructGauss "Case3 (weight)"
  swap_rows_perm(i, SG.single_row_limit-1, SG, Det)
  SG.single_row_limit-=1
 end
 return SG
end

#best_single_row = row to eliminate with (next pivot row)
function eliminate_and_update!(best_single_row::Int64, best_col_idx::Int64, SG::data_StructGauss, Det::data_Det)::data_StructGauss
 @assert !iszero(best_single_row)
 L_best = deepcopy(SG.col_list_perm[best_single_row]) #old index 
 best_col = SG.A[best_single_row].pos[best_col_idx] #col idx of elim-piv in matrix
 @assert length(SG.col_list[best_col]) > 1
 best_val = SG.R(0) #TODO: tmp?
 row_idx = 0
 while length(SG.col_list[best_col]) > 1
  best_single_row = SG.col_list_permi[L_best]
  #best_col_idx might change when scaling causes zeroes in Z/nZ
  best_val = getindex!(best_val, SG.A[best_single_row].values, best_col_idx)

  #Find row to add to
  @vprintln :StructGauss "before find"
  L_row, row_idx = find_row_to_add_on(L_best, best_col, SG)
  @vprintln :StructGauss "after find"
  @assert SG.base <= row_idx != best_single_row

  best_col_idx, SG = add_to_eliminate!(L_row, row_idx, L_best, best_single_row, best_col, best_col_idx, best_val, SG, Det)
  #g = gcd(SG.A[row_idx].values)
  #Det.divisions*=g
  #SG.A[row_idx].values./=g
  @assert iszero(SG.A[row_idx, best_col])
  @assert L_row !=L_best
  update_after_addition!(L_row, row_idx, SG)
  @vprintln :StructGauss "after update"
  #TODO: divide (row_idx) by gcd and test time diff
  #test_col_list(SG) #FAILS
  SG.unimodular_trafos && handle_new_light_weight!(best_single_row, SG, Det) #TODO: necessary?
  handle_new_light_weight!(row_idx, SG, Det)
  @vprintln :StructGauss "after weight"
 end
 return SG
end

#TODO: update best_row in Z/nZ case (new zeros might appear by scaling)
#TODO: update best_row after transform with gcd
function update_after_addition!(L_row::Int64, row_idx::Int64, SG::data_StructGauss)::data_StructGauss
 @assert L_row == SG.col_list_perm[row_idx]
 @assert !(0 in SG.A[row_idx].values)
 SG.light_weight[row_idx] = 0
 for c_idx in 1:length(SG.A[row_idx].pos)
  c = SG.A[row_idx].pos[c_idx]
  #@assert c != best_col
  @assert SG.A[row_idx].values[c_idx] != 0
  if SG.is_light_col[c]
   insert!(SG.col_list[c], searchsortedfirst(SG.col_list[c], L_row), L_row)
   SG.light_weight[row_idx]+=1
  end
 end
 return SG
end

#uses old indicies
function find_row_to_add_on(L_best::Int64, best_col::Int64, SG::data_StructGauss)::Tuple{Int64, Int64}
 for L_row in SG.col_list[best_col][end:-1:1] #findlast
  L_row == L_best && continue
  row_idx = SG.col_list_permi[L_row]
  @assert SG.base <= row_idx
  return L_row, row_idx
 end
end

function add_to_eliminate!(L_row::Int64, row_idx::Int64, L_best::Int64, best_single_row::Int64, best_col::Int64, best_col_idx::Int64, best_val::ZZRingElem, SG::data_StructGauss{ZZRingElem}, Det::data_Det)::Tuple{Int64, data_StructGauss{ZZRingElem}}
 for c in SG.A[row_idx].pos 
  @assert !isempty(SG.col_list[c]) #TODO: check why empty dense cols exist
  if SG.is_light_col[c]
   jj = searchsortedfirst(SG.col_list[c], L_row)#or searchsortedlast?
   @assert SG.col_list[c][jj] == L_row
   deleteat!(SG.col_list[c], jj)
  end
 end

 tmpa = Hecke.get_tmp(SG.A)
 tmpb = Hecke.get_tmp(SG.A)
 tmp, g, a_best, a_row, best_val, val = tmp_scalar = Hecke.get_tmp_scalar(SG.A, 6)
 
 best_val = getindex!(best_val, SG.A[best_single_row].values, best_col_idx)
 val = getindex!(val, SG.A[row_idx].values, searchsortedfirst(SG.A[row_idx].pos, best_col))
 @assert !iszero(val)

 fl, tmp = Nemo.divides!(tmp, val, best_val)
 if fl #best_val divides val
  #@vprintln :StructGauss "Case1:"
  tmp = neg!(tmp)
  SG.A.nnz -= length(SG.A[row_idx])
  SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
  SG.A.nnz += length(SG.A[row_idx])
 else
  !SG.unimodular_trafos && (fl, tmp = Nemo.divides!(tmp, best_val, val))
  if fl #val divides best_val
    #@vprintln :StructGauss "Case2:"
    SG.A.nnz -= length(SG.A[row_idx])
    tmp = neg!(tmp)
    scale_row!(SG.A, row_idx, tmp)
    Det.npiv > -1 && (Det.scaling*=tmp)
    tmp = one!(tmp)
    SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
    SG.A.nnz += length(SG.A[row_idx])
  else #best_val and val don't divide the other or unimodular ans val divides best_val
    @vprintln :StructGauss "Case3:"
    @vprintln :StructGauss "$divides(best_val, val)"

    #necessary to check whole row since transform generates new light entries in best_row
    for c in SG.A[best_single_row].pos 
     @assert !isempty(SG.col_list[c]) #TODO: check why empty dense cols exist
     if SG.is_light_col[c]
      jj = searchsortedfirst(SG.col_list[c], L_best)#or searchsortedlast?
      @assert SG.col_list[c][jj] == L_best
      deleteat!(SG.col_list[c], jj)
     end
    end
    g, a_best, a_row = gcdx!(g, a_best, a_row, best_val, val) #g = gcd(best_val, val) = a_best*best_val + a_row*val
    val = div!(tmp, val, g)
    val = neg!(val)
    best_val = div!(best_val, best_val, g) #TODO: check if best_val changed afterwards
    SG.A.nnz -= length(SG.A[row_idx])
    #TODO: optional parameter unimodular, to reduce fill-in in other cases
    @assert !(L_best in SG.col_list[best_col])
    if SG.unimodular_trafos
     Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], a_best, a_row, val, best_val, tmpa, tmpb)
    else
     #TODO: replace by scaling + add scaled row?
     Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], one!(a_best), zero!(a_row), val, best_val, tmpa, tmpb)
     Det.npiv > -1 && (Det.scaling*=best_val)
    end
    SG.A.nnz += length(SG.A[row_idx])
    #update best_row related stuff (potential new (light) entries from addition)
    best_col_idx = searchsortedfirst(SG.A[best_single_row].pos, best_col)
    @assert !(L_best in SG.col_list[best_col])
    update_after_addition!(L_best, best_single_row, SG)
  end
 end

 Hecke.release_tmp_scalar(SG.A, tmp_scalar)
 Hecke.release_tmp(SG.A, tmpa)
 Hecke.release_tmp(SG.A, tmpb)
 return best_col_idx, SG
end

function add_to_eliminate_old!(L_row::Int64, row_idx::Int64, L_best::Int64, best_single_row::Int64, best_col::Int64, best_col_idx::Int64, best_val::ZZRingElem, SG::data_StructGauss{ZZRingElem}, Det::data_Det)::data_StructGauss{ZZRingElem}
 for c in SG.A[row_idx].pos 
  @assert !isempty(SG.col_list[c]) #TODO: check why empty dense cols exist
  if SG.is_light_col[c]
   jj = searchsortedfirst(SG.col_list[c], L_row)#or searchsortedlast?
   @assert SG.col_list[c][jj] == L_row
   deleteat!(SG.col_list[c], jj)
  end
 end

 tmpa = Hecke.get_tmp(SG.A)
 tmpb = Hecke.get_tmp(SG.A)
 tmp, g, a_best, a_row, best_val, val = tmp_scalar = Hecke.get_tmp_scalar(SG.A, 6)
 
 best_val = getindex!(best_val, SG.A[best_single_row].values, best_col_idx)
 val = getindex!(val, SG.A[row_idx].values, searchsortedfirst(SG.A[row_idx].pos, best_col))
 @assert !iszero(val)

 fl, tmp = Nemo.divides!(tmp, val, best_val)
 if fl #best_val divides val
  #@vprintln :StructGauss "Case1:"
  tmp = neg!(tmp)
  SG.A.nnz -= length(SG.A[row_idx])
  SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
  SG.A.nnz += length(SG.A[row_idx])
 else
  fl, tmp = Nemo.divides!(tmp, best_val, val)
  if fl #val divides best_val
   #@vprintln :StructGauss "Case2:"
   SG.A.nnz -= length(SG.A[row_idx])
   tmp = neg!(tmp)
   scale_row!(SG.A, row_idx, tmp) #TODO:make unimodular
   tmp = one!(tmp)
   SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
   SG.A.nnz += length(SG.A[row_idx])
  else #best_val and val don't divide the other
   @vprintln :StructGauss "Case3:"
   @vprintln :StructGauss "$tmp, $fl"
   g, a_best, a_row = gcdx!(g, a_best, a_row, best_val, val) #g = gcd(best_val, val) = a_best*best_val + a_row*val
   val_red = div!(tmp, val, g)
   val_red = neg!(val_red)
   best_val_red = div!(best_val, best_val, g) #TODO: check if best_val changed afterwards
   SG.A.nnz -= length(SG.A[row_idx])
   #TODO: optional parameter unimodular, to reduce fill-in in other cases
   #Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], a_best, a_row, val_red, best_val_red, tmpa, tmpb) #wrong
   Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], one!(a_best), tmp, val_red, best_val_red, tmpa, tmpb)
   SG.A.nnz += length(SG.A[row_idx])
  end
 end
 Hecke.release_tmp_scalar(SG.A, tmp_scalar)
 Hecke.release_tmp(SG.A, tmpa)
 Hecke.release_tmp(SG.A, tmpb)
 return SG
end


################################################################################
#
#  Small Auxiliary Functions
#
################################################################################

#allTypes

#TODO: add sign changes in det for swap functions

function delete_zero_rows!(A::SMat{T}) where T
  filter!(!isempty, A.rows)
  A.r = length(A.rows)
  return A
end

function swap_entries(v::Vector{Int64}, i::Int64, j::Int64)
 v[i],v[j] = v[j],v[i]
end

#return Det?
function swap_rows_perm(i::Int64, j, SG::data_StructGauss{<:RingElem}, Det::data_Det)
 if i != j
  swap_rows!(SG.A, i, j)
  swap_entries(SG.pivot_col, i, j)
  swap_entries(SG.col_list_perm, i, j)
  swap_entries(SG.col_list_permi, SG.col_list_perm[i], SG.col_list_perm[j])
  swap_entries(SG.light_weight, i, j)
  Det.npiv > -1 && (Det.sign*=-1)
 end
end 

function swap_i_into_base(i::Int64, SG::data_StructGauss, Det::data_Det)
 if i < SG.single_row_limit
  swap_rows_perm(i, SG.base, SG, Det)
 else
   if i != SG.single_row_limit 
    swap_rows_perm(SG.base, SG.single_row_limit, SG, Det)
   end
   SG.single_row_limit +=1
   swap_rows_perm(SG.base, i, SG, Det)
 end
end

#returns index of light entry in position_array
function find_light_entry(position_array::Vector{Int64}, is_light_col::Vector{Bool})::Int64
 return findfirst(x->is_light_col[x], position_array)
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


function test_col_list(best_col, SG)
 for i in SG.col_list[best_col]
  @assert SG.col_list_permi[i]>=SG.base
 end
end

function test_light_weight(i, SG)
 _count = 0
 for j in SG.A[i].pos
  SG.is_light_col[j]&&(_count+=1)
 end
 @assert _count == SG.light_weight[i]
end
