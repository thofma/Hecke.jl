#TODO: input/output types and return
#important types: ZZ, Fq (small q), Z/nZ (n arb. large)
#TODO: modify Struct (row_marker, dense related stuff and starting number of pivots) to run a second time without extracting dense matrix

#=
add_verbosity_scope(:StructGauss)
set_verbosity_level(:StructGauss, 0)

add_assertion_scope(:StructGauss)
set_assertion_level(:StructGauss, 0)
=#

mutable struct data_StructGauss{T}
 A::SMat{T}
 R::Ring #TODO: type declaration
 nlight::Int64
 npivots::Int64
 nzero_rows::Int64
 nused_rows::Int64
 light_weight::Vector{Int64}
 col_list::Vector{Vector{Int64}}
 #col_list_perm::Vector{Int64} #perm gives new ordering of original A[i] via their indices
 #col_list_permi::Vector{Int64} #A[permi[i]]=A[i] before permutation = list of sigma(i) (recent position of former A[i])
 row_marker::Vector{Int64} #0=init, -1=light_weight 1, -2=light_weight 0 & length!=0, -3=length 0 (zero row), 1:npivots=order of pivot rows
 is_light_col::Vector{Bool}
 is_pivot_col::Vector{Bool}
 pivot_col::Vector{Int64} #pivot_col[i] = c >= 0 if col c has its only entry in row i, i always recent position
 unimodular_trafos::Bool

 function data_StructGauss(A::SMat{T}, unimodular_trafos::Bool) where T <: RingElem
  col_list = _col_list(A)
  return new{T}(A,
  base_ring(A),
  ncols(A),
  0,
  0,
  0,
  [length(A[i]) for i in 1:nrows(A)],
  col_list,
  #collect(1:nrows(A)),
  #collect(1:nrows(A)),
  fill(0, nrows(A)),
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

mutable struct data_DensePart
 dense_idx::Vector{Int64} #ascending list of dense col indices (dense_idx[t]=c -> dense_map[c] = t)
 dense_map::Vector{Int64} #col c is dense, then dense_map[c] = position of c in dense_idx, else 0

 function data_DensePart(SG::data_StructGauss, ndense::Int64)
  return new(
  sizehint!(Int[], ndense),
  fill(0, ncols(SG.A))
  )
 end
end

################################################################################
#
#  Partial Echolonization
#
################################################################################

#Build an upper triangular matrix for as many columns as possible compromising
#the loss of sparsity during this process.

function part_echelonize!(A::SMat{T}, _det=false, unimodular_trafos = false; pivbound=ncols(A), trybound=ncols(A))::Tuple{data_StructGauss{T}, data_Det} where T <: RingElem
 n = nrows(A)
 SG = data_StructGauss(A, unimodular_trafos)
 Det = Hecke.data_Det(base_ring(A), _det)
 #TODO: mark zero_rows later?
 #mark zero rows and single_rows
 for i = 1:n
  if iszero(length(A[i]))
   (SG.row_marker[i] = -3)
   SG.nzero_rows += 1
  elseif isone(length(A[i]))
   SG.row_marker[i] = -1
  end
 end

 t = ncols(SG.A) - trybound
 while SG.nlight > 0 && SG.nused_rows < n #TODO: find alternative for base (nothing marked 0?)
  build_part_ref!(SG, Det)
  
  (SG.npivots >= pivbound || t >= SG.nlight) && break
  (SG.nlight == 0 || SG.nused_rows >= n) && break #TODO: alternative
  best_single_row, best_col_idx = find_best_single_row(SG)
  best_single_row == 0 && @assert(!(-1 in SG.row_marker))
  
  if best_single_row == 0
   mark_col_as_dense(SG, Det)
   continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end
  eliminate_and_update!(best_single_row, best_col_idx, SG, Det)
 end
 return SG, Det
end

function build_part_ref!(SG::data_StructGauss{<:RingElem}, Det::data_Det)
 queue = collect(ncols(SG.A):-1:1)
 while !isempty(queue)
  queue_new = Int[]
  for j in queue
   if length(SG.col_list[j])==1 && SG.is_light_col[j]
    singleton_row = only(SG.col_list[j])
    @assert !iszero(SG.A[singleton_row, j])
    for jj in SG.A[singleton_row].pos
     if SG.is_light_col[jj]
      @assert singleton_row in SG.col_list[jj]
      j_idx = findfirst(isequal(singleton_row), SG.col_list[jj])
      deleteat!(SG.col_list[jj],j_idx)
      length(SG.col_list[jj]) == 1 && push!(queue_new, jj)
     end
    end
    SG.is_light_col[j] = false
    SG.is_pivot_col[j] = true
    SG.pivot_col[singleton_row] = j
    if Det.npiv > -1
     mul!(Det.pivprod, Det.pivprod, SG.A[singleton_row_idx, j])
    end
    SG.nlight -= 1
    SG.npivots += 1
    SG.row_marker[singleton_row] = SG.npivots
    #swap_i_into_base(singleton_row_idx, SG, Det)
    SG.nused_rows += 1
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
 for i = 1:nrows(SG.A)
  SG.row_marker[i]!=-1 && continue
  single_row = SG.A[i]
  single_row_len = length(single_row)
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
 for i in marked_col
  @assert SG.light_weight[i] > 0
  SG.light_weight[i] -= 1
  handle_new_light_weight!(i, SG, Det)
 end
 SG.nlight -= 1
end

#unimodular: light_weight can increase! -> swap out of single_row area
function handle_new_light_weight!(i::Int64, SG::data_StructGauss, Det::data_Det)::data_StructGauss
 w = SG.light_weight[i]
 if w == 0
  @vprintln :StructGauss "Case1 (weight)"
  if iszero(length(SG.A[i]))
   SG.row_marker[i] = -3
   SG.nzero_rows += 1
  else
    SG.row_marker[i] = -2
  end
  @assert iszero(SG.pivot_col[i])
  #swap_i_into_base(i, SG, Det)
  #SG.pivot_col[SG.base] = 0
  #move_into_Y(SG.base, SG)
  SG.nused_rows += 1
 elseif w == 1
  @vprintln :StructGauss "Case2 (weight)"
  SG.row_marker[i] = -1
 elseif SG.row_marker[i] == -1
  #unimodular: light_weight can increase! -> swap out of single_row area
  @vprintln :StructGauss "Case3 (weight)"
  SG.row_marker[i] = 0
 end
 return SG
end

#best_single_row = row to eliminate with (next pivot row)
function eliminate_and_update!(best_single_row::Int64, best_col_idx::Int64, SG::data_StructGauss, Det::data_Det)::data_StructGauss
 @assert !iszero(best_single_row)
 #L_best = deepcopy(SG.col_list_perm[best_single_row]) #old index 
 best_col = SG.A[best_single_row].pos[best_col_idx] #col idx of elim-piv in matrix
 @assert length(SG.col_list[best_col]) > 1
 @assert best_single_row in SG.col_list[best_col] #test
 best_val = SG.R(0) #TODO: tmp?
 row_idx = 0
 while length(SG.col_list[best_col]) > 1
  #best_col_idx might change when scaling causes zeroes in Z/nZ
  best_val = getindex!(best_val, SG.A[best_single_row].values, best_col_idx)
  @assert best_single_row in SG.col_list[best_col] #test
  #Find row to add to
  @vprintln :StructGauss "before find"
  row_idx = find_row_to_add_on(best_single_row, best_col, SG)
  @vprintln :StructGauss "after find"
  @assert row_idx != best_single_row

  best_col_idx, SG = add_to_eliminate!(row_idx, best_single_row, best_col, best_col_idx, best_val, SG, Det)
  #g = gcd(SG.A[row_idx].values)
  #Det.divisions*=g
  #SG.A[row_idx].values./=g
  @assert iszero(SG.A[row_idx, best_col])
  update_after_addition!(row_idx, SG)
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
function update_after_addition!(row_idx::Int64, SG::data_StructGauss)::data_StructGauss
 @assert !(0 in SG.A[row_idx].values)
 SG.light_weight[row_idx] = 0
 for c_idx in 1:length(SG.A[row_idx].pos)
  c = SG.A[row_idx].pos[c_idx]
  #@assert c != best_col
  @assert SG.A[row_idx].values[c_idx] != 0
  if SG.is_light_col[c]
   insert!(SG.col_list[c], searchsortedfirst(SG.col_list[c], row_idx), row_idx)
   SG.light_weight[row_idx] += 1
  end
 end
 return SG
end

function find_row_to_add_on(best_single_row::Int64, best_col::Int64, SG::data_StructGauss)::Int64
 for row_idx in SG.col_list[best_col][end:-1:1] #findlast
  row_idx == best_single_row && continue
  @assert SG.row_marker[row_idx]>-2
  return row_idx
 end
end

function add_to_eliminate!(row_idx::Int64, best_single_row::Int64, best_col::Int64, best_col_idx::Int64, best_val::ZZRingElem, SG::data_StructGauss{ZZRingElem}, Det::data_Det)::Tuple{Int64, data_StructGauss{ZZRingElem}}
 for c in SG.A[row_idx].pos 
  @assert !isempty(SG.col_list[c]) #TODO: check why empty dense cols exist
  if SG.is_light_col[c]
   jj = searchsortedfirst(SG.col_list[c], row_idx)#or searchsortedlast?
   @assert SG.col_list[c][jj] == row_idx
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
  @vprintln :StructGauss "Case1:"
  tmp = neg!(tmp)
  SG.A.nnz -= length(SG.A[row_idx])
  SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
  SG.A.nnz += length(SG.A[row_idx])
 else
  !SG.unimodular_trafos && (fl, tmp = Nemo.divides!(tmp, best_val, val))
  if fl #val divides best_val
    @vprintln :StructGauss "Case2:"
    SG.A.nnz -= length(SG.A[row_idx])
    tmp = neg!(tmp)
    scale_row!(SG.A, row_idx, tmp)
    Det.npiv > -1 && mul!(Det.scaling, Det.scaling, tmp)
    tmp = one!(tmp)
    SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
    SG.A.nnz += length(SG.A[row_idx])
  else #best_val and val don't divide the other or unimodular ans val divides best_val
    @vprintln :StructGauss "Case3:"
    @vprintln :StructGauss "$divides(best_val, val)"

    if SG.unimodular_trafos
     @assert best_val == SG.A[best_single_row, best_col] #test
     @assert val == SG.A[row_idx, best_col] #test
     g, a_best, a_row = gcdx!(g, a_best, a_row, best_val, val) #g = gcd(best_val, val) = a_best*best_val + a_row*val
    else
     g = gcd!(g, best_val, val)
    end
    val = div!(val, val, g)
    val = neg!(val)
    best_val = div!(best_val, best_val, g)
    SG.A.nnz -= length(SG.A[row_idx])
    if SG.unimodular_trafos
     #necessary to check whole row since transform generates new light entries in best_row
     for c in SG.A[best_single_row].pos 
      @assert !isempty(SG.col_list[c]) #TODO: check why empty dense cols exist
      if SG.is_light_col[c]
       jj = searchsortedfirst(SG.col_list[c], best_single_row)#or searchsortedlast?
       @assert SG.col_list[c][jj] == best_single_row
       deleteat!(SG.col_list[c], jj)
      end
     end
     Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], a_best, a_row, val, best_val, tmpa, tmpb)
     @assert iszero(SG.A[row_idx, best_col])
     #update best_row related stuff (potential new (light) entries from addition)
     update_after_addition!(best_single_row, SG)
     best_col_idx = searchsortedfirst(SG.A[best_single_row].pos, best_col)
    else
     #Attention: might run into problem if a_best = 0
     #Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], one!(a_best), zero!(a_row), val, best_val, tmpa, tmpb)
     scale_row!(SG.A, row_idx, best_val)
     mul!(Det.scaling, Det.scaling, best_val)
     SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], val, tmpa)
     Det.npiv > -1 && mul!(Det.scaling, Det.scaling, best_val)
    end
    SG.A.nnz += length(SG.A[row_idx])
  end
 end

 Hecke.release_tmp_scalar(SG.A, tmp_scalar)
 Hecke.release_tmp(SG.A, tmpa)
 Hecke.release_tmp(SG.A, tmpb)
 return best_col_idx, SG
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
  #TODO: no inplace for zzMod
  Det.npiv > -1 && neg!(Det.sign)
 end
end

#returns index of light entry in position_array
function find_light_entry(position_array::Vector{Int64}, is_light_col::Vector{Bool})::Int64
 return findfirst(x->is_light_col[x], position_array)
end

function track_swapping(Det)
 #TODO
end


################################################################################
#
#  Extract dense part
#
################################################################################

function collect_dense_indices(SG::data_StructGauss)::data_DensePart
 m = ncols(SG.A)
 ndense = m - SG.nlight - SG.npivots
 DPart = data_DensePart(SG, ndense)
 j = 1
 for i = 1:m
  if !SG.is_light_col[i] && !SG.is_pivot_col[i]
   DPart.dense_map[i] = j
   push!(DPart.dense_idx, i)
   j += 1
  end
 end
 @assert length(DPart.dense_idx) == ndense
 return DPart
end

function extract_dense_matrix(SG, DPart)
 #remove zero_rows
 D = ZZMatrix(nrows(SG.A) - SG.npivots - SG.nzero_rows, length(DPart.dense_idx))
	r = 0 
 for i in 1:length(SG.A)
   SG.row_marker[i] != -2 && continue
   r+=1
   idx = 0
   for j in SG.A[i].pos
    idx+=1
    c = DPart.dense_map[j] 
    @assert !iszero(c)
    #D[r,c] = SG.A[i,j]:
    setindex!(D, SG.A[i], r, c, idx)
	  end
	 end
 return D
end

function Base.setindex!(A::ZZMatrix, B::SRow{ZZRingElem}, ar::Int64, ac::Int64, bidx::Int64) #TODO: why not working with searchsortedfirst?
 ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, Ptr{Int}), Nemo.mat_entry_ptr(A, ar, ac), Hecke.get_ptr(B.values, bidx))
end

################################################################################
#
#  TESTs (to be removed later)
#
################################################################################

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