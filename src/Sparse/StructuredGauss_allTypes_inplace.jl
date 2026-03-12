#TODO: input/output types and return
#important types: ZZ, Fq (small q), Z/nZ (n arb. large)
#TODO: modify Struct (row_marker, dense related stuff and starting number of pivots) to run a second time without extracting dense matrix
#TODO: adapt mul! for Det resp. to type (not inplace for all)
#TODO: type declaration (shorten? and avoid double declarations)

#TODO: new sparse_row type for ZZModRing that saves ZZRingElems as values instead 
#to use transform_rows with reduction mod n in the end 

#TODO: check influence of zero columns and whether they are marked correctly
#TODO: merge nzero and nlight?

#TODO: Fq: try normalizing best_row to 1/-1 as pivot and scale by entry in other row 

#TODO: unimodular and _det as keyword arguments?

#TODO: nzero could change when scaling with zero_divisor!!

#TODO: find_best_single_row min col length instead of row length -> reduces number of eliminations

add_verbosity_scope(:StructGauss)
set_verbosity_level(:StructGauss, 0)

add_assertion_scope(:StructGauss)
set_assertion_level(:StructGauss, 0)


mutable struct data_StructGauss{T}
 A::SMat{T}
 R::Ring #TODO: type declaration; parent_type(T) doesn't work
 nzero::Int64 #number of zero columns
 nlight::Int64 #number of non-pivot and non-dense columns 
 npivot::Int64 #number of pivot columns
 nzero_rows::Int64 #number of zero_rows
 nsingle_rows::Int64 #number of rows withone light entry -> needed in unimodular case
 nused_rows::Int64 #number of rows without any light entry (zero+pivot+dense rows)
 light_weight::Vector{Int64} #light_weight[i] = number of entries in row i outside of dense columns 
 col_list::Vector{Vector{Int64}} #col_list[j] = row indices of entries in column j outside of pivot rows
 row_marker::Vector{Int64} #0=init, -1=light_weight 1, -2=light_weight 0 & length!=0, -3=length 0 (zero row), 1:npivot=order of pivot rows
 is_light_col::Vector{Bool} #neither zero nor dense column
 is_pivot_col::Vector{Bool} #
 pivot_col::Vector{Int64} #pivot_col[i] = c >= 0 if col c has its only entry in row i
 unimodular_trafos::Bool #true -> uses unimodular trafos in elimination part (unfortunately more fill-in)

 function data_StructGauss(A::SMat{T}, unimodular_trafos::Bool) where T <: RingElem
  col_list = _col_list(A)
  return new{T}(A,
  base_ring(A),
  0,
  ncols(A),
  0,
  0,
  0,
  0,
  [length(A[i]) for i in 1:nrows(A)],
  col_list,
  fill(0, nrows(A)),
  fill(true, ncols(A)),
  fill(false, ncols(A)),
  fill(0, nrows(A)),
  unimodular_trafos,
  )
 end
end

mutable struct data_Det{T}
 scaling #tracks scaling -> divide det by product in the end
 divisions #tracks divisions -> multiply det by product
 sign #tracks swaps -> multiply det by -1 or do nothing
 #content #tracks reduction of polys by content -> multiply det by prod
 pivprod #product of pivot elements
 npiv #number of pivots
 function data_Det(R::T, _det::Bool) where T <: Ring
  if _det
   return new{T}(one(R), one(R), one(R), one(R), 0)
  else
   return new{T}(zero(R), zero(R), zero(R), zero(R), -1)
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

mutable struct data_DensePart{T}
 dense_idx::Vector{Int64} #ascending list of dense col indices (dense_idx[t]=c -> dense_map[c] = t)
 dense_map::Vector{Int64} #col c is dense, then dense_map[c] = position of c in dense_idx, else 0

 function data_DensePart(SG::data_StructGauss{T}, ndense::Int64) where T <: RingElem
  return new{T}(
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

function part_echelonize!(A::SMat{<:RingElem}, unimodular_trafos = false, _det=false, SG = data_StructGauss(A, unimodular_trafos), Det = data_Det(base_ring(A), _det); pivbound=ncols(A), trybound=ncols(A))::Tuple{data_StructGauss, data_Det}
 @assert SG.A == A
 n = nrows(A)
 m = ncols(A)
 #TODO: mark zero_rows later?
 #mark zero rows and single_rows

 if SG.npivot > 0 #not the first iteration
  #create new col_list with:
  #- empty list for pivot columns
  #- entries outside of pivot columns else
  c_list = [Array{Int64}([]) for i = 1:m]
  for i = 1:n
   #re-mark rows in dense part (note that there is only -3, -2 and positive values)
   if SG.row_marker[i] == -2 #assuming, this is a nonzero row but zero light_weight
    SG.nused_rows -= 1
    SG.light_weight[i] = length(A[i])
    if isone(length(A[i]))
      SG.row_marker[i] = -1
      SG.nsingle_rows += 1
    else
      SG.row_marker[i] = 0
    end
    for c in A[i].pos #only entries outside of pivot columns here
      col = c_list[c]
      push!(col, i)
    end
   elseif SG.row_marker[i] == -1 #might only happen if last ieration ended prematurely
    for c in A[i].pos #only entries outside of pivot columns here
      col = c_list[c]
      push!(col, i)
    end
    if length(SG.A[i]) > 1 #TODO: variable for length?
     SG.row_marker[i] = 0
     SG.nsingle_rows -= 1
     SG.light_weight = SG.A[i]
    end
   elseif SG.row_marker[i] == 0
    @assert length(SG.A[i]) > 1
    for c in A[i].pos #only entries outside of pivot columns here
      col = c_list[c]
      push!(col, i)
    end
   end
  end
  SG.col_list = c_list

  SG.nlight = m-SG.npivot

  for j = 1:m
    if !SG.is_pivot_col[j]
      SG.is_light_col[j] = true
    end
  end

 else #first iteration
  println("first iteration")
  for i = 1:n
    if iszero(length(A[i]))
    (SG.row_marker[i] = -3)
    SG.nzero_rows += 1
    SG.nused_rows += 1
    elseif isone(length(A[i]))
     SG.row_marker[i] = -1
     SG.nsingle_rows += 1
    end
  end
  #TODO: add to build_part_ref! with variable first?
  for i = 1:m
    if iszero(length(SG.col_list[i]))
      SG.nzero+=1
      #SG.is_light_col[i] = false
    end
  end
 end

 

 @show SG.nzero #test

 t = ncols(SG.A) - trybound
 while SG.nlight > SG.nzero && SG.nused_rows < n #TODO: find alternative for base (nothing marked 0?)
  test_row_marker(SG) #test
  test_nsingle_row(SG) #test
  build_part_ref!(SG, Det)
  test_row_marker(SG) #test
  test_nsingle_row(SG) #test
  (SG.npivot >= pivbound || t >= SG.nlight) && break
  (SG.nlight-SG.nzero == 0 || SG.nused_rows >= n) && break #TODO: alternative
  if SG.nsingle_rows > 0
   @assert -1 in SG.row_marker #test
  #if -1 in SG.row_marker
    if SG.unimodular_trafos
      best_single_row, best_col_idx = find_best_row_unimodular(SG, false)
      #best_single_row, best_col_idx = find_best_single_row(SG)
    else
      best_single_row, best_col_idx = find_best_single_row(SG)
    end
    @assert best_single_row != 0
  else
    @assert !(-1 in SG.row_marker) #test
    test_row_marker(SG) #test
    mark_col_as_dense(SG, Det)
    continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end
  #=  
  if best_single_row == 0
   mark_col_as_dense(SG, Det)
   continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end
  =#
  #@vprintln :StructGauss "$(SG.A[best_single_row].values[best_col_idx])"
  eliminate_and_update!(best_single_row, best_col_idx, SG, Det)
  @show SG.nlight, SG.npivot, SG.nused_rows #test
 end
 return SG, Det
end

function build_part_ref!(SG::data_StructGauss, Det::data_Det)
 queue = collect(ncols(SG.A):-1:1)#TODO: try only collecting light columns
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
      deleteat!(SG.col_list[jj], j_idx)
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
    SG.npivot += 1
    SG.row_marker[singleton_row] == -1 && (SG.nsingle_rows -= 1)
    SG.row_marker[singleton_row] = SG.npivot
    SG.light_weight[singleton_row] = 0 #new 
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

# first prio: +/-1 as pivot entry
# second prio: length of row
function find_best_single_row(SG::data_StructGauss{ZZRingElem})::Tuple{Int64, Int64}
 best_single_row = 0
 best_len = 0
 best_is_one = false
 best_val = ZZ(0)
 single_row_val = ZZ(0)
 best_col_idx = 0
 for i = 1:nrows(SG.A)
  SG.row_marker[i]!=-1 && continue
  @assert SG.light_weight[i] == 1
  single_row = SG.A[i]
  single_row_len = length(single_row)
  light_idx = find_light_entry(single_row.pos, SG.is_light_col)
  single_row_val = getindex!(single_row_val, single_row.values, light_idx)
  _is_one = is_unit(single_row_val)
  if SG.unimodular_trafos
    if !best_is_one && _is_one
      best_single_row = i
      best_len = single_row_len
      best_is_one = true
      best_col_idx = light_idx
      best_val = single_row_val
    elseif best_single_row == 0 || abs(single_row_val) < abs(best_val) || single_row_len < best_len
      best_single_row = i
      best_len = single_row_len
      best_is_one = _is_one
      best_col_idx = light_idx
      best_val = single_row_val
    end
  else
    if best_single_row == 0 || (_is_one == best_is_one && single_row_len < best_len)
      best_single_row = i
      best_len = single_row_len
      best_is_one = _is_one
      best_col_idx = light_idx
    elseif !best_is_one && _is_one
      best_single_row = i
      best_len = single_row_len
      best_is_one = true
      best_col_idx = light_idx
    end
  end
 end
 return best_single_row, best_col_idx
end

# first prio: +/-1 as pivot entry
# second prio: length of row
# with optional length parameter
function find_best_single_row2(SG::data_StructGauss{ZZRingElem}, row_len= true)::Tuple{Int64, Int64, Bool, Int64}
 best_single_row = 0
 best_len = 0
 best_is_one = false
 #best_val = ZZ(0)
 single_row_val = ZZ(0)
 best_col_idx = 0
 for i = 1:nrows(SG.A)
  SG.row_marker[i]!=-1 && continue
  @assert SG.light_weight[i] == 1
  single_row = SG.A[i]
  light_idx = find_light_entry(single_row.pos, SG.is_light_col)
  if row_len
   single_row_len = length(single_row)
  else
    single_row_len = length(SG.col_list[SG.A[i].pos[light_idx]])
  end
  single_row_val = getindex!(single_row_val, single_row.values, light_idx)
  _is_one = is_unit(single_row_val)
  if SG.unimodular_trafos
    if !best_is_one && _is_one
      best_single_row = i
      best_len = single_row_len
      best_is_one = true
      best_col_idx = light_idx
      #best_val = single_row_val
    elseif best_single_row == 0 || single_row_len < best_len
      best_single_row = i
      best_len = single_row_len
      best_is_one = _is_one
      best_col_idx = light_idx
      #best_val = single_row_val
    end
  else
    if best_single_row == 0 || (_is_one == best_is_one && single_row_len < best_len)
      best_single_row = i
      best_len = single_row_len
      best_is_one = _is_one
      best_col_idx = light_idx
    elseif !best_is_one && _is_one
      best_single_row = i
      best_len = single_row_len
      best_is_one = true
      best_col_idx = light_idx
    end
  end
 end
 return best_single_row, best_len, best_is_one, best_col_idx
end

#1st prio: unit
#2nd prio:light_weight
#3rd prio: length of row if row_len = true, length of col else
#look at -1 and 0 in same loop
#TODO: What shall happen, when there is no -1...?
function find_best_row_unimodular(SG::data_StructGauss, row_len = true)::Tuple{Int64, Int64}
 best_candidate_row = 0
 best_len = 0
 best_light_weight = 0
 best_is_unit = false
 best_is_single = false
 best_col_idx = 0
 candidate_row_val = SG.R(0)
 for i = 1:nrows(SG.A)
  #only consider SG.row_marker[i]=-1, -2
  if SG.row_marker[i] == -1 #is_single
   @assert SG.light_weight[i] == 1 #TODO: think about not using -1 at all in row_marker
   candidate_row = SG.A[i]
   light_idx = find_light_entry(candidate_row.pos, SG.is_light_col)
   candidate_row_val = getindex!(candidate_row_val, candidate_row.values, light_idx)
   if row_len #minimize length of row
    candidate_len = length(candidate_row)
   else #minimize length of column
    candidate_col = SG.A[i].pos[light_idx]
    candidate_len = length(SG.col_list[candidate_col])
   end
   _is_unit = is_unit(candidate_row_val)
   if best_is_unit == _is_unit
    #println("Case -1, 1")
    if !best_is_single || candidate_len < best_len
     best_candidate_row = i
     best_len = candidate_len
     best_light_weight = 1 #prob. not necessary
     #best_is_unit == _is_unit -> no change
     best_is_single = true #not needed in second case
     best_col_idx = light_idx
    end
   elseif (!best_is_unit && _is_unit) || best_candidate_row == 0
    #println("Case -1, 2")
    best_candidate_row = i
    best_len = candidate_len
    best_light_weight = 1 #prob. not necessary
    best_is_unit = true
    best_is_single = true
    best_col_idx = light_idx
   end
  elseif SG.row_marker[i] == 0 #!is_single_row
   @assert SG.light_weight[i] > 1
   #search for unit, if none exists in light part, then continue
   _is_unit = false
   light_idx = 0
   for idx in 1:length(SG.A[i].pos)
     j = SG.A[i].pos[idx]
     if SG.is_light_col[j] && is_unit(SG.A[i].values[idx])
       _is_unit = true
       light_idx = idx
       break
     end
   end
   #!_is_unit && continue
   if !best_is_unit && _is_unit
    #println("Case -2, 1")
    best_single_row = i
    best_len = length(SG.A[i])
    best_light_weight = SG.light_weight[i]
    best_is_unit = true
    best_col_idx = light_idx
   elseif best_is_unit && _is_unit && !best_is_single
    #println("Case -2, 2")
    #look after light_weight, then row/col len
    if row_len #minimize length of row
     candidate_len = length(SG.A[i])
    else #minimize length of column
     candidate_col = SG.A[i].pos[light_idx]
     candidate_len = length(SG.col_list[candidate_col])
    end
    #TODO: variable for light_weight[i]
    @assert SG.light_weight[i] > 1
    if SG.light_weight[i] < best_light_weight
     #println("Case -2, 2, 1")
     best_candidate_row = i
     best_len = candidate_len
     best_light_weight = SG.light_weight[i]
     best_is_unit = true
     best_is_single = true
     best_col_idx = light_idx
    elseif SG.light_weight[i] == best_light_weight
      #println("Case -2, 2, 2")
     if candidate_len < best_len
      #println("Case -2, 2, 2, 1")
      best_candidate_row = i
      best_len = candidate_len
      #light_weight doesn't change
      best_is_unit = true
      best_is_single = true
      best_col_idx = light_idx
     end
    end
   end
  end
 end
 return best_candidate_row, best_col_idx #if best_col_idx for -2, use other function later!!!
end

#1st prio: unit
#2nd prio:light_weight
#3rd prio: length of row if row_len = true, length of col else
#first -1, is no unit found, then 0
function find_best_row_unimodular2(SG::data_StructGauss, row_len = true)::Tuple{Int64, Int64}
  best_candidate_row, best_len, best_is_unit, best_col_idx = find_best_single_row2(SG, row_len)
  if best_candidate_row == 0 
    best_is_single = false
    best_light_weight = 0
  else
    best_is_single = true
    best_light_weight = 1
  end
  if best_is_unit
    return best_candidate_row, best_col_idx
  end

  #no unit found yet
  for i = 1:nrows(SG.A)
    if SG.row_marker[i] != 0
      continue
    end
    #row_marker is 0:
    @assert SG.light_weight[i] > 1
    #search for unit, if none exists in light part, then continue
    _is_unit = false
    light_idx = 0
    for idx in 1:length(SG.A[i].pos)
      j = SG.A[i].pos[idx]
      if SG.is_light_col[j] && is_unit(SG.A[i].values[idx])
        _is_unit = true
        light_idx = idx
        break
      end
    end
    #!_is_unit && continue
    if !best_is_unit && _is_unit
      #println("Case -2, 1")
      best_candidate_row = i
      best_len = length(SG.A[i])
      best_light_weight = SG.light_weight[i]
      best_is_unit = true
      best_col_idx = light_idx
    elseif best_is_unit && _is_unit && !best_is_single
      #println("Case -2, 2")
      #look after light_weight, then row/col len
      if row_len #minimize length of row
      candidate_len = length(candidate_row)
      else #minimize length of column
      candidate_col = SG.A[i].pos[light_idx]
      candidate_len = length(SG.col_list[candidate_col])
      end
      #TODO: variable for light_weight[i]
      @assert SG.light_weight[i] > 1
      if SG.light_weight[i] < best_light_weight
      #println("Case -2, 2, 1")
      best_candidate_row = i
      best_len = candidate_len
      best_light_weight = SG.light_weight[i]
      best_is_unit = true
      best_is_single = true
      best_col_idx = light_idx
      elseif SG.light_weight[i] == best_light_weight
        #println("Case -2, 2, 2")
        if candidate_len < best_len
          #println("Case -2, 2, 2, 1")
          best_candidate_row = i
          best_len = length(SG.A[i])
          #light_weight doesn't change
          best_is_unit = true
          best_is_single = true
          best_col_idx = light_idx
        end
      end
    end
  end
  return best_candidate_row, best_col_idx #FALSE: best_col_idx wrong!!!
end

#prio: shortest row
function find_best_single_row(SG::data_StructGauss{<:FinFieldElem})::Tuple{Int64, Int64}
 best_single_row = 0
 best_len = 0 #TODO: set to ncols + 1?
 best_col_idx = 0
 for i = 1:nrows(SG.A)
  SG.row_marker[i]!=-1 && continue
  @assert SG.light_weight[i] == 1
  single_row_len = length(SG.A[i])
  if best_single_row == 0 || single_row_len < best_len
   best_single_row = i
   best_len = single_row_len
  end
 end
 if best_single_row != 0
  best_col_idx = find_light_entry(SG.A[best_single_row].pos, SG.is_light_col)
 end
 return best_single_row, best_col_idx
end

#TODO: save is_unit info
#entry size not relevant
#prio: first length or first unit? TODO: test
#for now:
#1st prio: +-1
#2nd prio: unit
#3rd prio: length
function find_best_single_row(SG::data_StructGauss{T})::Tuple{Int64, Int64} where T <: Union{zzModRingElem, ZZModRingElem}
 best_single_row = 0
 best_val = SG.R(0)
 single_row_val = SG.R(0)
 best_len = 0
 best_is_one = false
 best_col_idx = 0
 for i = 1:nrows(SG.A)
  SG.row_marker[i]!=-1 && continue
  @assert SG.light_weight[i] == 1
  single_row = SG.A[i]
  single_row_len = length(single_row)
  light_idx = find_light_entry(single_row.pos, SG.is_light_col)
  single_row_val = getindex!(single_row_val, single_row.values, light_idx)
  _is_one = is_one(single_row_val) || is_one(-single_row_val)
  if !best_is_one && (is_unit(single_row_val))
    best_single_row = i
    best_len = single_row_len
    best_is_one = true
    best_col_idx = light_idx
    best_val = single_row_val
  elseif best_single_row == 0 || single_row_len < best_len
    best_single_row = i
    best_len = single_row_len
    best_is_one = _is_one
    best_col_idx = light_idx
    best_val = single_row_val
  end
 end
 return best_single_row, best_col_idx
end

#=
#entry size is relevant
function find_best_single_row(SG::data_StructGauss{ZZModRingElem})::Tuple{Int64, Int64}
 best_single_row = 0
 best_col = 0
 best_val = SG.R(0)
 best_len = 0
 best_is_one = false
 best_col_idx = 0
 for i = SG.base:SG.single_row_limit-1
  single_row = SG.A[i]
  single_row_len = length(single_row)
  w = SG.light_weight[i]
  @assert w == 1
  light_idx = find_light_entry(single_row.pos, SG.is_light_col)
  j_light = single_row.pos[light_idx]
  single_row_val = SG.A[i].values[light_idx]
  @assert length(SG.col_list[j_light]) > 1
  _is_one = single_row_val.data == 1 #|| single_row_val.data == R.n-1#TODO
  if best_single_row == 0
   best_single_row = i
   best_col = j_light
   best_len = single_row_len
   best_is_one = _is_one
   best_val = single_row_val
  elseif !best_is_one && _is_one
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
   best_is_one = _is_one
   best_val = single_row_val
  end
 end
 return best_single_row, best_col_idx
end
=#

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
 #dense_col_idx == 0 && @show SG.nlight, SG.nzero #-> fixed with nzero
 SG.is_light_col[dense_col_idx] = false
 marked_col = SG.col_list[dense_col_idx] #TODO: try without extra definition
 for i in marked_col
  @assert SG.light_weight[i] > 0
  SG.light_weight[i] -= 1
  handle_new_light_weight!(i, SG, Det)
  test_row_marker(SG) #test
 end
 SG.nlight -= 1
end

#unimodular: light_weight can increase! -> swap out of single_row area
function handle_new_light_weight!(i::Int64, SG::data_StructGauss, Det::data_Det)::data_StructGauss
 if SG.row_marker[i] == -1
  SG.nsingle_rows -= 1
 end
 w = SG.light_weight[i]
 if w == 0
  @vprintln :StructGauss 2 "Case1 (weight)"
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
  @vprintln :StructGauss 2 "Case2 (weight)"
  SG.row_marker[i] = -1
  SG.nsingle_rows += 1
 elseif SG.row_marker[i] == -1 #TODO: combine with beginning?
  #unimodular: light_weight can increase! -> swap out of single_row area
  @vprintln :StructGauss 2 "Case3 (weight)"
  SG.row_marker[i] = 0
 end
 return SG
end

#TODO: split later and define Vector_ZZModRingElem (see ZZRow)?
#best_single_row = row to eliminate with (next pivot row)
function eliminate_and_update!(best_single_row::Int64, best_col_idx::Int64, SG::data_StructGauss, Det::data_Det)::data_StructGauss
 @assert !iszero(best_single_row)
 best_col = SG.A[best_single_row].pos[best_col_idx] #col idx of elim-piv in matrix
 bc = deepcopy(best_col) #test
 @assert length(SG.col_list[best_col]) > 1
 @assert best_single_row in SG.col_list[best_col] #test
 best_val = SG.R(0) #TODO: tmp?
 row_idx = 0
 while length(SG.col_list[best_col]) > 1
  #best_col_idx might change when scaling causes zeroes in Z/nZ
  @assert best_single_row in SG.col_list[best_col] #test
  #Find row to add to
  @vprintln :StructGauss 2 "before find"
  row_idx = find_row_to_add_on(best_single_row, best_col, SG)
  @vprintln :StructGauss 2 "after find"
  @assert row_idx != best_single_row
  test_row_marker(SG) #test
  @assert best_col == bc
  best_col_idx, SG = add_to_eliminate!(row_idx, best_single_row, best_col, best_col_idx, SG, Det)
  @assert SG.A[best_single_row].pos[best_col_idx] == bc #test
  @assert best_col == bc #test
  #g = gcd(SG.A[row_idx].values)
  #Det.divisions*=g
  #SG.A[row_idx].values./=g
  @assert iszero(SG.A[row_idx, best_col])
  update_after_addition!(row_idx, SG)
  @assert SG.A[best_single_row].pos[best_col_idx] == bc #test
  @vprintln :StructGauss 2 "after update"
  #TODO: divide (row_idx) by gcd and test time diff
  #test_col_list(SG) #FAILS
  SG.unimodular_trafos && handle_new_light_weight!(best_single_row, SG, Det) #TODO: necessary?
  handle_new_light_weight!(row_idx, SG, Det)
  @assert SG.A[best_single_row].pos[best_col_idx] == bc #test
  test_row_marker(SG) #test
  @vprintln :StructGauss 2 "after weight"
 end
 return SG
end

#TODO: update best_row in Z/nZ case (new zeros might appear by scaling)
#TODO: update best_row after transform with gcd
#TODO: check in which cases row_idx can have other changes in light weight than -1 after elimination
function update_after_addition!(row_idx::Int64, SG::data_StructGauss)::data_StructGauss
 @assert !(0 in SG.A[row_idx].values)
 SG.light_weight[row_idx] = 0
 for c_idx in 1:length(SG.A[row_idx].pos)
  c = SG.A[row_idx].pos[c_idx]
  #@assert c != best_col
  @assert SG.A[row_idx].values[c_idx] != 0
  if SG.is_light_col[c] #for second iteration, this is also needed in dense cols
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

#TODO: why best_val as input?
function add_to_eliminate!(row_idx::Int64, best_single_row::Int64, best_col::Int64, best_col_idx::Int64, SG::data_StructGauss{ZZRingElem}, Det::data_Det{ZZRing})::Tuple{Int64, data_StructGauss{ZZRingElem}}
 remove_row(row_idx, SG)

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
 else
  !SG.unimodular_trafos && (fl, tmp = Nemo.divides!(tmp, best_val, val))
  if fl #val divides best_val
    #@vprintln :StructGauss "Case2:"
    SG.A.nnz -= length(SG.A[row_idx])
    tmp = neg!(tmp)
    scale_row!(SG.A, row_idx, tmp)
    Det.npiv > -1 && mul!(Det.scaling, Det.scaling, tmp)
    tmp = one!(tmp)
    SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
    SG.A.nnz += length(SG.A[row_idx])
  else #best_val and val don't divide the other or unimodular and val divides best_val
    @vprintln :StructGauss 2 "Case3:"

    if SG.unimodular_trafos
     #@assert best_val == SG.A[best_single_row, best_col] #test
     #@assert val == SG.A[row_idx, best_col] #test
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
     remove_row(best_single_row, SG)
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
  end
 end
 SG.A.nnz += length(SG.A[row_idx])

 Hecke.release_tmp_scalar(SG.A, tmp_scalar)
 Hecke.release_tmp(SG.A, tmpa)
 Hecke.release_tmp(SG.A, tmpb)
 return best_col_idx, SG
end

#Fq
function add_to_eliminate!(row_idx::Int64, best_single_row::Int64, best_col::Int64, best_col_idx::Int64, SG::data_StructGauss{T}, Det::data_Det{<:FinField})::Tuple{Int64, data_StructGauss{T}} where T <: FinFieldElem
 remove_row(row_idx, SG)

 tmpa = Hecke.get_tmp(SG.A)
 tmp, best_val, val = tmp_scalar = Hecke.get_tmp_scalar(SG.A, 3)
 #goal: scale with tmp = -val/best_val
 best_val = getindex!(best_val, SG.A[best_single_row].values, best_col_idx)
 val = getindex(SG.A[row_idx].values, searchsortedfirst(SG.A[row_idx].pos, best_col))
 Nemo.set!(tmp, div!(tmp, val, best_val))
 neg!(tmp)
 @assert !iszero(tmp)

 SG.A.nnz -= length(SG.A[row_idx])
 SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
 SG.A.nnz += length(SG.A[row_idx])

 Hecke.release_tmp_scalar(SG.A, tmp_scalar)
 Hecke.release_tmp(SG.A, tmpa)
 return best_col_idx, SG
end

#zz/ZZModRingElem
function add_to_eliminate!(row_idx::Int64, best_single_row::Int64, best_col::Int64, best_col_idx::Int64, SG::data_StructGauss{T}, Det::data_Det)::Tuple{Int64, data_StructGauss{T}} where T <: Union{zzModRingElem, ZZModRingElem}
#TODO
#divides with differencve between unit and not and unimodular
  remove_row(row_idx, SG)
  #tmpa = Hecke.get_tmp(SG.A)
  #tmpb = Hecke.get_tmp(SG.A)
  tmp, g, a_best, a_row, best_val, val = tmp_scalar = Hecke.get_tmp_scalar(SG.A, 6)

  best_val = getindex!(best_val, SG.A[best_single_row].values, best_col_idx)
  val = getindex!(val, SG.A[row_idx].values, searchsortedfirst(SG.A[row_idx].pos, best_col))
  @assert !iszero(val)

  fl, tmp = Nemo.divides!(tmp, val, best_val)
  if fl #best_val divides val
    @vprintln :StructGauss 2 "Case1:"
    tmp = neg!(tmp)
    SG.A.nnz -= length(SG.A[row_idx])
    SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp)#, tmpa)
  else
    @vprintln :StructGauss 2 "Case3:"
    g, a_best, a_row = gcdx!(g, a_best, a_row, best_val, val)
    val = div!(val, val, g)
    val = neg!(val)
    best_val = div!(best_val, best_val, g)
    SG.A.nnz -= length(SG.A[row_idx])
    
    remove_row(best_single_row, SG)
    #Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], a_best, a_row, val, best_val)#, tmpa, tmpb)
    Hecke.transform_row!(SG.A, best_single_row, row_idx, a_best, a_row, val, best_val)
    @assert iszero(SG.A[row_idx, best_col])
    #update best_row related stuff (potential new (light) entries from addition)
    update_after_addition!(best_single_row, SG)
    best_col_idx = searchsortedfirst(SG.A[best_single_row].pos, best_col)
  end
  SG.A.nnz += length(SG.A[row_idx])
  
  Hecke.release_tmp_scalar(SG.A, tmp_scalar)
  #Hecke.release_tmp(SG.A, tmpa)
  #Hecke.release_tmp(SG.A, tmpb)
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
function swap_rows_perm(i::Int64, j, SG::data_StructGauss, Det::data_Det)
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

function remove_row(i::Int64, SG) #TODO: better name
 for c in SG.A[i].pos 
  @assert !isempty(SG.col_list[c])
  if SG.is_light_col[c]
   jj = searchsortedfirst(SG.col_list[c], i) # or searchsortedlast?
   @assert SG.col_list[c][jj] == i
   deleteat!(SG.col_list[c], jj)
  end
 end
 return SG
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

#needed if `part_echelonize!`` stopped prematurely
function update_light_cols!(SG)
 for i = 1:ncols(SG.A)
  if SG.is_pivot_col[i]
    continue
  elseif SG.is_light_col[i] && !isempty(SG.col_list[i])
   SG.is_light_col[i] = false
   SG.nlight -= 1
  #avoid columns of zeros in dense part: 
  elseif !SG.is_light_col[i] && isempty(SG.col_list[i]) #TODO: test
   SG.is_light_col[i] = true
   SG.nlight += 1
  end
 end
 return SG
end

function collect_dense_col_indices(SG::data_StructGauss{T})::data_DensePart{T} where T <: RingElem
 m = ncols(SG.A)
 ndense = m - SG.nlight - SG.npivot
 DPart = data_DensePart(SG, ndense)
 j = 1
 for i = 1:m
  if !SG.is_light_col[i] && !SG.is_pivot_col[i] #column belongs to dense part
   DPart.dense_map[i] = j
   push!(DPart.dense_idx, i)
   j += 1
  end
 end
 @assert length(DPart.dense_idx) == ndense
 return DPart
end

#TODO: avoid zero rows/cols in dense part!!!
function extract_dense_matrix(SG::data_StructGauss{ZZRingElem}, DPart::data_DensePart{ZZRingElem})
 #ignores zero_rows
 D = ZZMatrix(nrows(SG.A) - SG.npivot - SG.nzero_rows, length(DPart.dense_idx))
 r = 0 
 for i in 1:length(SG.A)
   SG.row_marker[i] != -2 && continue
   r += 1
   idx = 0
   for j in SG.A[i].pos
    idx += 1
    c = DPart.dense_map[j] 
    @assert !iszero(c)
    setindex!(D, SG.A[i], r, c, idx) #D[r,c] = SG.A[i,j]
	  end
	 end
 return D
end

function Base.setindex!(A::ZZMatrix, B::SRow{ZZRingElem}, ar::Int64, ac::Int64, bidx::Int64)
 ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, Ptr{Int}), Nemo.mat_entry_ptr(A, ar, ac), Hecke.get_ptr(B.values, bidx))
end

function extract_dense_matrix(SG::data_StructGauss{T}, DPart::data_DensePart{T}) where T <: RingElem
 #ignores zero_rows
 D = zero_matrix(SG.R, nrows(SG.A) - SG.npivot - SG.nzero_rows, length(DPart.dense_idx))
 r = 0 
 for i in 1:length(SG.A)
   SG.row_marker[i] != -2 && continue
   r += 1
   idx = 0
   for j in SG.A[i].pos
    idx += 1
    c = DPart.dense_map[j] 
    @assert !iszero(c)
    D[r,c] = SG.A[i].values[idx]
	  end
	 end
 return D
end


################################################################################
#
#  Kernel
#
################################################################################

#TODO: Option to get only one element of the kernel independent of its dimension?

function nullspace(A::SMat{T}, SG::data_StructGauss{T} = data_StructGauss(A, false)) where T<:RingElem
 if SG.npivot == 0 
  SG, = part_echelonize!(A, false, false, SG)
 end
 update_light_cols!(SG)
 DPart = collect_dense_col_indices(SG)
 D = extract_dense_matrix(SG, DPart)
 _nullity, _dense_kernel = nullspace(D)
 l, K = init_kernel(_nullity, _dense_kernel, SG, DPart)
 return compose_kernel(l, K, SG)
end

function init_kernel(_nullity::Int64, _dense_kernel::ZZMatrix, SG::data_StructGauss{ZZRingElem}, DPart::data_DensePart{ZZRingElem})
 R = base_ring(SG.A)
 m = ncols(SG.A)
 l = _nullity+SG.nlight
 K = ZZMatrix(m, l)
 #initialisation
 ilight = 1
 for i = 1:m
  if SG.is_light_col[i]
    @assert ilight <= SG.nlight
    one!(Nemo.mat_entry_ptr(K, i, _nullity+ilight))
    ilight +=1
  else
   j = DPart.dense_map[i]
   if j>0
    for c = 1:_nullity
      set!(mat_entry_ptr(K, i, c), mat_entry_ptr(_dense_kernel, j, c))
    end
   end
  end
 end
 return l, K
end

function compose_kernel(l::Int64, K::ZZMatrix, SG::data_StructGauss{ZZRingElem})
  n, m = nrows(SG.A), ncols(SG.A)
  x = zero(ZZ)
  a = zero(ZZ)
  r = zero(ZZ)
  g = zero(ZZ)
  for i = n:-1:1
    c = SG.pivot_col[i]  # col idx of pivot or zero
    iszero(c) && continue
    a = Hecke.get_ptr(SG.A[i].values, searchsortedfirst(SG.A[i].pos, c))
    for kern_i in 1:l
     for idx in 1:length(SG.A[i])
      cc = SG.A[i].pos[idx]
      cc == c && continue
      submul!(x, Nemo.mat_entry_ptr(K, cc, kern_i), Hecke.get_ptr(SG.A[i].values, idx))
     end
     gcd!(g, a, x)
     divexact!(r, a, g)
     divexact!(x, x, g)
     for j = 1:m
      Nemo.mul!(Nemo.mat_entry_ptr(K, j, kern_i), Nemo.mat_entry_ptr(K, j, kern_i), r)
     end
     setindex!(K, x, c, kern_i)
     zero!(x)
     zero!(r)
     zero!(g)
    end
  end
  return l, K
end

function _kernel(h, add_to_lattice::Bool = true) #h::FinGenAbGroupHom
  G = domain(h)
  H = codomain(h)
  m = vcat(sparse_matrix(h.map), sparse_matrix(rels(H)))
  m = Hecke.delete_zero_rows!(m)
  hn, t = hnf_with_transform(m)
  for i = 1:nrows(hn)
    if is_zero_row(hn, i)
      return sub(G, sub(t, i:nrows(t), 1:ngens(G)), add_to_lattice)
    end
  end
  # if the Hermite form has no zero-row, there is no
  # non-trivial kernel element
  return sub(G, elem_type(G)[], add_to_lattice)
end

################################################################################
#
#  Image
#
################################################################################

#TODO: describe as lattice?
#doc with optional parameter?
@doc raw"""
    column_span(A::SMat{ZZRingElem}) -> ZZMatrix

Return the column $\mathbb Z$-span of $A$ as columns of a `ZZMatrix`. 
"""
function column_span(B::SMat{T}, A::SMat{T}=transpose(B), SG::data_StructGauss{T} = data_StructGauss(A, true))::ZZMatrix where T<:RingElem
  if SG.npivot == 0 
    SG, = part_echelonize!(A, true, false, SG)
  end
  update_light_cols!(SG)
  DPart = collect_dense_col_indices(SG)
  D = extract_dense_matrix(SG, DPart)
  Dc = size(D)[2]
  @assert Dc == length(DPart.dense_idx)
  hnf!(D)
  s = row_rank_of_hnf(D)
  Mc = SG.npivot+s
  M = zero_matrix(ZZ, SG.A.c, Mc)
  c_idx = 1 #column index in M
  dense_counter = 0 #counts rows in dense part
  for i = 1:SG.A.r
    c_idx > Mc && break
    if SG.row_marker[i] > 0 #pivot row in triangular part of a
      #set M[:,c_idx] to A[i]:
      pos_idx = 0
      for j in SG.A[i].pos
        pos_idx += 1 
        setindex!(M, SG.A[i], j, c_idx, pos_idx) #M[j, c_idx] = A[i,j]
      end
      c_idx += 1
    elseif SG.row_marker[i] == -2 && dense_counter < s #nonzero row (after hnf) outside of triangular part
      dense_counter += 1 #row index in D
      #set M[:,c_idx] to D[dense_counter,:] and zeros
      for j in 1:Dc #j is column index in c
        cc = DPart.dense_idx[j] #corresponding column index in A -> row index in M
        M[cc, c_idx] = D[dense_counter, j]
      end
      c_idx += 1
    end
  end
  return M
end

@doc raw"""
    row_span(A::SMat{ZZRingElem}) -> ZZMatrix

Return the row $\mathbb Z$-span of $A$ as rows of a `ZZMatrix`.
"""
function row_span(A::SMat{T}, SG::data_StructGauss{T} = data_StructGauss(A, true))::ZZMatrix where T<:RingElem
  A = delete_zero_rows!(A)
  if SG.npivot == 0 
    SG, = part_echelonize!(A, true, false, SG)
  end
  update_light_cols!(SG)
  DPart = collect_dense_col_indices(SG)
  D = extract_dense_matrix(SG, DPart)
  Dc = size(D)[2]
  @assert Dc == length(DPart.dense_idx)
  hnf!(D)
  s = row_rank_of_hnf(D)
  Mr = SG.npivot+s
  M = zero_matrix(ZZ, Mr, SG.A.c)
  r_idx = 1 #row index in M
  dense_counter = 0 #counts rows in dense part
  for i = 1:SG.A.r
    r_idx > Mr && break
    if SG.row_marker[i] > 0 #pivot row in triangular part of a
      #set M[r_idx,:] to A[i]:
      pos_idx = 0
      for j in SG.A[i].pos
        pos_idx += 1 
        setindex!(M, SG.A[i], r_idx, j, pos_idx) #M[j, c_idx] = A[i,j]
      end
      r_idx += 1
    elseif SG.row_marker[i] == -2 && dense_counter < s #nonzero row (after hnf) outside of triangular part
      dense_counter += 1 #row index in D
      #set M[r_idx,:] to D[dense_counter,:] and zeros
      for j in 1:Dc #j is column index in c
        cc = DPart.dense_idx[j] #corresponding column index in A -> row index in M
        M[r_idx, cc] = D[dense_counter, j]
      end
      r_idx += 1
    end
  end
  return M
end

function _image(h, add_to_lattice::Bool = true)
  H = codomain(h)
  hn = row_span(vcat(sparse_matrix(h.map), sparse_matrix(rels(H))))
  im = FinGenAbGroupElem[]
  for i = 1:nrows(hn)
    @assert !is_zero_row(hn, i)
    push!(im, FinGenAbGroupElem(H, sub(hn, i:i, 1:ngens(H))))
  end
  return sub(H, im, add_to_lattice)  # too much, this is sub in hnf....
end


#TODO: improve with less allocations/flint function
function row_rank_of_hnf(D::ZZMatrix)::Int64
  r,c = size(D)
  for i = r:-1:1
    !is_zero_row(D, i) && (return i)
  end
  return 0
end



################################################################################
#
#  TESTs (to be removed later)
#
################################################################################

function test_col_list(SG)
 for i = 1:length(SG.col_list)
  if SG.is_light_col[i]
   @assert length(SG.col_list[i]) > 0
  end
 end
end

function test_light_weight(i, SG)
 _count = 0
 for j in SG.A[i].pos
  SG.is_light_col[j]&&(_count+=1)
 end
 @assert _count == SG.light_weight[i]
end

function test_row_marker(SG, _range = 1:SG.A.r)
 for i in _range
  if SG.light_weight[i] == 1
    SG.row_marker[i] != -1 && @show SG.row_marker[i]
    @assert SG.row_marker[i] == -1
  elseif SG.light_weight[i] == 0
    @assert SG.row_marker[i] != -1
  elseif SG.light_weight[i] > 1
    @assert SG.row_marker[i] == 0
  end
 end
end

function test_nsingle_row(SG)
  _count = 0
  for i = 1:SG.A.r
    SG.row_marker[i] == -1 && (_count += 1)
  end
  @assert SG.nsingle_rows == _count
end