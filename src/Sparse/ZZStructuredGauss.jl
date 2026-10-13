#TODO: sizehints
#TODO: pointer pointer pointer
#TODO: sizehint for heavy stuff can be given later, so don't initialize immediately
#TODO: add sizehint for Y?
#TODO: remove whitespaces at beginning of lines
#TODO: eliminate some assertions/hassert
#TODO: inplace instead of Y, dense part via pointer
#TODO: use new set! for value array
#TODO: alternatives for nullspace with treshhold or combination with rref mod p
#TODO: write is_zero_entry for value arrays?
#TODO: single kernel elem for any rank
#TODO: adapt doc to optional argument
#TODO: don't deepcopy best_row?
#TODO: set best_single_row to 0, same for best_col
#TODO: is_light_col with 0 and 1 and inplace changes?
#TODO: include update in add_scaled_row!
#TODO: check why update after addition necessary in combination with deleting before adding
#TODO: set tmp to zero after divides

#=
PROBLEMS:
- why more nnzs in SG.A+SG.Y than in PR.A?
- maximum of PR.A greater as in SG.Y?
=#

add_verbosity_scope(:StructGauss)
set_verbosity_level(:StructGauss, 1)

add_assertion_scope(:StructGauss)
set_assertion_level(:StructGauss, 1)

#test
mutable struct test_ZZStructGauss{T}
  best_row_idcs::Vector{Int64}
  best_col_idcs::Vector{Int64}
  best_rows::Vector{SRow}
  
  function test_ZZStructGauss(A::SMat{T}) where T <: ZZRingElem
    return new{T}([],
    [],
    [])
  end
end



mutable struct data_ZZStructGauss{T}
  A::SMat{T}
  Y::SMat{T}
  base::Int64
  single_row_limit::Int64
  dense_start::Int64
  nlight::Int64
  npivots::Int64
  light_weight::Vector{Int64}
  col_list::Vector{Vector{Int64}} 
  col_list_perm::Vector{Int64} #perm gives new ordering of original A[i] via their indices
  col_list_permi::Vector{Int64} #A[permi[i]] = A_input[i]  = list of sigma(i) (recent position of former A[i])
  is_light_col::Vector{Bool}
  is_pivot_col::Vector{Bool}
  pivot_col::Vector{Int64} #pivot_col[i] = c > 0 if col c has its only entry in row i, i always recent position
  
  #TODO: set variable to nrows(A)
  function data_ZZStructGauss(A::SMat{T}) where T <: ZZRingElem
   Y = sparse_matrix(base_ring(A), 0, ncols(A))
   col_list = _col_list(A)
   return new{T}(A,
   Y,
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
   fill(0, nrows(A)))
  end
end

function _col_list(A::SMat{T})::Vector{Vector{Int64}}  where T <: ZZRingElem
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
    structured_gauss(A::SMat{T}, kernel_basis::Bool=false) where T <: ZZRingElem

Return a tuple $(\nu, N)$ consisting of the nullity $\nu$ of `A` and a basis `N`
(consisting of column vectors) for the right nullspace of `A`, i.e. such that
`A*N` is the zero matrix.
"""
function structured_gauss(A::SMat{T}, kernel_basis::Bool=false) where T <: ZZRingElem
 SG, SG_test = part_echelonize!(A)
 return compute_kernel(SG, kernel_basis)
end

################################################################################
#
#  Partial Echelonization
#
################################################################################

#Build an upper triangular matrix for as many columns as possible compromising
#the loss of sparsity during this process.

#function part_echelonize!(A::SMat{T})::data_ZZStructGauss where T <: ZZRingElem
function part_echelonize!(A::SMat{T})::Tuple{data_ZZStructGauss{ZZRingElem}, test_ZZStructGauss{ZZRingElem}} where T <: ZZRingElem #test
 A = delete_zero_rows!(A)
 n = nrows(A)
 SG = data_ZZStructGauss(A)
 SG_test = test_ZZStructGauss(A)
 single_rows_to_top!(SG)

 #while SG.nlight > 0 && SG.base <= SG.dense_start #all inplace
 while SG.nlight > 0 && SG.base <= n #with Y
  build_part_ref!(SG)
  #=
  for i = 1:m
   SG.is_light_col[i] && @assert length(SG.col_list[i]) != 1
  end
  =# #testing
  #(SG.nlight == 0 || SG.base > SG.dense_start) && break #all inplace
  (SG.nlight == 0 || SG.base > n) && break #with Y
  best_single_row = find_best_single_row(SG)
  best_single_row < 0 && @assert(SG.base == SG.single_row_limit)
  
  if best_single_row < 0
   turn_heavy(SG)
   continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end
  #@vprint :StructGauss best_single_row, SG.base, SG.dense_start
  push!(SG_test.best_row_idcs, SG.col_list_perm[best_single_row]) #test
  eliminate_and_update2!(best_single_row, SG, SG_test)
 end
 #return SG
 return SG, SG_test #test
end

function single_rows_to_top!(SG::data_ZZStructGauss)::data_ZZStructGauss
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

function build_part_ref!(SG::data_ZZStructGauss)
 queue = collect(ncols(SG.A):-1:1)
 while !isempty(queue)
  queue_new = Int[]
  for j in queue
   if length(SG.col_list[j])==1 && SG.is_light_col[j]
    singleton_row_origin = only(SG.col_list[j])
    singleton_row_idx = SG.col_list_permi[singleton_row_origin]
    for jj in SG.A[singleton_row_idx].pos
     if SG.is_light_col[jj]
      @hassert :StructGauss singleton_row_origin in SG.col_list[jj]
      j_idx = searchsortedfirst(SG.col_list[jj], singleton_row_origin)
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

function find_best_single_row(SG::data_ZZStructGauss)::Int64
 best_single_row = -1
 best_col = NaN
 best_val = NaN
 best_len = -1
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
  is_one = single_row_val.d == 1 || single_row_val.d == -1
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

function turn_heavy(SG::data_ZZStructGauss)
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
  #handle_new_light_weight2!(i_current, SG) #all inplace
  handle_new_light_weight!(i_current, SG) #with Y
 end
 SG.nlight -= 1
end

function handle_new_light_weight!(i::Int64, SG::data_ZZStructGauss)::data_ZZStructGauss
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
 elseif SG.base <= i < SG.single_row_limit
  swap_rows_perm(i, SG.single_row_limit-1, SG)
  SG.single_row_limit-=1
 end
 return SG
end

#handles case without Y
function handle_new_light_weight2!(i::Int64, SG::data_ZZStructGauss)::data_ZZStructGauss
 w = SG.light_weight[i]
 if w == 0
  #=
  swap_i_into_base(i, SG)
  SG.pivot_col[SG.base] = 0
  move_into_Y(SG.base, SG)
  SG.base+=1
  =#
  swap_to_end(i, SG)
 elseif w == 1
  if i > SG.single_row_limit
   swap_rows_perm(i, SG.single_row_limit, SG)
  end
  SG.single_row_limit += 1
 elseif SG.base <= i < SG.single_row_limit
  swap_rows_perm(i, SG.single_row_limit-1, SG)
  SG.single_row_limit-=1
 end
 return SG
end

#function eliminate_and_update!(best_single_row::Int64, SG::data_ZZStructGauss)::data_ZZStructGauss
function eliminate_and_update!(best_single_row::Int64, SG::data_ZZStructGauss, SG_test::test_ZZStructGauss)::Tuple{data_ZZStructGauss{ZZRingElem}, test_ZZStructGauss{ZZRingElem}} #test
 @assert best_single_row != 0
 best_row = deepcopy(SG.A[best_single_row])
 push!(SG_test.best_rows, best_row) #test
 light_idx = find_light_entry(best_row.pos, SG.is_light_col)
 best_col = best_row.pos[light_idx]
 push!(SG_test.best_col_idcs, best_col) #test
 @assert length(SG.col_list[best_col]) > 1
 best_val = deepcopy(SG.A[best_single_row, best_col])
 @assert !iszero(best_val)
 best_col_idces = SG.col_list[best_col]
 row_idx = 0
 while length(best_col_idces) > 1
  row_idx = find_row_to_add_on(row_idx, best_row, best_col_idces, SG)
  @v_do :StructGauss lw = deepcopy(SG.light_weight[row_idx]) #test
  #@hassert :StructGauss 1 best_col_idces == SG.col_list[best_col]
  @assert row_idx > 0
  #@hassert :StructGauss SG.col_list_perm[row_idx] in SG.col_list[best_col]
  L_row = SG.col_list_perm[row_idx]
  add_to_eliminate!(L_row, row_idx, best_row, best_col, best_val, SG) #TODO: isone query
  @hassert :StructGauss row_idx == SG.col_list_permi[L_row]
  update_after_addition!(L_row, row_idx, best_col, SG)
  #@vprintln :StructGauss lw, SG.light_weight[row_idx]
  @hassert :StructGauss row_idx == SG.col_list_permi[L_row]
  @hassert :StructGauss SG.light_weight[row_idx] == lw-1
  #handle_new_light_weight2!(row_idx, SG) #all inplace
  handle_new_light_weight!(row_idx, SG) #with Y
 end
 return SG, SG_test
end

function find_row_to_add_on(row_idx::Int64, best_row::SRow{T}, best_col_idces::Vector{Int64}, SG::data_ZZStructGauss)::Int64 where T <: ZZRingElem
 for L_row in best_col_idces[end:-1:1]
  row_idx = SG.col_list_permi[L_row]
  SG.A[row_idx] == best_row && continue
  row_idx < SG.base && continue
  break
 end
 return row_idx
end

#TODO: only changes in lightcol for bestcol in row_idx
function add_to_eliminate!(L_row::Int64, row_idx::Int64, best_row::SRow{T}, best_col::Int64, best_val::ZZRingElem, SG::data_ZZStructGauss)::data_ZZStructGauss where T <: ZZRingElem
 #@hassert :StructGauss L_row in SG.col_list[best_col]
 #@hassert :StructGauss !(0 in SG.A[row_idx].values)
 val = SG.A[row_idx, best_col] #TODO: use searchsortedfirst
 @assert !iszero(val)
 g = gcd(val, best_val)
 val_red = divexact(val, g)
 best_val_red = divexact(best_val, g)
 #@hassert :StructGauss L_row in SG.col_list[best_col]
 for c in SG.A[row_idx].pos
  @assert !isempty(SG.col_list[c])
  if SG.is_light_col[c]
   jj = searchsortedfirst(SG.col_list[c], L_row)
   deleteat!(SG.col_list[c], jj)
  end
 end
 scale_row!(SG.A, row_idx, best_val_red)
 #@hassert :StructGauss !(0 in best_row.values)
 SG.A.nnz -= length(SG.A[row_idx])
 Hecke.add_scaled_row!(best_row, SG.A[row_idx], -val_red)
 SG.A.nnz += length(SG.A[row_idx])
 #@hassert :StructGauss iszero(Hecke.get_ptr(SG.A[row_idx], searchsortedfirst(SG.A[row_idx].pos, best_col)))
 #@hassert :StructGauss !(0 in SG.A[row_idx].values)
 return SG
end

function update_after_addition!(L_row::Int64, row_idx::Int64, best_col::Int64, SG::data_ZZStructGauss)::data_ZZStructGauss
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
 
 function swap_rows_perm(i::Int64, j::Int64, SG::data_ZZStructGauss)
  if i != j
   swap_rows!(SG.A, i, j)
   #swap! pointers
   swap_entries(SG.pivot_col, i, j)
   swap_entries(SG.col_list_perm, i, j)
   swap_entries(SG.col_list_permi, SG.col_list_perm[i], SG.col_list_perm[j])
   swap_entries(SG.light_weight, i, j)
  end
 end 
 
function swap_i_into_base(i::Int64, SG::data_ZZStructGauss)
 #Note that i>=SG.base when function applied.
 if i < SG.single_row_limit
  swap_rows_perm(i, SG.base, SG)
 else
   if i != SG.single_row_limit 
    swap_rows_perm(SG.base, SG.single_row_limit, SG)
   end
   SG.single_row_limit+=1
   swap_rows_perm(SG.base, i, SG)
 end
end


function swap_to_end(i::Int64, SG::data_ZZStructGauss)
 #Note that i>=SG.base when function applied.
 if i < SG.single_row_limit
  swap_rows_perm(i, SG.single_row_limit-1, SG)
  swap_rows_perm(SG.single_row_limit-1, SG.dense_start, SG)
  SG.single_row_limit-=1
 else
  swap_rows_perm(i, SG.dense_start, SG)
 end
 SG.dense_start-=1
end

function find_light_entry(position_array::Vector{Int64}, is_light_col::Vector{Bool})::Int64
 for idx in 1:length(position_array)
   is_light_col[position_array[idx]] && return idx
 end
end

#TODO: push only non-empty rows into Y
function move_into_Y(i::Int64, SG::data_ZZStructGauss)
 @assert i == SG.base
 push!(SG.Y, deepcopy(SG.A[SG.base]))
 for base_c in SG.A[SG.base].pos
  @assert !SG.is_light_col[base_c]
  @assert !isempty(SG.col_list[base_c])
 end
 SG.A.nnz-=length(SG.A[SG.base])
 empty!(SG.A[SG.base].pos), empty!(SG.A[SG.base].values)
end

function delete_zero_rows!(A::SMat{T}) where T <: ZZRingElem
 for i = A.r:-1:1
   if isempty(A[i].pos)
     deleteat!(A.rows, i)
     A.r-=1
   end
 end
 return A
end

################################################################################
#
#  Kernel Computation
#
################################################################################

#Compute the kernel corresponding to the non echelonized part from above and
#insert backwards using the triangular part to get the full kernel.

mutable struct data_ZZKernel
 heavy_mapi::Vector{Int64}
 heavy_map::Vector{Int64}

 function data_ZZKernel(SG::data_ZZStructGauss, nheavy::Int64)
  return new(
  sizehint!(Int[], nheavy),
  fill(0, ncols(SG.A))
  )
 end
end

function compute_kernel(SG, kernel_basis::Bool)
  Hecke.update_light_cols!(SG)
  @assert SG.nlight >= 0
  KER = Hecke.collect_dense_cols!(SG)
  #D = dense_matrix2(SG, KER) #all inplace
  D = dense_matrix(SG, KER) #with Y
  if kernel_basis
    _nullity, _dense_kernel = nullspace(D)
  else
    _nullity, _dense_kernel = 1, kernel_elem(D)
  end
  l, K = Hecke.init_kernel(_nullity, _dense_kernel, SG, KER, kernel_basis)
  return compose_kernel(l, K, SG)
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
 KER = data_ZZKernel(SG, nheavy)
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
 D = ZZMatrix(nrows(SG.A) - SG.npivots, length(KER.heavy_mapi))
	 for i in 1:length(SG.Y)
	  for j in 1:length(KER.heavy_mapi)
	   setindex!(D, SG.Y[i], i, j, KER.heavy_mapi[j])
	  end
	 end
 return D
end

#TODO: case where D is empty
function dense_matrix2(SG, KER) #all inplace
 delete_zero_rows!(SG.A)
 D = ZZMatrix(nrows(SG.A) - SG.npivots, length(KER.heavy_mapi))
	 for i in 1:nrows(SG.A)-SG.dense_start
   #@show i
	  for j in 1:length(KER.heavy_mapi)
    @assert i<= size(D)[1]
	   setindex!(D, SG.A[i], i, j, KER.heavy_mapi[j])
	  end
	 end
 return D
end

function kernel_elem(D)
  #assume D has full rank-1
  n, m = size(D)
  @assert n >= m #TODO: allow m<n?
  p = 0
  crank = Int64(0) #TODO: type decl. relevant?
  rrank = Int64(0)
  lbound = Int64(0) #TODO: remove if not needed else safe p to best lbound
  DT = transpose(D)
  for i = 1:5
    p = next_prime(2^20 + rand(2:2^10))
    Dp = change_base_ring(Native.GF(p), D)
    crank  = rref!(Dp)
    if crank < lbound
      @vprint :StructGauss "$p is bad prime."
      continue
    end
    crank == m && return ZZMatrix(m, 1)
    lbound = crank
    lbound < m-1 && continue
    DTp = change_base_ring(Native.GF(p), DT)
    rrank = rref!(DTp)
    @assert rrank == crank
    c, cpivots = _pivots(Dp, crank, true)
    _, rpivots = _pivots(DTp, rrank)
    @assert !iszero(c)
    D_red = D[rpivots, cpivots]
    #@show rpivots, cpivots
    d = D[rpivots, c:c]
    sol = Nemo.dixon_solve(D_red, d)
    return vcat(sol[1], ZZMatrix(1,1,[-sol[2]]))
  end
  p = next_prime(2^50 + rand(2:2^10))
  Dp = change_base_ring(Native.GF(p), D)
  crank  = rref!(Dp)
  crank == m && return ZZMatrix(m, 1)
  @error("case for rank smaller ncols-1 not yet implemented") 
  #=TODO:
    - dixon_solve with given rank
    - if solution trivial, independent col d found
    - try to find P+d with another p to get corresp. rows
      a) look for indep. rows in submatrix D[:, P+d]    or
      b) take union of new and old pivots if diff not empty and try again
  =#
end

#TODO: assume dixon for one-dim kernel, nullspace else
function init_kernel(_nullity, _dense_kernel, SG, KER, kernel_basis)
 R = base_ring(SG.A)
 m = ncols(SG.A)
 if kernel_basis
  l = _nullity+SG.nlight
  #SG.nlight>0 && _one = one(ZZ)
 else
  l = 1
 end
 K = ZZMatrix(m, l)
 #initialisation
 ilight = 1
 for i = 1:m
  if SG.is_light_col[i]
   if kernel_basis
    @assert ilight <= SG.nlight
    one!(Nemo.mat_entry_ptr(K, i, _nullity+ilight))
    ilight +=1
   end
  else
   j = KER.heavy_map[i]
   if j>0
    for c = 1:_nullity
      set!(mat_entry_ptr(K, i, c), mat_entry_ptr(_dense_kernel, j, c))
    end
   end
  end
 end
 return l, K
end

function compose_kernel(l, K, SG)
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

function _pivots(A, _rank, nonpivot = false)
  n,m = size(A)
  i = 1
  j = 1
  P = sizehint!(Int64[], _rank)
  c = m
  while i<= n && j<=m
   while iszero(A[i,j])
    j+=1
    j>m && return c, P
   end
   if j<=m
    if !isempty(P) && nonpivot && j > (P[end]+1)
      c = P[end] +1
      @show c
    end
    push!(P,j)
   else
    break
   end
   while !iszero(A[i,j])
    i+=1
    i>n && return c, P
   end
  end
  return P
end

#TODO: check if still necessary
#Warning: skips zero entries in sparse matrix
function Base.setindex!(A::ZZMatrix, B::SRow{ZZRingElem}, ar::Int64, ac::Int64, bj::Int64) #TODO: why not working with searchsortedfirst?
 isnothing(findfirst(isequal(bj), B.pos)) && return
 ccall((:fmpz_set, Nemo.libflint), Cvoid, (Ptr{ZZRingElem}, Ptr{Int}), Nemo.mat_entry_ptr(A, ar, ac), Hecke.get_ptr(B.values, findfirst(isequal(bj), B.pos)))
end


#functions for correct elimination:
#function eliminate_and_update2!(best_single_row::Int64, SG::data_ZZStructGauss)::data_ZZStructGauss
function eliminate_and_update2!(best_single_row::Int64, SG::data_ZZStructGauss, SG_test::test_ZZStructGauss)::Tuple{data_ZZStructGauss{ZZRingElem}, test_ZZStructGauss{ZZRingElem}} #test
 L_best = deepcopy(SG.col_list_perm[best_single_row])
 best_row_pos = deepcopy(SG.A[best_single_row].pos) #test
 @assert !iszero(best_single_row)
 #@vprint :StructGauss "limits: $(SG.base), $(SG.single_row_limit), $best_single_row"
 push!(SG_test.best_rows, SG.A[best_single_row]) #test
 light_idx = find_light_entry(SG.A[best_single_row].pos, SG.is_light_col)
 best_col = SG.A[best_single_row].pos[light_idx]
 @hassert :StructGauss !(best_col in SG_test.best_col_idcs)
 push!(SG_test.best_col_idcs, best_col) #test
 @assert length(SG.col_list[best_col]) > 1
 best_val = SG.A[best_single_row].values[light_idx] #test
 @hassert :StructGauss !iszero(best_val)
 #best_col_idces = SG.col_list[best_col]
 row_idx = 0
 len = length(SG.col_list[best_col]) #test
 while length(SG.col_list[best_col]) > 1
  #@show SG.col_list[best_col]
  best_single_row = SG.col_list_permi[L_best]
  @hassert :StructGauss SG.light_weight[best_single_row] == 1
  row_idx = find_row_to_add_on2(row_idx, best_single_row, best_col, SG)
  @assert row_idx > 0
  @hassert :StructGauss L_best != SG.col_list_perm[row_idx]
  L_row = SG.col_list_perm[row_idx]
  row_pos = deepcopy(SG.A[row_idx].pos) #test
  #L1 = deepcopy(L_row) #test
  @v_do :StructGauss _light = deepcopy(SG.is_light_col)
  @v_do :StructGauss lw = deepcopy(SG.light_weight[row_idx]) #test
  _v = 0
  for _i in SG.A[row_idx].pos
    if SG.is_light_col[_i] 
      _v+=1
    end
  end
  #best_col == 42 && @show row_idx, SG.nlight
  @hassert :StructGauss best_row_pos == SG.A[best_single_row].pos
  @hassert :StructGauss best_single_row == SG.col_list_permi[L_best]
  add_to_eliminate2!(L_row, row_idx, best_single_row, best_col, SG) #TODO: isone query
  @hassert :StructGauss L_best != SG.col_list_perm[row_idx]
  @hassert :StructGauss row_idx == SG.col_list_permi[L_row]
  #= TODO: alternative update
  SG.light_weight[row_idx] -= 1
  jj = searchsortedfirst(SG.col_list[best_col], L_row)
  @hassert :StructGauss SG.col_list[best_col][jj] == L_row
  deleteat!(SG.col_list[best_col], jj)
  =#
  #@show best_single_row, row_idx
  best_row_pos != SG.A[best_single_row].pos && @vprintln :StructGauss "bestpos1 = $best_row_pos \n bestpos2 = $(SG.A.rows[best_single_row].pos) \n pos1 = $row_pos \n pos2 = $(SG.A.rows[row_idx].pos)"
  @hassert :StructGauss best_row_pos == SG.A[best_single_row].pos #error, best row pos is union of row positions for best_row and row_idx
  
  update_after_addition2!(L_row, row_idx, best_col, SG)
  @hassert :StructGauss L_best != SG.col_list_perm[row_idx]
  @hassert :StructGauss best_single_row == SG.col_list_permi[L_best]
  @hassert :StructGauss SG.is_light_col == _light
  @hassert :StructGauss best_row_pos == SG.A[best_single_row].pos
  #best_col == 42 && @show row_idx
  _w = 0
  for _i in SG.A[row_idx].pos
    if SG.is_light_col[_i] 
      _w+=1
      @hassert :StructGauss !iszero(SG.A[row_idx, _i])
    end
  end
  #@vprintln :StructGauss lw, _v, SG.light_weight[row_idx], _w
  @hassert :StructGauss row_idx == SG.col_list_permi[L_row]
  @hassert :StructGauss SG.light_weight[row_idx] == lw-1
  #handle_new_light_weight2!(row_idx, SG) #all inplace
  #@vprintln :StructGauss row_idx, SG.col_list_permi[L_best]
  handle_new_light_weight!(row_idx, SG) #with Y
  #best_row_pos != SG.A[best_single_row].pos && @show best_col, best_row_pos, SG.A[best_single_row].pos
  #@hassert :StructGauss best_row_pos == SG.A[best_single_row].pos
  #row_idx == 100 && @show 2, SG.col_list_perm[row_idx], SG.light_weight[row_idx]
  @hassert :StructGauss length(SG.col_list[best_col]) == len-1
  @v_do :StructGauss len -= 1
 end
 return SG, SG_test
end

function find_row_to_add_on2(row_idx::Int64, best_single_row::Int64, best_col::Int64, SG::data_ZZStructGauss)::Int64
 for L_row in SG.col_list[best_col][end:-1:1]
  row_idx = SG.col_list_permi[L_row]
  row_idx == best_single_row && continue #TODO: work with origin idces here
  @assert SG.base <= row_idx
  break
 end
 return row_idx
end

#TODO: only changes in lightcol for bestcol in row_idx
function add_to_eliminate2!(L_row::Int64, row_idx::Int64, best_single_row::Int64, best_col::Int64, SG::data_ZZStructGauss{ZZRingElem})::data_ZZStructGauss{ZZRingElem}
 #test start
 best_row_pos = deepcopy(SG.A[best_single_row].pos) #test
 L_best = SG.col_list_perm[best_single_row]
 @assert L_row in SG.col_list[best_col]
 @assert !(0 in SG.A[row_idx].values)
 best_row = SG.A[best_single_row]
 bv = best_row.values[searchsortedfirst(best_row.pos, best_col)]
 #best_val = getindex!(best_val, best_row.values, searchsortedfirst(best_row.pos, best_col))
 @hassert :StructGauss row_idx == SG.col_list_permi[L_row]
 @v_do :StructGauss _count = 0
 #=
 for c in SG.A[row_idx].pos
  SG.is_light_col[c] && @v_do :StructGauss _count += 1
  isempty(SG.col_list[c]) && @show c, SG.is_light_col[c]
  @assert !isempty(SG.col_list[c]) #TODO: check why empty dense cols exist
 end
 =#
 #test end
 #not necessary for integral domains???
 
 for c in SG.A[row_idx].pos
  SG.is_light_col[c] && @v_do :StructGauss _count += 1
  isempty(SG.col_list[c]) && @show c, SG.is_light_col[c]
  @assert !isempty(SG.col_list[c]) #TODO: check why empty dense cols exist
  if SG.is_light_col[c]
   jj = searchsortedfirst(SG.col_list[c], L_row)
   @hassert :StructGauss SG.col_list[c][jj] == L_row
   deleteat!(SG.col_list[c], jj)
  end
 end
 @hassert :StructGauss L_best != L_row

 #best_idx = searchsortedfirst(SG.A[].pos, best_col)
 tmpa = Hecke.get_tmp(SG.A)
 tmpb = Hecke.get_tmp(SG.A)
 #best_val = SG.A[best_single_row, best_col] #TODO: use only one best_val
 tmp, g, a_best, a_row, best_val, val = tmp_scalar = Hecke.get_tmp_scalar(SG.A, 6)
 best_val = getindex!(best_val, SG.A[best_single_row].values, searchsortedfirst(SG.A[best_single_row].pos, best_col))
 #TODO: use index from before instead (jlight)
 val = getindex!(val, SG.A[row_idx].values, searchsortedfirst(SG.A[row_idx].pos, best_col))
 @assert !iszero(val)
 fl, tmp = Nemo.divides!(tmp, val, best_val) 
 if fl #best_val divides val
  #@vprintln :StructGauss "Case1:"
  tmp = neg!(tmp)
  SG.A.nnz -= length(SG.A[row_idx])
  SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
  SG.A.nnz += length(SG.A[row_idx])
  @hassert :StructGauss best_row_pos == SG.A[best_single_row].pos
 else
  fl, tmp = Nemo.divides!(tmp, best_val, val)
  if fl #val divides best_val
   #@vprintln :StructGauss "Case2:"
   SG.A.nnz -= length(SG.A[row_idx])
   tmp = neg!(tmp)
   scale_row!(SG.A, row_idx, tmp)
   tmp = one!(tmp)
   SG.A[row_idx] = Hecke.add_scaled_row!(SG.A[best_single_row], SG.A[row_idx], tmp, tmpa)
   SG.A.nnz += length(SG.A[row_idx])
   @hassert :StructGauss best_row_pos == SG.A[best_single_row].pos
  else #best_val and val don't divide the other
   #@vprintln :StructGauss "Case3:"
   #@vprintln :StructGauss "fl = $fl, tmp = $tmp"
   g, a_best, a_row = gcdx!(g, a_best, a_row, best_val, val) #g = gcd(best_val, val) = a_best*best_val + a_row*val
   val_red = div!(tmp, val, g)
   @hassert :StructGauss val_red == div(val, g)
   val_red = neg!(val_red)
   bv = deepcopy(best_val) #test
   best_val_red = div!(best_val, best_val, g) #TODO: check if best_val changed afterwards
   @hassert :StructGauss best_val_red == div(bv, g)
   SG.A.nnz -= length(SG.A[row_idx])
   @hassert :StructGauss iszero(tmp)
   #Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], a_best, a_row, val_red, best_val_red, tmpa, tmpb) #wrong
   Hecke.transform_row!(SG.A[best_single_row], SG.A[row_idx], ZZ(1), tmp, val_red, best_val_red, tmpa, tmpb)
   SG.A.nnz += length(SG.A[row_idx])
   @hassert :StructGauss best_row_pos == SG.A[best_single_row].pos #error
  end
 end
 Hecke.release_tmp_scalar(SG.A, tmp_scalar)
 Hecke.release_tmp(SG.A, tmpa)
 Hecke.release_tmp(SG.A, tmpb)
 #test begin
 @hassert :StructGauss row_idx == SG.col_list_permi[L_row]
 @hassert :StructGauss L_best != L_row
 @v_do :StructGauss _count2 = 0
  for c in SG.A[row_idx].pos
    SG.is_light_col[c] && @v_do :StructGauss _count2 += 1
  end
  #@show _count, _count2
  #test end
 return SG
end

#should work for both eliminations, updates all cols not only light
function update_after_addition2!(L_row::Int64, row_idx::Int64, best_col::Int64, SG::data_ZZStructGauss)::data_ZZStructGauss
 SG.light_weight[row_idx] = 0
 for c_idx in 1:length(SG.A[row_idx].pos)
  c = SG.A[row_idx].pos[c_idx]
  @assert c != best_col
  if SG.is_light_col[c]
    @hassert :StructGauss !iszero(SG.A[row_idx].values[c_idx])
    @hassert :StructGauss !(L_row in SG.col_list[c])
    insert!(SG.col_list[c], searchsortedfirst(SG.col_list[c], L_row), L_row)
    SG.light_weight[row_idx]+=1
  end
 end
 return SG
end