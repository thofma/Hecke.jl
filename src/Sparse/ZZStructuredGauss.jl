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
#TODO: single kernel elem for any rank (try wiedemann vs nullspace?)
#TODO: adapt doc to optional argument

#=
PROBLEMS:
- why more nnzs in SG.A+SG.Y than in PR.A?
- maximum of PR.A greater as in SG.Y?
=#

AbstractAlgebra.add_verbosity_scope(:StructGauss)
AbstractAlgebra.set_verbosity_level(:StructGauss, 1)

AbstractAlgebra.add_assertion_scope(:StructGauss)
AbstractAlgebra.set_assertion_level(:StructGauss, 1)

mutable struct data_ZZStructGauss{T}
  A::SMat{T}
  Y::SMat{T}
  single_row_limit::Int64
  base::Int64
  nlight::Int64
  npivots::Int64
  light_weight::Vector{Int64}
  col_list::Vector{Vector{Int64}} 
  col_list_perm::Vector{Int64} #perm gives new ordering of original A[i] via their indices
  col_list_permi::Vector{Int64} #A[permi[i]]=A[i] before permutation = list of sigma(i) (recent position of former A[i])
  is_light_col::Vector{Bool}
  is_pivot_col::Vector{Bool}
  pivot_col::Vector{Int64} #pivot_col[i] = c >= 0 if col c has its only entry in row i, i always recent position
  heavy_ext::Int64
  heavy_col_idx::Vector{Int64}
  heavy_col_len::Vector{Int64}
 
  function data_ZZStructGauss(A::SMat{T}) where T <: ZZRingElem
   Y = sparse_matrix(base_ring(A), 0, ncols(A))
   col_list = _col_list(A)
   return new{T}(A,
   Y,
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
   0,
   Int[],
   Int[])
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
 
 Return a tuple (\nu, N) consisting of the nullity \nu of A and a basis N
 (consisting of column vectors) for the right nullspace of A, i.e. such that
 AN is the zero matrix.
 """
 function structured_gauss(A::SMat{T}, kernel_basis::Bool=false) where T <: ZZRingElem
  SG = part_echolonize!(A)
  return compute_kernel(SG, kernel_basis)
 end
 
 ################################################################################
 #
 #  Partial Echolonization
 #
 ################################################################################
 
 #Build an upper triangular matrix for as many columns as possible compromising
 #the loss of sparsity during this process.
 
 function part_echolonize!(A::SMat{T})::data_ZZStructGauss where T <: ZZRingElem
  A = delete_zero_rows!(A)
  n = nrows(A)
  m = ncols(A)
  SG = data_ZZStructGauss(A)
  single_rows_to_top!(SG)
 
  while SG.nlight > 0 && SG.base <= n
   build_part_ref!(SG)
   #=
   for i = 1:m
    SG.is_light_col[i] && @assert length(SG.col_list[i]) != 1
   end
   =# #testing
   (SG.nlight == 0 || SG.base > n) && break
   best_single_row = find_best_single_row(SG)
   best_single_row < 0 && @assert(SG.base == SG.single_row_limit)
   
   if best_single_row < 0
    find_dense_cols(SG)
    turn_heavy(SG)
    continue #while SG.nlight > 0 && SG.base <= SG.A.r
   end
   eliminate_and_update!(best_single_row, SG)
  end
  return SG
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
       #@hassert :StructGauss singleton_row_origin in SG.col_list[jj]
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
 
 function find_dense_cols(SG::data_ZZStructGauss)
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
  #@hassert :StructGauss light_cols == findall(x->SG.is_light_col[x], 1:m)
 end
 
 function turn_heavy(SG::data_ZZStructGauss)
  for j = 1:SG.heavy_ext
   c = SG.heavy_col_idx[j]
   if c<0
    continue
   end
   SG.is_light_col[c] = false
   lt2hvy_col = SG.col_list[c]
   lt2hvy_len = length(lt2hvy_col)
   @assert lt2hvy_len == length(SG.col_list[c])
   for k = 1:lt2hvy_len
    i_origin = lt2hvy_col[k]
    i_now = SG.col_list_permi[i_origin]
    @assert SG.light_weight[i_now] > 0
    SG.light_weight[i_now]-=1
    handle_new_light_weight!(i_now, SG)
   end
  end
  SG.nlight -= SG.heavy_ext
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
  end
  return SG
 end
 
 function eliminate_and_update!(best_single_row::Int64, SG::data_ZZStructGauss)::data_ZZStructGauss
  @assert best_single_row != 0
  best_row = deepcopy(SG.A[best_single_row])
  light_idx = find_light_entry(best_row.pos, SG.is_light_col)
  best_col = best_row.pos[light_idx]
  @assert length(SG.col_list[best_col]) > 1
  best_val = deepcopy(SG.A[best_single_row, best_col])
  @assert !iszero(best_val)
  best_col_idces = SG.col_list[best_col]
  row_idx = 0
  while length(best_col_idces) > 1
   row_idx = find_row_to_add_on(row_idx, best_row, best_col_idces, SG)
   #@hassert :StructGauss 1 best_col_idces == SG.col_list[best_col]
   @assert row_idx > 0
   #@hassert :StructGauss SG.col_list_perm[row_idx] in SG.col_list[best_col]
   L_row = SG.col_list_perm[row_idx]
   add_to_eliminate!(L_row, row_idx, best_row, best_col, best_val, SG) #TODO: isone query
   update_after_addition!(L_row, row_idx, best_col, SG)
   handle_new_light_weight!(row_idx, SG)
  end
  return SG
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
 
 function add_to_eliminate!(L_row::Int64, row_idx::Int64, best_row::SRow{T}, best_col::Int64, best_val::ZZRingElem, SG::data_ZZStructGauss)::data_ZZStructGauss where T <: ZZRingElem
  #@hassert :StructGauss L_row in SG.col_list[best_col]
  #@hassert :StructGauss !(0 in SG.A[row_idx].values)
  val = SG.A[row_idx, best_col]
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
   SG.is_light_col[c] && insert!(SG.col_list[c], searchsortedfirst(SG.col_list[c], L_row), L_row)
   SG.is_light_col[c] && (SG.light_weight[row_idx]+=1)
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
   swap_entries(SG.pivot_col, i, j)
   swap_entries(SG.col_list_perm, i, j)
   swap_entries(SG.col_list_permi, SG.col_list_perm[i], SG.col_list_perm[j])
   swap_entries(SG.light_weight, i, j)
  end
 end 
 
 function swap_i_into_base(i::Int64, SG::data_ZZStructGauss)
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

#Compute the kernel corresponding to the non echolonized part from above and
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
  D = dense_matrix(SG, KER)
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

function dense_matrix(SG, KER)
 D = ZZMatrix(nrows(SG.A) - SG.npivots, length(KER.heavy_mapi))
	 for i in 1:length(SG.Y)
	  for j in 1:length(KER.heavy_mapi)
	   setindex!(D, SG.Y[i], i, j, KER.heavy_mapi[j])
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
  lbound = Int64(0)
  DT = transpose(D)
  for i = 1:5
    p = next_prime(2^20 + rand(2:2^10))
    Dp = change_base_ring(Native.GF(p), D)
    crank  = rref!(Dp)
    crank == m && return ZZMatrix(m, 1)
    lbound = crank
    lbound < m-1 && continue
    DTp = change_base_ring(Native.GF(p), DT)
    rrank = rref!(DTp)
    @assert rrank == crank
    c, cpivots = _pivots(Dp, crank, true)
    _, rpivots = _pivots(DTp, rrank)
    @show(c)
    @assert !iszero(c)
    D_red = D[rpivots, cpivots]
    d = D[rpivots, c:c]
    sol = Nemo.dixon_solve(D_red, d)#TODO: use view or alternative
    return vcat(sol[1], ZZMatrix(1,1,[-sol[2]]))#TODO: vcat at position c? why working like this?
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
    - alternatively: ignore rank and use wiedemann
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
    #one!(K[i, _nullity+ilight]) doesn't work inplace
    K[i, _nullity+ilight] = one(ZZ) #TODO
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