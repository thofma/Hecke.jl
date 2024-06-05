################################################################################
#
#  Minkowski matrix
#
################################################################################

function minkowski_matrix_parallel(O::AbsSimpleNumFieldOrder, abs_tol::Int = 64)
  if isdefined(O, :minkowski_matrix) && O.minkowski_matrix[2] > abs_tol
    A = deepcopy(O.minkowski_matrix[1])
  else
    T = Vector{Vector{ArbFieldElem}}(undef, degree(O))
    B = O.basis_nf
    @Threads.threads for i in 1:degree(O)
      T[i] = minkowski_map(B[i], abs_tol)
    end
    p = maximum(Int[ precision(parent(T[i][j])) for i in 1:degree(O), j in 1:degree(O) ])
    M = zero_matrix(ArbField(p, cached = false), degree(O), degree(O))
    for i in 1:degree(O)
      for j in 1:degree(O)
        M[i, j] = T[i][j]
      end
    end
    O.minkowski_matrix = (M, abs_tol)
    A = deepcopy(M)
  end
  return A
end

@doc raw"""
    minkowski_gram_mat_scaled(O::AbsSimpleNumFieldOrder, prec::Int = 64) -> ZZMatrix

Let $c$ be the Minkowski matrix as computed by `minkowski_matrix` with precision $p$.
This function computes $d = round(c 2^p)$ and returns $round(d d^t/2^p)$.
"""
function minkowski_gram_mat_scaled_parallel(O::AbsSimpleNumFieldOrder, prec::Int = 64)
  if isdefined(O, :minkowski_gram_mat_scaled) && O.minkowski_gram_mat_scaled[2] >= prec
    A = deepcopy(O.minkowski_gram_mat_scaled[1])
    Hecke.shift!(A, prec - O.minkowski_gram_mat_scaled[2])
  else
    c = minkowski_matrix_parallel(O, prec)
    d = zero_matrix(FlintZZ, degree(O), degree(O))
    A = zero_matrix(FlintZZ, degree(O), degree(O))
    round_scale!(d, c, prec)
    ccall((:fmpz_mat_gram, libflint), Nothing, (Ref{ZZMatrix}, Ref{ZZMatrix}), A, d)
    Hecke.shift!(A, -prec)
    O.minkowski_gram_mat_scaled = (A, prec)
    A = deepcopy(A)
  end
  # to ensure pos. definitenes, we add n to the diag.
  for i=1:degree(O)
    A[i, i] += nrows(A)
  end
  return A
end


function parallel_lll_precomputation(M::AbsSimpleNumFieldOrder, prec::Int, nblocks::Int = 4)
  n = degree(M)
  K = nf(M)
  dimension_blocks = div(n, nblocks)
  blocks = Vector{Int}[]
  for i = 1:nblocks-1
    int = (dimension_blocks*(i-1)+1):dimension_blocks*i
    push!(blocks, collect(int))
  end
  int = (dimension_blocks*(nblocks-1)+1):n
  push!(blocks, collect(int))
  new_prec = prec
  to_do = Hecke.subsets(blocks, 2)
  @vprintln :LLL 3 "Subsets computed"
  #I need first to create all the blocks to do simultaneously.
  done = falses(length(to_do))
  while !all(done)
    blocks_selection = Vector{Int}[]
    block = 1
    @vprintln :LLL 3 "Starting block selection"
    while block < length(to_do)+1
      while block < length(to_do)+1 && (done[block] || !Hecke._has_trivial_intersection(to_do[block], blocks_selection))
        block += 1
      end
      if block == length(to_do)+1
        break
      end
      done[block] = true
      indices = vcat(to_do[block][1], to_do[block][2])
      push!(blocks_selection, indices)
      block += 1
    end
    @vprintln :LLL 3 "Blocks selection finished"
    g = identity_matrix(FlintZZ, n)
    while true
      try
        Hecke.minkowski_gram_mat_scaled(M, prec)
	    break
      catch e
        prec *= 2
      end
    end
    @vprintln :LLL 3 "Start computation"
    @Threads.threads for i = 1:length(blocks_selection)
      indices = blocks_selection[i]
      g1 = Hecke._lll_sublattice(M, indices, prec = prec)[2]
      Hecke._copy_matrix_into_matrix(g, indices, indices, g1)
    end
    On = AbsSimpleNumFieldOrder(K, g*basis_matrix(M, copy = false))
    On.is_maximal = M.is_maximal
    if isdefined(M, :index)
      On.index = M.index
    end
    if isdefined(M, :disc)
      On.disc = M.disc
    end
    if isdefined(M, :gen_index)
      On.gen_index = M.gen_index
    end
    M = On
  end
  @vprintln :LLL 3 "Precomputation finished with precision $(prec)"
  return prec, M
end
