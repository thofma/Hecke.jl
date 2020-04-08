function parallel_lll_precomputation(M::NfOrd, prec::Int, nblocks::Int = 4)
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
  #I need first to create all the blocks to do simultaneously.
  done = falses(length(to_do))
  while !all(done)
    blocks_selection = Vector{Int}[]
    block = 1
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
    g = identity_matrix(FlintZZ, n)
    @Threads.threads for i = 1:length(blocks_selection)
      indices = blocks_selection[i]
      g1 = Hecke._lll_sublattice(M, indices, prec = prec)[2]
      Hecke._copy_matrix_into_matrix(g, indices, indices, g1)
    end
    On = NfOrd(K, g*basis_matrix(M, copy = false))
    On.ismaximal = M.ismaximal
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
  @vprint :LLL 3 "Precomputation finished with precision $(prec)\n"
  return prec, M
end
