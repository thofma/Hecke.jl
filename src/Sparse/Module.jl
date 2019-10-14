#fin. gen. submodules of Z^n and F_p^n (and possibly more)
#
#import Base.show, Base.inv, Nemo.inv, Base.solve, Hecke.solve,
#       Hecke.lift, Hecke.rational_reconstruction, Hecke.elementary_divisors,
#       Hecke.rank, Hecke.det

export det_mc, id, isupper_triangular, norm2, hadamard_bound2, 
       hnf, hnf!, echelon_with_transform

add_verbose_scope(:HNF)

add_assert_scope(:HNF)
set_assert_level(:HNF, 0)


function show(io::IO, M::ModuleCtxNmod)
  println("Sparse module over $(M.R) of (current) rank $(nrows(M.basis)) and $(nrows(M.gens))")
end

function show(io::IO, M::ModuleCtx_fmpz)
  println("Sparse module over FlintZZ of (current) rank $(nrows(M.bas_gens)) and further $(nrows(M.rel_gens))")
  if isdefined(M, :basis_idx)
    println("current index: $(M.basis_idx)")
  end
  if isdefined(M, :essential_elementary_divisors)
    println("current structure: $(M.essential_elementary_divisors)")
  end
end

function add_gen!(M::ModuleCtxNmod, g::SRow{nmod})
  if M.basis.r == M.basis.c
    return false
  end
  h = reduce(M.basis, g)
  if !iszero(h)
    i = 1
    while i<= nrows(M.basis) && M.basis.rows[i].pos[1] < h.pos[1]
      i += 1
    end
    @hassert :HNF 2  i > nrows(M.basis) || M.basis[i].pos[1] > h.pos[1]
    insert!(M.basis.rows, i, h)
    M.basis.r += 1
    M.basis.nnz += length(h)
    M.basis.c = max(M.basis.c, h.pos[end])
    push!(M.gens, g)
    return true
  end
  return false 
end

function add_gen!(M::ModuleCtx_fmpz, g::SRow{fmpz}, always::Bool = true)
  gp = change_ring(g, M.Mp.R)
  M.new = true
  if add_gen!(M.Mp, gp)
    push!(M.bas_gens, g)
    return true
  else
    always && push!(M.rel_gens, g)
  end
  return false 
end

function check_index(M::ModuleCtx_fmpz)
  if nrows(M.Mp.basis) < ncols(M.Mp.basis)
    return fmpz(0)
  end

  if !M.new
    return M.basis_idx
  end

  if isdefined(M, :trafo)  #once we have trafo, we need to keep it!
    module_trafo_assure(M)
    return M.basis_idx
  end

  M.new = false


  if isdefined(M, :basis)
    C = copy(M.basis)
  else
    d = abs(det_mc(M.bas_gens))
    C = M.max_indep
    C.c = M.bas_gens.c
    for ii = M.bas_gens
      h = reduce(C, ii, 2*d) #to avoid problems with diag being 1...1 d
      @hassert :HNF 2  !iszero(h)
      i = 1
      while i<= nrows(C) && C.rows[i].pos[1] < h.pos[1]
        i += 1
      end
      @hassert :HNF 2  i > nrows(C) || C[i].pos[1] > h.pos[1]
      insert!(C.rows, i, h)
      C.r += 1
      C.nnz += length(h)
      C.c = max(C.c, h.pos[end])
    end
    M.max_indep = copy(C)
  end

  for i=length(M.rel_reps_p)+1:length(M.rel_gens)
    reduce(C, M.rel_gens[i])
    push!(M.rel_reps_p, solve_ut(M.Mp.basis, change_ring(M.rel_gens[i], M.Mp.R)))
  end

#=
  for l=1:5
    mis = find(i->C[i,i] != 1, 1:nrows(C))
    if length(mis) == 0
      break
    end
#    println("mis: $mis")
    for i = mis
      if C[i,i] == 1
#        println("miracle for $i")
        continue
      end
      r = find(x->i in M.rel_reps_p[x].pos, 1:length(M.rel_reps_p))
#      println("found $(length(r)) rows")
      if length(r) == 0
        break
      end
      g = M.rel_gens[rand(r)]
      for j=1:min(5, div(length(r), 2))
        g += rand(-10:10)*M.rel_gens[rand(r)]
      end
      reduce(C, g)
      if C[i,i] == 1
#        println("bingo for i=$i")
      end
    end
  end
=#
  M.basis = C
  M.basis_idx = prod([C[i,i] for i=1:nrows(C)])

  return M.basis_idx
end

function elementary_divisors(M::ModuleCtx_fmpz)
  if !isdefined(M, :basis)
    i = check_index(M)
    if i == 0
      return fmpz[]
    end
  end
  C = M.basis
  f = find(i -> C[i,i] != 1, 1:nrows(C))
  if length(f) == 0
    M.essential_elementary_divisors = fmpz[]
    return M.essential_elementary_divisors
  end
  e = minimum(f)
  m = fmpz_mat(sub(C, e:nrows(C), e:ncols(C)))
  s = snf(m)
  M.essential_elementary_divisors = [s[i,i] for i=1:nrows(s)]
  return M.essential_elementary_divisors
end

function missing_pivot(M::ModuleCtx_fmpz)
  C = M.Mp.basis
  return setdiff(BitSet(1:ncols(C)), [x.pos[1] for x=C])
end

function non_trivial_pivot(M::ModuleCtx_fmpz)
  h = check_index(M)
  if h == 0 
    return missing_pivot(M)
  end
  C = M.basis
  @hassert :HNF 2  C.r == C.c
  return setdiff(BitSet(1:ncols(C)), findall(i->C[i].values[1] == 1, 1:C.c))
end

function rank(M::ModuleCtx_fmpz)
  return M.bas_gens.r
end

function rank(M::ModuleCtxNmod)
  return M.basis.r
end

function module_trafo_assure(M::ModuleCtx_fmpz)

  if !M.new && isdefined(M, :trafo)
    return
  end
  if isdefined(M, :trafo)
    st = M.done_up_to + 1
    _, t = hnf_extend!(M.basis, sub(M.rel_gens, st:nrows(M.rel_gens), 1:ncols(M.rel_gens)), Val{true}, offset = st-1, truncate = true)
    append!(M.trafo, t)

  else
    z = vcat(M.bas_gens, M.rel_gens)
    h, t = hnf_kannan_bachem(z, Val{true}, truncate = true)
    M.trafo = t
    M.basis = h
  end
  M.done_up_to = nrows(M.rel_gens)
  M.basis_idx = det(M.basis) # h is upp_triangular, hence det is trivial
  @assert M.basis_idx > 0
  M.new = false

  nothing
end

