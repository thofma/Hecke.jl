#fin. gen. submodules of Z^n and F_p^n (and possibly more)
#
#import Base.show, Base.inv, Nemo.inv, Base.solve, Hecke.solve,
#       Hecke.lift, Hecke.rational_reconstruction, Hecke.elementary_divisors,
#       Hecke.rank, Hecke.det

export det_mc, id, isid, isupper_triangular, norm2, hadamard_bound2, 
       hnf, hnf!, echelon_with_trafo

const p = next_prime(2^20)

add_verbose_scope(:HNF)

add_assert_scope(:HNF)
set_assert_level(:HNF, 0)


function show(io::IO, M::ModuleCtxNmod)
  println("Sparse module over $(M.R) of (current) rank $(rows(M.basis)) and $(rows(M.gens))")
end

function show(io::IO, M::ModuleCtx_fmpz)
  println("Sparse module over FlintZZ of (current) rank $(rows(M.bas_gens)) and further $(rows(M.rel_gens))")
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
    while i<= rows(M.basis) && M.basis.rows[i].pos[1] < h.pos[1]
      i += 1
    end
    @hassert :HNF 2  i > rows(M.basis) || M.basis[i].pos[1] > h.pos[1]
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
  gp = SRow(g, M.Mp.R)
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
  if rows(M.Mp.basis) < cols(M.Mp.basis)
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
    d = abs(det(M.bas_gens))
    C = M.max_indep
    C.c = M.bas_gens.c
    for ii = M.bas_gens
      h = reduce(C, ii, 2*d) #to avoid problems with diag being 1...1 d
      @hassert :HNF 2  !iszero(h)
      i = 1
      while i<= rows(C) && C.rows[i].pos[1] < h.pos[1]
        i += 1
      end
      @hassert :HNF 2  i > rows(C) || C[i].pos[1] > h.pos[1]
      insert!(C.rows, i, h)
      C.r += 1
      C.nnz += length(h)
      C.c = max(C.c, h.pos[end])
    end
    M.max_indep = copy(C)
  end

  for i=length(M.rel_reps_p)+1:length(M.rel_gens)
    reduce(C, M.rel_gens[i])
    push!(M.rel_reps_p, solve_ut(M.Mp.basis, SRow(M.rel_gens[i], M.Mp.R)))
  end

#=
  for l=1:5
    mis = find(i->C[i,i] != 1, 1:rows(C))
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
  M.basis_idx = prod([C[i,i] for i=1:rows(C)])

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
  f = findall(i -> C[i,i] != 1, 1:rows(C))
  if length(f) == 0
    M.essential_elementary_divisors = fmpz[]
    return M.essential_elementary_divisors
  end
  e = minimum(f)
  m = fmpz_mat(sub(C, e:rows(C), e:cols(C)))
  s = snf(m)
  M.essential_elementary_divisors = [s[i,i] for i=1:rows(s)]
  return M.essential_elementary_divisors
end

function missing_pivot(M::ModuleCtx_fmpz)
  C = M.Mp.basis
  return setdiff(BitSet(1:cols(C)), [x.pos[1] for x=C])
end

function non_trivial_pivot(M::ModuleCtx_fmpz)
  h = check_index(M)
  if h == 0 
    return missing_pivot(M)
  end
  C = M.basis
  @hassert :HNF 2  C.r == C.c
  return setdiff(BitSet(1:cols(C)), findall(i->C[i].values[1] == 1, 1:C.c))
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
  z = vcat(M.bas_gens, M.rel_gens)
  h, t = hnf_kannan_bachem(z, Val{true})
  M.trafo = t
  M.basis = h
  M.basis_idx = det(h) # h is upp_triangular, hence det is trivial
  M.new = false
  nothing
end

