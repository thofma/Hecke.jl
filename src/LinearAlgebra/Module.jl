#fin. gen. submodules of Z^n and F_p^n (and possibly more)
#
#import Base.show, Base.reduce, Base.inv, Nemo.inv, Base.solve, Hecke.solve,
#       Hecke.lift, Hecke.rational_reconstruction, Hecke.elementary_divisors,
#       Hecke.rank, Hecke.det

const p = next_prime(2^20)
type ModuleCtx_UIntMod
  R::ZZModUInt
  basis::Smat{UIntMod}
  gens::Smat{UIntMod}
  function ModuleCtx_UIntMod()
    return new()
  end
  function ModuleCtx_UIntMod(p::Int, dim::Int)
    M = new()
    M.R = ZZModUInt(UInt(p))
    M.basis = Smat{UIntMod}()
    M.basis.c = dim
    M.gens = Smat{UIntMod}()
    return M
  end
end

type ModuleCtx_fmpz
  bas_gens::Smat{fmpz}  # contains a max. indep system
  max_indep::Smat{fmpz} # the bas_gens in upper-triangular shape
  basis::Smat{fmpz}     # if set, probably a basis (in upper-triangular)
  rel_gens::Smat{fmpz}  # more elements, used for relations
  Mp::ModuleCtx_UIntMod
  rel_reps_p::Smat{UIntMod}  # rel_reps_p[i] * Mp.basis = rel_gens[i] - if set
                        # at least mod p...
  basis_idx::fmpz                      
  essential_elementary_divisors::Array{fmpz, 1}
  function ModuleCtx_fmpz(dim::Int)
    M = new()
    M.max_indep = Smat{fmpz}()
    M.bas_gens = Smat{fmpz}()
    M.bas_gens.c = dim
    M.rel_gens = Smat{fmpz}()
    M.rel_reps_p = Smat{UIntMod}()
    M.Mp = ModuleCtx_UIntMod(p, dim)
    return M
  end
end

function show(io::IO, M::ModuleCtx_UIntMod)
  println("Module over $(M.R) of (current) rank $(rows(M.basis)) and $(rows(M.gens))")
end
function show(io::IO, M::ModuleCtx_fmpz)
  println("Module over FlintZZ of (current) rank $(rows(M.bas_gens)) and further $(rows(M.rel_gens))")
  if isdefined(M, :basis_idx)
    println("current index: $(M.basis_idx)")
  end
  if isdefined(M, :essential_elementary_divisors)
    println("current structure: $(M.essential_elementary_divisors)")
  end
end

function reduce(A::Smat{UIntMod}, g::SmatRow{UIntMod})
  @assert isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  # supposed to be a field...
  if A.r == A.c
    return SmatRow{UIntMod}()
  end
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      break
    end
    @assert A.rows[j].pos[1] == g.pos[1]
    @assert (A.rows[j].values[1]) == 1
    p = g.values[1]
    g = Hecke.add_scaled_row(A[j], g, -p)
    @assert length(g)==0 || g.pos[1] > A[j].pos[1]
  end
  if length(g) > 0
    li = inv(g.values[1])
    for i=1:length(g)
      g.values[i] *= li
    end
  end
  return g
end

function inv(x::UIntMod)
  return 1//x
end

#returns true if g enlarged M
function add_gen!(M::ModuleCtx_UIntMod, g::SmatRow{UIntMod})
  if M.basis.r == M.basis.c
    return false
  end
  h = reduce(M.basis, g)
  if !iszero(h)
    i = 1
    while i<= rows(M.basis) && M.basis.rows[i].pos[1] < h.pos[1]
      i += 1
    end
    @assert i > rows(M.basis) || M.basis[i].pos[1] > h.pos[1]
    insert!(M.basis.rows, i, h)
    M.basis.r += 1
    M.basis.nnz += length(h)
    M.basis.c = max(M.basis.c, h.pos[end])
    push!(M.gens, g)
    return true
  end
  return false 
end

function reduce(A::Smat{fmpz}, g::SmatRow{fmpz})
  @assert isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      if g.values[1] < 0
        for i=1:length(g.values)
          g.values[i] *= -1
        end
      end
      return g
    end
    h = typeof(g)()
    st_g = 2
    st_A = 2
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      g = Hecke.add_scaled_row(A[j], g, - divexact(p, A.rows[j].values[1]))
      @assert length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @assert x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      @assert A[j].values[1] == x
      @assert length(g)==0 || g.pos[1] > A[j].pos[1]
    end
  end
  if length(g.values) > 0 && g.values[1] < 0
    for i=1:length(g.values)
      g.values[i] *= -1
    end
  end
  return g
end

function reduce(A::Smat{fmpz}, g::SmatRow{fmpz}, m::fmpz)
  @assert isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      if g.values[1] < 0 || g.values[1] >= div(m, 2)
        for i=1:length(g.values)
          g.values[i] *= -1
        end
      end
      Hecke.mod_sym!(g, m)
      return g
    end
    st_g = 2
    st_A = 2
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      g = Hecke.add_scaled_row(A[j], g, - divexact(p, A.rows[j].values[1]))
      Hecke.mod_sym!(g, m)
      @assert length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @assert x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      Hecke.mod_sym!(g, m)
      Hecke.mod_sym!(A[j], m)
      @assert A[j].values[1] == x
      @assert length(g)==0 || g.pos[1] > A[j].pos[1]
    end
  end
  if length(g.values) > 0 && mod_sym(g.values[1], m) < 0
    for i=1:length(g.values)
      g.values[i] *= -1
    end
  end
  Hecke.mod_sym!(g, m)
  return g
end

doc"""
    norm2(A::SmatRow{fmpz})

> The square of the euclidean norm of $A$.
"""
function norm2(A::SmatRow{fmpz})
  return sum([x*x for x= A.values])
end

doc"""
    hadamard_bound2(A::Smat{fmpz})

> The square of the product of the norms of the rows of $A$.
"""
function hadamard_bound2(A::Smat{fmpz})
  return prod([norm2(x) for x=A])
end

function add_gen!(M::ModuleCtx_fmpz, g::SmatRow{fmpz})
  gp = SmatRow(g, M.Mp.R)
  if add_gen!(M.Mp, gp)
    push!(M.bas_gens, g)
    return true


    return true
  else
    push!(M.rel_gens, g)
  end
  return false 
end

function check_index(M::ModuleCtx_fmpz)
  if rows(M.Mp.basis) < cols(M.Mp.basis)
    return fmpz(0)
  end

  if isdefined(M, :basis)
    C = copy(M.basis)
  else
    d = det(M.bas_gens)
    C = M.max_indep
    C.c = M.bas_gens.c
    for i=M.bas_gens
      h = reduce(C, i, 2*d) #to avoid problems with diag being 1...1 d
      @assert !iszero(h)
      i = 1
      while i<= rows(C) && C.rows[i].pos[1] < h.pos[1]
        i += 1
      end
      @assert i > rows(C) || C[i].pos[1] > h.pos[1]
      insert!(C.rows, i, h)
      C.r += 1
      C.nnz += length(h)
      C.c = max(C.c, h.pos[end])
    end
    M.max_indep = copy(C)
  end

  for i=length(M.rel_reps_p)+1:length(M.rel_gens)
    push!(M.rel_reps_p, solve(M.Mp.basis, SmatRow(M.rel_gens[i], M.Mp.R)))
  end

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
      g = M.rel_gens[rand(r)]
      for j=1:min(5, div(length(r), 2))
        g += M.rel_gens[rand(r)]
      end
      println(reduce(C, g))
      if C[i,i] == 1
#        println("bingo for i=$i")
      end
    end
  end

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
  f = find(i -> C[i,i] != 1, 1:rows(C))
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
  return setdiff(1:cols(C), [x.pos[1] for x=C])
end

function non_trivial_pivot(M::ModuleCtx_fmpz)
  h = check_index(M)
  if h == 0 
    return missing_pivot(M)
  end
  C = M.basis
  @assert C.r == C.c
  return setdiff(1:cols(C), find(i->C[i].values[1] == 1, 1:C.c))
end

function rank(M::ModuleCtx_fmpz)
  return M.max_indep.r
end

function rank(M::ModuleCtx_UIntMod)
  return M.basis.r
end

function solve(A::Smat{UIntMod}, g::SmatRow{UIntMod})
  @assert cols(A) == rows(A)
  @assert isupper_triangular(A)
  # assumes A is upper triangular, reduces g modulo A to zero and collects
  # the tansformation
  # supposed to be a field...

  sol = typeof(g)()

  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      break
    end
    @assert A.rows[j].pos[1] == g.pos[1]
    p = g.values[1]//A.rows[j].values[1]
    push!(sol.pos, j)
    push!(sol.values, p)
    g = Hecke.add_scaled_row(A[j], g, -p)
    @assert length(g)==0 || g.pos[1] > A[j].pos[1]
  end
  if length(g) > 0
    li = inv(g.values[1])
    for i=1:length(g)
      g.values[i] *= li
    end
  end
  return sol
end

doc"""
    lift(a::SmatRow{UIntMod}) -> SmatRow{fmpz}

> Lifts all entries in $a$.
"""
function lift(a::SmatRow{UIntMod})
  b = SmatRow{fmpz}()
  for (p,v) = a
    push!(b.pos, p)
    push!(b.values, fmpz(v.m))
  end
  return b
end

#TODO: write vector reconstruction and use it here.
doc"""
    rational_reconstruction(A::SmatRow{fmpz}, M::fmpz) -> Bool, SmatRow{fmpz}, fmpz

> Apply rational reconstruction to the entries of $A$. Returns true iff 
> successful. In this case, the numerator is returned as a matrix and the 
> common denominator in the third value.
"""
function rational_reconstruction(A::SmatRow{fmpz}, M::fmpz)
  B = SmatRow{fmpz}()
  de = fmpz(1)
  for (p,v) = A
    fl, n, d = rational_reconstruction(v, M)
    if !fl
      return false, B, de
    end
    if de % d == 0
      push!(B.pos, p)
      push!(B.values, n*(div(de, d)))
    else
      l = lcm(d, de)
      B = div(l, de) * B
      push!(B.pos, p)
      push!(B.values, div(l, d)*n)
      de = l
    end
  end
  return true, B, de
end
   
function dixon_solve(A::Smat{fmpz}, b::SmatRow{fmpz})
  @assert isupper_triangular(A)
  #assumes A to be upper triangular of full rank - for now at least

  p = next_prime(2^20)
  b_orig = b

  Ap = Smat(A, p)
  bp = SmatRow(b, p)

  sol = SmatRow{fmpz}()

  pp = fmpz(1)

  last = (sol, 1)
  while true
    zp = solve(Ap, bp)
#    @assert Hecke.mul(zp, Ap) == bp

    z = lift(zp)
#    @assert SmatRow(z, p) == zp

    sol += pp*z

    pp *= fmpz(p)
    if nbits(pp) > 10000
      error("too large")
    end

#    @assert iszero(SmatRow(b_orig - Hecke.mul(sol, A), pp)) 

    fl, nu, de = rational_reconstruction(sol, pp)
    if fl 
#      @assert SmatRow(de*sol, pp) == SmatRow(nu, pp)
#      @assert SmatRow(mul(nu, A), pp) == SmatRow(de*b_orig, pp)
      if last == (nu, de)
        if Hecke.mul(nu, A) == de*b_orig
          return nu, de
        end
        println("bad")
      else
        last = (nu, de)
      end
    end

#    @assert SmatRow(Hecke.mul(z, A), p) == bp
    b = b - Hecke.mul(z, A)

    for i=1:length(b.values)
#      @assert b.values[i] % p == 0
      b.values[i] = div(b.values[i], p)
    end
    bp = SmatRow(b, p)
  end
end

function direct_solve(A::Smat{fmpz}, b::SmatRow{fmpz})
  @assert isupper_triangular(A)
  #still assuming A to be upper-triag

  sol = SmatRow{fmpz}()
  den = fmpz(1)
  while length(b) > 0
    p = b.pos[1]
    v = b.values[1]
    d = gcd(A[p].values[1], v)
    if d != A[p].values[1]  # A does not divide b, the RHSS
      f = div(A[p].values[1], d)
      sol = f * sol
      b = f * b
      v *= f
      den *= f
    end
    push!(sol.pos, p)
    @assert Smat(v, A[p].values[1]) == 0
    push!(sol.values, div(v, A[p].values[1]))
    b = b - sol.values[end]*A[p]
    @assert length(b) == 0 || b.pos[1] > p
  end
  return sol, den
end

doc"""
    isupper_triangular(A::Smat)
 
> Returns true iff $A$ is upper triangular.
"""
function isupper_triangular(A::Smat)
  for i=2:A.r
    if A[i-1].pos[1] >= A[i].pos[1]
      return false
    end
  end
  return true
end

#TODO: to Kannem-Bachem style reduction which avoids the blow up
#      also, do the "same" in reduce further up whenever
#      a pivot changes
function full_echelon!(A::Smat{fmpz})
  @assert isupper_triangular(A)
  for i=2:A.r
    for j=i-1:-1:1
      A[j] = A[j] - div(A[j, A[i].pos[1]], A[i].values[1])*A[i]
      @assert length(find(iszero, A[j].values)) == 0
    end
  end
end

function full_echelon(A::Smat{fmpz})
  B = copy(A)
  full_echelon!(B)
  return B
end

doc"""
    det_mc(A::Smat{fmpz}

> Computes the determinant of $A$ using a LasVegas style algorithm,
> ie. the result is not proven to be correct.
"""
function det_mc(A::Smat{fmpz})
  @assert A.r == A.c
  if isupper_triangular(A)
    return prod([A[i,i] for i=1:A.r])
  end
  
  q = p
  first = true
  dd = fmpz(1)
  mm = fmpz(1)
  last = fmpz(0)
  while true
    d = det(nmod_mat(Smat(A, q)))
    if first
      dd = fmpz(d)
      mm = fmpz(q)
      first = false
    else
      dd = crt(dd, mm, fmpz(d), fmpz(q), true)
      mm *= q
    end
    q = next_prime(q)
    if dd == last
      return dd
    else
      last = dd
    end
  end
end

doc"""
    det(A::Smat{fmpz})

> The determinant of $A$ using a modular algorithm.
"""
function det(A::Smat{fmpz})
  @assert A.r == A.c
  if isupper_triangular(A)
    return prod([A[i,i] for i=1:A.r])
  end

  b = div(nbits(hadamard_bound2(A)), 2)
  lp = fmpz[p]
  while b > 0
    push!(lp, next_prime(lp[end]))
    b -= nbits(lp[end])
  end

  #TODO: re-use the nmod_mat....
  ld = [fmpz(det(nmod_mat(Smat(A, Int(q))))) for q = lp]
  return crt_signed(ld, crt_env(lp))
end

