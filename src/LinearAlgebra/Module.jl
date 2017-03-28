#fin. gen. submodules of Z^n and F_p^n (and possibly more)
#
#import Base.show, Base.reduce, Base.inv, Nemo.inv, Base.solve, Hecke.solve,
#       Hecke.lift, Hecke.rational_reconstruction, Hecke.elementary_divisors,
#       Hecke.rank, Hecke.det

import Base.reduce
export det_mc, id, isid, isupper_triangular, norm2, hadamard_bound2, 
       hnf, hnf!, echelon_with_trafo

const p = next_prime(2^20)

add_verbose_scope(:HNF)

add_assert_scope(:HNF)
set_assert_level(:HNF, 0)


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
############################################################
##
############################################################
function reduce(A::Smat{UIntMod}, g::SmatRow{UIntMod})
  @hassert :HNF 1  isupper_triangular(A)
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
    @hassert :HNF 2  A.rows[j].pos[1] == g.pos[1]
    @hassert :HNF 2  (A.rows[j].values[1]) == 1
    p = g.values[1]
    g = Hecke.add_scaled_row(A[j], g, -p)
    @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
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

function reduce(A::Smat{fmpz}, g::SmatRow{fmpz})
  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  #until the 1st (pivot) change in A
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
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      g = Hecke.add_scaled_row(A[j], g, - divexact(p, A.rows[j].values[1]))
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @hassert :HNF 2  x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      @hassert :HNF 2  A[j].values[1] == x
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
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
  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A
  new_g = false
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      if !new_g
        g = copy(g)
      end
      if mod_sym(g.values[1], m) < 0 
        for i=1:length(g.values)
          g.values[i] *= -1
        end
        @hassert :HNF 3  mod_sym(g.values[1], m) > 0
      end
      mod_sym!(g, m)
      return g
    end
    st_g = 2
    st_A = 2
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      g = add_scaled_row(A[j], g, - divexact(p, A.rows[j].values[1]))
      new_g = true
      mod_sym!(g, m)
      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @hassert :HNF 2  x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      new_g = true
#      @hassert :HNF 2  A[j].values[1] == x
      mod_sym!(g, m)
      mod_sym!(A[j], m)
#      @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
#      @hassert :HNF 2  A[j].values[1] > 0
    end
  end
  if !new_g
    g = copy(g)
  end
  if length(g.values) > 0 && mod_sym(g.values[1], m) < 0
    for i=1:length(g.values)
      g.values[i] *= -1
    end
  end
  Hecke.mod_sym!(g, m)
#  @hassert :HNF 1  length(g.pos) == 0 || g.values[1] >= 0
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
  M.new = true
  if add_gen!(M.Mp, gp)
    push!(M.bas_gens, g)
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

  if !M.new
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
      if length(r) == 0
        break
      end
      g = M.rel_gens[rand(r)]
      for j=1:min(5, div(length(r), 2))
        g += M.rel_gens[rand(r)]
      end
      reduce(C, g)
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
  @hassert :HNF 2  C.r == C.c
  return setdiff(1:cols(C), find(i->C[i].values[1] == 1, 1:C.c))
end

function rank(M::ModuleCtx_fmpz)
  return M.bas_gens.r
end

function rank(M::ModuleCtx_UIntMod)
  return M.basis.r
end

function solve(A::Smat{UIntMod}, g::SmatRow{UIntMod})
  @hassert :HNF 1  cols(A) == rows(A)
  @hassert :HNF 2  isupper_triangular(A)
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
    @hassert :HNF 2  A.rows[j].pos[1] == g.pos[1]
    p = g.values[1]//A.rows[j].values[1]
    push!(sol.pos, j)
    push!(sol.values, p)
    g = Hecke.add_scaled_row(A[j], g, -p)
    @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
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
   
function solve_ut(A::Smat{fmpz}, b::SmatRow{fmpz})
  @hassert :HNF 1  isupper_triangular(A)
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
    @hassert :HNF 2  mod(v, A[p].values[1]) == 0
    push!(sol.values, div(v, A[p].values[1]))
    b = b - sol.values[end]*A[p]
    @hassert :HNF 2  length(b) == 0 || b.pos[1] > p
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

doc"""
    det_mc(A::Smat{fmpz}

> Computes the determinant of $A$ using a LasVegas style algorithm,
> ie. the result is not proven to be correct.
> Uses the dense (nmod_mat) determinant on $A$ for various primes $p$.
"""
function det_mc(A::Smat{fmpz})
  @hassert :HNF 1  A.r == A.c
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
> Uses the dense (nmod_mat) determinant on $A$ for various primes $p$.
"""
function det(A::Smat{fmpz})
  @hassert :HNF 1  A.r == A.c
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

doc"""
    id{T}(::Type{Smat{T}}, n::Int) -> Smat{T}

> The $n\times n$ identity matrix as a Smat of type T.
"""
function id{T}(::Type{Smat{T}}, n::Int)
  A = Smat{T}()
  for i=1:n
    push!(A, SmatRow{T}([(i, T(1))]))
  end
  return A
end

doc"""
    id{S}(::Type{Smat}, R::S, n::Int) -> Smat{elem_type(R)}
    
> The $n \times n$ identity over $R$ as a Smat.
> Necessary if $T(1)$ for the type $T$ does not work.
"""
function id{S}(::Type{Smat}, R::S, n::Int)
  T = elem_type(R)
  A = Smat{T}()
  for i=1:n
    push!(A, SmatRow{T}([(i, R(1))]))
  end
  return A
end

doc"""
    isid{T}(A::Smat{T})

> Tests if $A$ is the $n \times n$ identity.
"""
function isid{T}(A::Smat{T})
  if A.c != A.r
    return false
  end
  for i = 1:A.r
    if length(A.rows[i].pos) != 1
      return false
    end
    if A.rows[i].pos[1] != i ||
       !isone(A.rows[i].values[1])
      return false
    end
  end
  return true
end

doc"""
    echelon_with_trafo(A::Smat{UIntMod}) -> Smat, Smat

> Find a unimodular matrix $T$ and an upper-triangular $E$ s.th.
> $TA = E$ holds.
"""
function echelon_with_trafo(A::Smat{UIntMod})
  z = hcat(A, id(Smat, base_ring(A), A.r))
  M = Hecke.ModuleCtx_UIntMod(Int(base_ring(A).mod.n), z.c)
  for i=z
    Hecke.add_gen!(M, i)
  end
  return sub(M.basis, 1:A.r, 1:A.c), sub(M.basis, 1:A.r, A.c+1:z.c)
end

doc"""
    solve_dixon_sf(A::Smat{fmpz}, b::SmatRow{fmpz}, is_int::Bool = false) -> SmatRow{fmpz}, fmpz
    solve_dixon_sf(A::Smat{fmpz}, B::Smat{fmpz}, is_int::Bool = false) -> Smat{fmpz}, fmpz

> For an upper-triangular sparse matrix $A$ and a sparse matrix (row), find
> a sparse matrix (row) $x$ and an integer $d$ s.th.
> $$x A = bd$$
> holds.
> The algorithm is a Dixon-based linear p-adic lifting method.
> If \code{is_int} is given, then $d$ is assumed to be $1$. In this case
> rational reconstriction is avoided.
"""
function solve_dixon_sf(A::Smat{fmpz}, b::SmatRow{fmpz}, is_int::Bool = false)
  B = Smat{fmpz}()
  push!(B, b)
  s, d = solve_dixon_sf(A, B, is_int)
  return s[1], d
end

function solve_dixon_sf(A::Smat{fmpz}, B::Smat{fmpz}, is_int::Bool = false)
  #for square matrices (s) of full rank (f) only.
  p = next_prime(2^20)

  Ap = Smat(A, p)

  #want AT = upper_triag.
  #Let J = anti-identity, so JA inverts the rows of A and AJ the columns
  #
  # B := (JA)' = A'J and TB = E in upper triag
  # J (TB)' J = JE'J is still upper triag and
  # J (TB)' J = J B' T' J = J (JA) T' J = A (JT)' = JE'J still upp-triag

  Bp = copy(Ap)
  invert_rows!(Bp)
  Bp = Bp'
  Ep, Tp = echelon_with_trafo(Bp)
  @hassert :HNF 1  Ep.c == Ep.r
#  @hassert :HNF 1  nmod_mat(Tp) * nmod_mat(Bp) == nmod_mat(Ep)

  invert_rows!(Ep)
  Ep = Ep'
  invert_rows!(Ep)
#  @hassert :HNF 1  Hecke.isupper_triangular(Ep)

  invert_rows!(Tp)
  Tp = Tp'
#  @hassert :HNF 1  nmod_mat(Ap)*nmod_mat(Tp) == nmod_mat(Ep)

  #now, to solve xA = b, we do
  #              xAT = bT since AT is upper-triag, we can do this!

  sol_all = Smat{fmpz}()
  den_all = fmpz(1)

  for b in B
    pp = fmpz(1)
    b_orig = b

    bp = SmatRow(b, p)

    sol = SmatRow{fmpz}()
    last = (sol, 1)

    while true
      bp = mul(bp, Tp)
      zp = solve(Ep, bp)
      z = lift(zp)

      sol += pp*z

      pp *= fmpz(p)

  #    @hassert :HNF 1  iszero(SmatRow(b_orig - Hecke.mul(sol, A), pp)) 

      if is_int
        fl = true
        nu = copy(sol)
        Hecke.mod_sym!(nu, pp)
        de = fmpz(1)
      else
        fl, nu, de = rational_reconstruction(sol, pp)
      end
      if fl 
  #      @hassert :HNF 1  SmatRow(de*sol, pp) == SmatRow(nu, pp)
  #      @hassert :HNF 1  SmatRow(mul(nu, A), pp) == SmatRow(de*b_orig, pp)
        if last == (nu, de)
          if Hecke.mul(nu, A) == de*b_orig
            l = lcm(den_all, de)
            if l == den_all
              push!(sol_all, div(l, de)*nu)
            else
              sol_all = div(l, den_all)*sol_all
              push!(sol_all, div(l, de)*nu)
              den_all = l
            end
            break
          end
          println("bad")
        else
          last = (nu, de)
        end
      end

  #    @hassert :HNF 1  SmatRow(Hecke.mul(z, A), p) == bp
      b = b - Hecke.mul(z, A)

      for i=1:length(b.values)
  #      @hassert :HNF 1  b.values[i] % p == 0
        b.values[i] = div(b.values[i], p)
      end  
      bp = SmatRow(b, p)
    end
  end
  return sol_all, den_all
end

doc"""
    saturate(A::fmpz_mat) -> fmpz_mat
    saturate(A::Smat{fmpz}) -> Smat{fmpz}

> Computes the \code{saturation} of $A$, ie. a basis for $Q\otimes [A] \meet Z^n$.
> Equivalently, $TA$ for $T \in \Gl(n, Q)$ s.th. $TA\in Z^{n\times m}$ and
> the elementary divisors of $TA$ are all trivial.
> The Smat-case is using the dense code.
"""
function saturate(A::fmpz_mat)
  #row saturation: want
  #  TA in Z, T in Q and elem_div TA = [1]
  #
  #  AT = H (in HNF), then A = HT^-1 and H^-1A = T^-1
  # since T is uni-mod, H^-1 A is in Z with triv. elm. div

  H = hnf(A')
  H = H'
  Hi, d = pseudo_inv(sub(H, 1:rows(H), 1:rows(H)))
  S = Hi*A
  Sd = divexact(S, d)
#  @hassert :HNF 1  d*Sd == S
  return Sd
end

function saturate(A::Smat{fmpz})
  return Smat(saturate(fmpz_mat(A)))
end

################################################################################
#
#  Hermite normal form using Kannan-Bachem algorithm
#
################################################################################

doc"""
    find_row_starting_with(A::Smat, p::Int)
 
> Tries to find the index $i$ s.th. $A[i,p] != 0$ and $A[i, p-j] = 0$
> holds for all $j$.
> Assumes $A$ to be upper-triangular.
> If such an index does not exist, find the smallest index
> larger.
"""
function find_row_starting_with(A::Smat, p::Int)
#  @hassert :HNF 1  isupper_triangular(A)
  start = 0
  stop = rows(A)+1
  while start < stop - 1
    mid = div((stop + start), 2)
    if A[mid].pos[1] == p
      return mid
    elseif A[mid].pos[1] < p
      start = mid 
    else
      stop = mid 
    end
  end
  return stop
end

# If trafo is set to Val{true}, then additionaly an Array of transformations
# is returned.
function reduce_up{N}(A::Smat{fmpz}, piv::Array{Int, 1},
                                     trafo::Type{Val{N}} = Val{false})

  with_trafo = (trafo == Val{true})
  if with_trafo
    trafos = []
  end

  sort!(piv)
  p = find_row_starting_with(A, piv[end])

  for red=p-1:-1:1
    # the last argument should be the smallest pivot larger then pos[1]
    if with_trafo
      A[red], new_trafos = reduce_right(A, A[red], max(A[red].pos[1]+1, piv[1]), trafo)
      for t in new_trafos
        t.j = red
      end
      append!(trafos, new_trafos)
    else
      A[red] = reduce_right(A, A[red], max(A[red].pos[1]+1, piv[1]))
    end
  end
  with_trafo ? (return trafos) : nothing
end

# If trafo is set to Val{true}, then additionaly an Array of transformations
# is returned.
doc"""
    reduce_full(A::Smat{fmpz}, g::SmatRow{fmpz}, trafo::Type{Val{Bool}} = Val{false})

> Reduces $g$ modulo $A$, that is, all entries in $g$ in columns where $A$ has
> pivot elements for those columns, reduce $g$ modulo the pivots.
> Assumes $A$ to be upper-triangular.  
>
> The second return value is the array of pivot element of $A$ that
> changed.
>
> If `trafo` is set to `Val{true}`, then additionally an array of transformations
> is returned.
"""
function reduce_full{T}(A::Smat{fmpz}, g::SmatRow{fmpz}, trafo::Type{Val{T}} = Val{false})
#  @hassert :HNF 1  isupper_triangular(A)
  #assumes A is upper triangular, reduces g modulo A

  with_trafo = (trafo == Val{true})
  no_trafo = (trafo == Val{false})

  if with_trafo
    trafos = []
  end 

  piv = Int[]
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      if g.values[1] < 0
        # Multiply row g by -1
        if with_trafo
          push!(trafos, TrafoScale{fmpz}(rows(A) + 1, fmpz(-1)))
        end
        for i=1:length(g.values)
          g.values[i] *= -1
        end
      end

      if with_trafo
        g, new_trafos  = reduce_right(A, g, 1, trafo)
        append!(trafos, new_trafos)
      else
        g = reduce_right(A, g)
      end

      if A.r == A.c
        @hassert :HNF 1  length(g) == 0 || min(g) >= 0
      end

      with_trafo ? (return g, piv, trafos) : (return g, piv)

    end
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      sca =  -divexact(p, A.rows[j].values[1])
      g = Hecke.add_scaled_row(A[j], g, sca)
      with_trafo ? push!(trafos, TrafoAddScaled(j, rows(A) + 1, sca)) : nothing
      @hassert :HNF 1  length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @hassert :HNF 1  x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      if with_trafo
        push!(trafos, TrafoParaAddScaled(j, rows(A) + 1, a, b, c, d))
      end
      @hassert :HNF 1  A[j].values[1] == x
      @hassert :HNF 1  length(g)==0 || g.pos[1] > A[j].pos[1]
      push!(piv, A[j].pos[1])
      if with_trafo
        A[j], new_trafos = reduce_right(A, A[j], A[j].pos[1]+1, trafo)
        # We are updating the jth row
        # Have to adjust the transformations
        for t in new_trafos
          t.j = j
        end
        # Now append
        append!(trafos, new_trafos)
      else
        A[j] = reduce_right(A, A[j], A[j].pos[1]+1, trafo)
      end

      if A.r == A.c
        @hassert :HNF 1  min(A[j]) >= 0
      end
    end
  end
  if length(g.values) > 0 && g.values[1] < 0
    for i=1:length(g.values)
      g.values[i] *= -1
    end
    with_trafo ? push!(trafos, TrafoScale{fmpz}(rows(A) + 1, fmpz(-1))) : nothing
  end
  if with_trafo
    g, new_trafos = reduce_right(A, g, 1, trafo)
    append!(trafos, new_trafos)
  else
    g = reduce_right(A, g)
  end
  if A.r == A.c
    @hassert :HNF 1  length(g) == 0 || min(g) >= 0
  end
  with_trafo ? (return g, piv, trafos) : (return g, piv)
end

function reduce_right{N}(A::Smat{fmpz}, b::SmatRow{fmpz}, start::Int = 1, trafo::Type{Val{N}} = Val{false})
  with_trafo = (trafo == Val{true})
  with_trafo ? trafos = [] : nothing
  if length(b.pos) == 0
    with_trafo ? (return b, trafos) : return b
  end
  j = 1
  while j <= length(b.pos) && b.pos[j] < start
    j += 1
  end
  if j > length(b.pos)
    with_trafo ? (return b, trafos) : return b
  end
  p = find_row_starting_with(A, b.pos[j])
  if p > rows(A)
    with_trafo ? (return b, trafos) : return b
  end
  @hassert :HNF 1  A[p] != b
  while j <= length(b.pos)
    while p<rows(A) && A[p].pos[1] < b.pos[j]
      p += 1
    end
    if A[p].pos[1] == b.pos[j]
      q, r = divrem(b.values[j], A[p].values[1])
      if r < 0
        q -= 1
        r += A[p].values[1]
        @hassert :HNF 1  r >= 0
      end
      if q != 0
        b = Hecke.add_scaled_row(A[p], b, -q)
        with_trafo ? push!(trafos, TrafoAddScaled(p, rows(A) + 1, -q)) : nothing
        if r == 0
          j -= 1
        else
          @hassert :HNF 1  b.values[j] == r
        end
      end
    end
    j += 1
  end
  with_trafo ? (return b, trafos) : return b
end

doc"""
    hnf_kannan_bachem(A::Smat{fmpz})

> Hermite Normal Form of $A$ using the Kannan-Bachem algorithm to avoid
> intermediate coefficient swell.
"""
function hnf_kannan_bachem{N}(A::Smat{fmpz}, trafo::Type{Val{N}} = Val{false})
  @vprint :HNF 1 "Starting Kannan Bachem HNF on:\n"
  @vprint :HNF 1 A
  @vprint :HNF 1 "with density $(A.nnz/(A.c*A.r))"

  with_trafo = (trafo == Val{true})
  with_trafo ? trafos = [] : nothing

  B = Smat{fmpz}()
  B.c = A.c
  nc = 0
  for i=A
    if with_trafo 
      q, w, new_trafos = reduce_full(B, i, trafo)
      append!(trafos, new_trafos)
    else
      q, w = reduce_full(B, i)
    end

    if length(q) > 0
      p = find_row_starting_with(B, q.pos[1])
      if p > length(B.rows)
        # Appending row q to B
        # Do not need to track a transformation
        push!(B, q)
      else
        # Inserting row q at position p
        insert!(B.rows, p, q)
        B.r += 1
        B.nnz += length(q)
        B.c = max(B.c, q.pos[end])
        # The transformation is swapping pairwise from rows(B) to p.
        # This should be the permutation matrix corresponding to
        # (k k-1)(k-1 k-2) ...(p+1 p) where k = rows(B)
        if with_trafo
          for j in rows(B):-1:(p+1)
            push!(trafos, TrafoSwap{fmpz}(j, j - 1))
          end
        end
      end
      push!(w, q.pos[1])
    else
      # Row i was reduced to zero
      with_trafo ? push!(trafos, TrafoDeleteZero{fmpz}(rows(B) + 1)) : nothing
    end
    if length(w) > 0
      if with_trafo
        new_trafos = reduce_up(B, w, trafo)
        append!(trafos, new_trafos)
      else
        reduce_up(B, w)
      end
    end
    @v_do :HNF 1 begin
      if nc % 10 == 0
        println("Now at $nc rows of $(A.r), HNF so far $(B.r) rows")
        println("Current density: $(B.nnz/(B.c*B.r))")
        println("and size of largest entry: $(nbits(abs_max(B))) bits")
      end
    end
    nc += 1
  end
  with_trafo ? (return B, trafos) : (return B)
end

doc"""
    hnf(A::Smat{fmpz}) -> Smat{fmpz}

> The Hermite Normal Form of $A$, ie. an upper triangular matrix with non-negative
> entries in echelon form that is row-equivalent to $A$.
> Currently, Kannan-Bachem is used.
"""
function hnf{N}(A::Smat{fmpz}, trafo::Type{Val{N}} = Val{true})
  return hnf_kannan_bachem(A, trafo)
end

doc"""
    hnf!(A::Smat{fmpz})

> In-place reduction of $A$ into Hermite Normal Form.
> Currently, Kannan-Bachem is used.
"""
function hnf!(A::Smat{fmpz})
  B = hnf(A)
  A.rows = B.rows
  A.nnz = B.nnz
  A.r = B.r
  A.c = B.c
end

