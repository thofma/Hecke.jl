function _can_solve_ut(A::SMat{T}, g::SRow{T}) where T <: Union{FieldElem, zzModRingElem}
  # Works also for non-square matrices
  #@hassert :HNF 1  ncols(A) == nrows(A)
  @hassert :HNF 2  is_upper_triangular(A)
  # assumes A is upper triangular, reduces g modulo A to zero and collects
  # the transformation
  # supposed to be over a field...

  sol = sparse_row(base_ring(g))

  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= nrows(A) && A.rows[j].pos[1] < s
      j += 1
    end
    if j > nrows(A) || A.rows[j].pos[1] > s
      break
    end
    @hassert :HNF 2  A.rows[j].pos[1] == g.pos[1]
    p = divexact(g.values[1], A.rows[j].values[1])
    push!(sol.pos, j)
    push!(sol.values, p)
    _g = Hecke.add_scaled_row(A[j], g, -p)
    @assert _g != g
    g = _g
    @hassert :HNF 2  length(g)==0 || g.pos[1] > A[j].pos[1]
  end
  if length(g) == 0
    return true, sol
  else
    return false, sol
  end

  if length(g) > 0
    li = inv(g.values[1])
    for i=1:length(g)
      g.values[i] *= li
    end
  end
  return sol
end

function _solve_ut(A::SMat{T}, g::SRow{T}) where T <: Union{FieldElem, zzModRingElem}
  fl, sol = _can_solve_ut(A, g)
  @assert fl
  return sol
end

#TODO: write vector reconstruction and use it here.
@doc raw"""
    rational_reconstruction(A::SRow{ZZRingElem}, M::ZZRingElem) -> Bool, SRow{ZZRingElem}, ZZRingElem

Apply rational reconstruction to the entries of $A$. Returns true iff
successful. In this case, the numerator is returned as a matrix and the
common denominator in the third value.
"""
function rational_reconstruction(A::SRow{ZZRingElem}, M::ZZRingElem)
  B = sparse_row(FlintZZ)
  de = ZZRingElem(1)
  M2 = div(M, 2)
  nbM = div(nbits(M), 2)
  fl, d,n = true, ZZRingElem(1), ZZRingElem(1)
  for (p,v) = A
    vv = mod_sym(d*v, M)
    if nbits(vv) < nbM
      fl, n = true, vv
    else
      fl, n, d = rational_reconstruction(v, M)
    end
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

function _solve_ut(A::SMat{ZZRingElem}, b::SRow{ZZRingElem})
  @hassert :HNF 1  is_upper_triangular(A)
  #still assuming A to be upper-triag

  sol = sparse_row(FlintZZ)
  den = ZZRingElem(1)
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

function _solve_ut(A::SMat{ZZRingElem}, b::SMat{ZZRingElem})
  @hassert :HNF 1  is_upper_triangular(A)
  #still assuming A to be upper-triag
  d = ZZRingElem(1)
  r = sparse_matrix(FlintZZ)
  for i = b
    x, dx = _solve_ut(A, i)
    nd = lcm(d, dx)
    if nd != d
      dd = div(nd, d)
      for j = 1:r.r
        Hecke.scale_row!(r, j, dd)
      end
      d = nd
    end
    push!(r, div(d, dx)*x)
  end
  return r, d
end

################################################################################
#
#  Determinant
#
################################################################################

@doc raw"""
    det_mc(A::SMat{ZZRingElem})

Computes the determinant of $A$ using a LasVegas style algorithm,
i.e. the result is not proven to be correct.
Uses the dense (zzModMatrix) determinant on $A$ for various primes $p$.
"""
function det_mc(A::SMat{ZZRingElem})

  @hassert :HNF 1  A.r == A.c
  if is_upper_triangular(A)
    z = ZZRingElem[ A[i, i] for i in 1:A.r]
    return prod(z)
  end

  b = sparse_matrix(matrix(FlintZZ, 1, A.c, rand(1:10, A.c)))
  _, qq = solve_dixon_sf(A, b)

  q = p_start # global prime
  first = true
  dd = ZZRingElem(1)
  mm = ZZRingElem(1)
  last = ZZRingElem(0)
  while true
    R = residue_ring(FlintZZ, q, cached = false)[1]
    d = det(matrix(change_base_ring(R, A)))*inv(R(qq))
    if first
      dd = ZZRingElem(d)
      mm = ZZRingElem(q)
      first = false
    else
      dd = crt(dd, mm, ZZRingElem(d), ZZRingElem(q), true)
      mm *= q
    end
    q = next_prime(q)
    if dd == last
      return dd*qq
    else
      last = dd
    end
  end
end

@doc raw"""
    det(A::SMat{ZZRingElem})

The determinant of $A$ using a modular algorithm.
Uses the dense (zzModMatrix) determinant on $A$ for various primes $p$.
"""
function det(A::SMat{ZZRingElem})
  @hassert :HNF 1  A.r == A.c
  if is_upper_triangular(A)
    return prod(ZZRingElem[A[i,i] for i=1:A.r]) end

  b = div(nbits(hadamard_bound2(A)), 2)
  lp = ZZRingElem[p_start]
  while b > 0
    push!(lp, next_prime(lp[end]))
    b -= nbits(lp[end])
  end

  #TODO: re-use the zzModMatrix....
  ld = ZZRingElem[]
  for q in lp
    R = residue_ring(FlintZZ, Int(q), cached = false)[1]
    push!(ld, ZZRingElem(det(matrix(change_base_ring(R, A)))))
  end
  #ld = [ZZRingElem(det(matrix(sparse_matrix(A, Int(q))))) for q = lp]
  return crt_signed(ld, crt_env(lp))
end

@doc raw"""
    echelon_with_transform(A::SMat{zzModRingElem}) -> SMat, SMat

Find a unimodular matrix $T$ and an upper-triangular $E$ s.th.
$TA = E$ holds.
"""
function echelon_with_transform(A::SMat{zzModRingElem})
  z = hcat(A, identity_matrix(SMat, base_ring(A), A.r))
  M = Hecke.ModuleCtxNmod(base_ring(A), z.c)
  for i=z
    Hecke.add_gen!(M, i)
  end
  return sub(M.basis, 1:A.r, 1:A.c), sub(M.basis, 1:A.r, A.c+1:z.c)
end

@doc raw"""
    solve_dixon_sf(A::SMat{ZZRingElem}, b::SRow{ZZRingElem}, is_int::Bool = false) -> SRow{ZZRingElem}, ZZRingElem
    solve_dixon_sf(A::SMat{ZZRingElem}, B::SMat{ZZRingElem}, is_int::Bool = false) -> SMat{ZZRingElem}, ZZRingElem

For a sparse square matrix $A$ of full rank and a sparse matrix (row), find
a sparse matrix (row) $x$ and an integer $d$ s.th.
$$x A = bd$$
holds.
The algorithm is a Dixon-based linear p-adic lifting method.
If \code{is_int} is given, then $d$ is assumed to be $1$. In this case
rational reconstruction is avoided.
"""
function solve_dixon_sf(A::SMat{ZZRingElem}, b::SRow{ZZRingElem}, is_int::Bool = false)
  B = sparse_matrix(FlintZZ)
  push!(B, b)
  s, d = solve_dixon_sf(A, B, is_int)
  return s[1], d
end

function solve_dixon_sf(A::SMat{ZZRingElem}, B::SMat{ZZRingElem}, is_int::Bool = false)
  #for square matrices (s) of full rank (f) only.
  p = next_prime(2^20)
  R = residue_ring(FlintZZ, p, cached = false)[1]

  Ap = change_base_ring(R, A)

  #want AT = upper_triag.
  #Let J = anti-identity, so JA inverts the rows of A and AJ the columns
  #
  # B := (JA)' = A'J and TB = E in upper triag
  # J (TB)' J = JE'J is still upper triag and
  # J (TB)' J = J B' T' J = J (JA) T' J = A (JT)' = JE'J still upp-triag

  Bp = copy(Ap)
  reverse_rows!(Bp)
  Bp = transpose(Bp)
  Ep, Tp = echelon_with_transform(Bp)
  @hassert :HNF 1  Ep.c == Ep.r
#  @hassert :HNF 1  zzModMatrix(Tp) * zzModMatrix(Bp) == zzModMatrix(Ep)

  reverse_rows!(Ep)
  Ep = transpose(Ep)
  reverse_rows!(Ep)
#  @hassert :HNF 1  Hecke.is_upper_triangular(Ep)

  reverse_rows!(Tp)
  Tp = transpose(Tp)
#  @hassert :HNF 1  zzModMatrix(Ap)*zzModMatrix(Tp) == zzModMatrix(Ep)

  #now, to solve xA = b, we do
  #              xAT = bT since AT is upper-triag, we can do this!

  sol_all = sparse_matrix(FlintZZ)
  den_all = ZZRingElem(1)

  for b in B
    pp = ZZRingElem(1)
    b_orig = b

    bp = change_base_ring(R, b)

    sol = sparse_row(FlintZZ)
    last = (sol, ZZRingElem(1))

    while true
      bp = bp * Tp
      zp = _solve_ut(Ep, bp)
      z = lift(zp)

      sol += pp*z

      pp *= ZZRingElem(p)

  #    @hassert :HNF 1  iszero(SRow(b_orig - sol * A, pp))

      if is_int
        fl = true
        nu = copy(sol)
        mod_sym!(nu, pp)
        de = ZZRingElem(1)
      else
        fl, nu, de = rational_reconstruction(sol, pp)
      end
      if fl
  #      @hassert :HNF 1  SRow(de*sol, pp) == SRow(nu, pp)
  #      @hassert :HNF 1  SRow(nu*A, pp) == SRow(de*b_orig, pp)
        if last == (nu, de)
          if nu*A == de*b_orig
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

  #    @hassert :HNF 1  SRow(z*A, p) == bp
      b = b - z*A

      for i=1:length(b.values)
  #      @hassert :HNF 1  b.values[i] % p == 0
        b.values[i] = div(b.values[i], p)
      end
      bp = change_base_ring(R, b)
    end
  end
  return sol_all, den_all
end

function solve(a::SMat{T}, b::SRow{T}) where T <: FieldElem
  fl, sol = can_solve_with_solution(a, b)
  @assert fl
  return sol
end

function can_solve(a::SMat{T}, b::SRow{T}) where T <: FieldElem
  c = sparse_matrix(base_ring(b))
  push!(c, b)

  # b is a row, so this is always from the left
  return can_solve(a, c, side = :left)
end

function can_solve_with_solution(a::SMat{T}, b::SRow{T}) where T <: FieldElem
  c = sparse_matrix(base_ring(b))
  push!(c, b)

  # b is a row, so this is always from the left
  fl, sol = can_solve_with_solution(a, c, side = :left)
  if !fl
    return fl, sparse_row(base_ring(b))
  end
  return fl, sol.rows[1]
end

function solve(a::SMat{T}, b::SMat{T}; side = :left) where T <: FieldElem
  fl, sol = can_solve_with_solution(a, b, side = side)
  @assert fl
  return sol
end

function find_pivot(A::SMat{T}) where T <: RingElement
  p = Int[]
  j = 0
  for i = 1:nrows(A)
    j += 1
    if j > ncols(A)
      return p
    end
    while !insorted(j, A.rows[i].pos)
      j += 1
      if j > ncols(A)
        return p
      end
    end
    push!(p, j)
  end
  return p
end

function can_solve(A::SMat{T}, B::SMat{T}; side::Symbol = :left) where T <: FieldElement
  Solve.check_option(side, [:right, :left], "side")
  K = base_ring(A)
  if side === :right
    # sparse matrices might have omitted zero rows, so checking compatibility of
    # the dimensions does not really make sense (?)
    #nrows(A) != nrows(B) && error("Incompatible matrices")
    mu = hcat(A, B)
    ncolsA = ncols(A)
    ncolsB = ncols(B)
  else # side == :left
    #ncols(A) != ncols(B) && error("Incompatible matrices")
    mu = hcat(transpose(A), transpose(B))
    ncolsA = nrows(A) # They are transposed
    ncolsB = nrows(B)
  end

  rk, mu = rref(mu, truncate = true)
  p = find_pivot(mu)
  return !any(let ncolsA = ncolsA; i -> i > ncolsA; end, p)
end

function can_solve_with_solution(A::SMat{T}, B::SMat{T}; side::Symbol = :left) where T <: FieldElement
  Solve.check_option(side, [:right, :left], "side")
  K = base_ring(A)
  if side === :right
    # sparse matrices might have omitted zero rows, so checking compatibility of
    # the dimensions does not really make sense (?)
    #nrows(A) != nrows(B) && error("Incompatible matrices")
    mu = hcat(A, B)
    ncolsA = ncols(A)
    ncolsB = ncols(B)
  else # side == :left
    #ncols(A) != ncols(B) && error("Incompatible matrices")
    mu = hcat(transpose(A), transpose(B))
    ncolsA = nrows(A) # They are transposed
    ncolsB = nrows(B)
  end

  rk, mu = rref(mu, truncate = true)
  p = find_pivot(mu)
  if any(let ncolsA = ncolsA; i -> i > ncolsA; end, p)
    return (false, sparse_matrix(K))
  end
  sol = zero_matrix(SMat, K, ncolsA, ncolsB)
  for i = 1:length(p)
    for j = 1:ncolsB
      k = searchsortedfirst(mu.rows[i].pos, ncolsA + j)
      if k > length(mu.rows[i].pos)
        break
      end
      if ncolsA + j != mu.rows[i].pos[k]
        continue
      end
      push!(sol.rows[p[i]].pos, j)
      push!(sol.rows[p[i]].values, mu.rows[i].values[k])
      sol.nnz += 1
    end
  end
  if side === :left
    sol = transpose(sol)
  end
  return (true, sol)
end

#TODO: can_solve using Dixon for Q, NF
#      for SMat rather than SRow only
