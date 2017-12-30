function cansolve_ut(A::SMat{T}, g::SRow{T}) where T <: Union{FieldElem, nmod}
  # Works also for non-square matrices
  #@hassert :HNF 1  cols(A) == rows(A)
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

function solve_ut(A::SMat{T}, g::SRow{T}) where T <: Union{FieldElem, nmod}
  fl, sol = cansolve_ut(A, g)
  @assert fl
  return sol
end

#TODO: write vector reconstruction and use it here.
doc"""
    rational_reconstruction(A::SRow{fmpz}, M::fmpz) -> Bool, SRow{fmpz}, fmpz

> Apply rational reconstruction to the entries of $A$. Returns true iff 
> successful. In this case, the numerator is returned as a matrix and the 
> common denominator in the third value.
"""
function rational_reconstruction(A::SRow{fmpz}, M::fmpz)
  B = SRow{fmpz}()
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
   
function solve_ut(A::SMat{fmpz}, b::SRow{fmpz})
  @hassert :HNF 1  isupper_triangular(A)
  #still assuming A to be upper-triag

  sol = SRow{fmpz}()
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

function solve_ut(A::SMat{fmpz}, b::SMat{fmpz})
  @hassert :HNF 1  isupper_triangular(A)
  #still assuming A to be upper-triag
  d = fmpz(1)
  r = SMat(FlintZZ)
  for i = b
    x, dx = solve_ut(A, i)
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

doc"""
    det_mc(A::SMat{fmpz}

> Computes the determinant of $A$ using a LasVegas style algorithm,
> ie. the result is not proven to be correct.
> Uses the dense (nmod_mat) determinant on $A$ for various primes $p$.
"""
function det_mc(A::SMat{fmpz})
  @hassert :HNF 1  A.r == A.c
  if isupper_triangular(A)
    z = [ A[i, i] for i in 1:A.r]
    return prod(z)
  end
  
  q = p
  first = true
  dd = fmpz(1)
  mm = fmpz(1)
  last = fmpz(0)
  while true
    d = det(nmod_mat(SMat(A, q)))
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
    det(A::SMat{fmpz})

> The determinant of $A$ using a modular algorithm.
> Uses the dense (nmod_mat) determinant on $A$ for various primes $p$.
"""
function det(A::SMat{fmpz})
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
  ld = [fmpz(det(matrix(SMat(A, Int(q))))) for q = lp]
  return crt_signed(ld, crt_env(lp))
end

doc"""
    echelon_with_trafo(A::SMat{nmod}) -> SMat, SMat

> Find a unimodular matrix $T$ and an upper-triangular $E$ s.th.
> $TA = E$ holds.
"""
function echelon_with_trafo(A::SMat{nmod})
  z = hcat(A, id(SMat, base_ring(A), A.r))
  M = Hecke.ModuleCtxNmod(base_ring(A), z.c)
  for i=z
    Hecke.add_gen!(M, i)
  end
  return sub(M.basis, 1:A.r, 1:A.c), sub(M.basis, 1:A.r, A.c+1:z.c)
end

doc"""
    solve_dixon_sf(A::SMat{fmpz}, b::SRow{fmpz}, is_int::Bool = false) -> SRow{fmpz}, fmpz
    solve_dixon_sf(A::SMat{fmpz}, B::SMat{fmpz}, is_int::Bool = false) -> SMat{fmpz}, fmpz

> For an upper-triangular sparse matrix $A$ and a sparse matrix (row), find
> a sparse matrix (row) $x$ and an integer $d$ s.th.
> $$x A = bd$$
> holds.
> The algorithm is a Dixon-based linear p-adic lifting method.
> If \code{is_int} is given, then $d$ is assumed to be $1$. In this case
> rational reconstriction is avoided.
"""
function solve_dixon_sf(A::SMat{fmpz}, b::SRow{fmpz}, is_int::Bool = false)
  B = SMat(FlintZZ)
  push!(B, b)
  s, d = solve_dixon_sf(A, B, is_int)
  return s[1], d
end

function solve_dixon_sf(A::SMat{fmpz}, B::SMat{fmpz}, is_int::Bool = false)
  #for square matrices (s) of full rank (f) only.
  p = next_prime(2^20)

  Ap = SMat(A, p)

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

  sol_all = SMat(FlintZZ)
  den_all = fmpz(1)

  for b in B
    pp = fmpz(1)
    b_orig = b

    bp = SRow(b, p)

    sol = SRow{fmpz}()
    last = (sol, 1)

    while true
      bp = mul(bp, Tp)
      zp = solve_ut(Ep, bp)
      z = lift(zp)

      sol += pp*z

      pp *= fmpz(p)

  #    @hassert :HNF 1  iszero(SRow(b_orig - Hecke.mul(sol, A), pp)) 

      if is_int
        fl = true
        nu = copy(sol)
        Hecke.mod_sym!(nu, pp)
        de = fmpz(1)
      else
        fl, nu, de = rational_reconstruction(sol, pp)
      end
      if fl 
  #      @hassert :HNF 1  SRow(de*sol, pp) == SRow(nu, pp)
  #      @hassert :HNF 1  SRow(mul(nu, A), pp) == SRow(de*b_orig, pp)
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

  #    @hassert :HNF 1  SRow(Hecke.mul(z, A), p) == bp
      b = b - Hecke.mul(z, A)

      for i=1:length(b.values)
  #      @hassert :HNF 1  b.values[i] % p == 0
        b.values[i] = div(b.values[i], p)
      end  
      bp = SRow(b, p)
    end
  end
  return sol_all, den_all
end

function echelon!(S::SMat{T}) where T <: FieldElem
  i = 1
  while i <= rows(S)
    m = cols(S)+1
    mp = 0
    for j=i:rows(S)
      if m > S[j].pos[1]
        m = S[j].pos[1]
        mp = j
      end  
    end  
    if mp == 0
      return
    end
    if mp != i
      swap_rows!(S, i, mp)
    end
    Si = -inv(S[i].values[1])
    j = i+1
    while j <= rows(S)
      if S[j].pos[1] == m
        add_scaled_row!(S, i, j, S[j].values[1]*Si)
        if length(S[j].values) == 0
          deleteat!(S.rows, j)
        else
          j += 1
        end  
      else
        j += 1
      end
    end
    i += 1  
  end  
end

function solve(a::SMat{T}, b::SRow{T}) where T <: FieldElem
  fl, sol = cansolve(a, b)
  @assert fl
  return sol
end

function Nemo.cansolve(a::SMat{T}, b::SRow{T}) where T <: FieldElem
  c = hcat(a, id(SMat, base_ring(a), a.r))
  echelon!(c)
  fl, sol = cansolve_ut(sub(c, 1:rows(c), 1:a.c), b)
  if fl
    return fl, mul(sol, sub(c, 1:rows(c), a.c+1:c.c))
  else
    return fl, sol
  end  
end

