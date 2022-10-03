
# this code currently only uses one custom type

mutable struct pfracinfo{E}
  xalphas           ::Vector{E}                 # [x_i - alpha_i for i = 1..r]
  betas             ::Vector{Vector{E}}         # matrix of beta evaluations
  inv_prod_betas1   ::Vector{E}                 # info for univariate solver
  prod_betas_coeffs ::Vector{Vector{Vector{E}}} # matrix of taylor coeffs
  deltas            ::Vector{Vector{E}}         # answers
  delta_coeffs      ::Vector{Vector{Vector{E}}} # taylor coeffs of answer
end


########### various helpers for expansions in terms of (x - alpha) ############

# evaluation at x = alpha should use divrem. Don't use evaluate for this!!!

# set t to the coefficients of q when expanded in powers of (x - alpha)
function taylor_get_coeffs!(t::Vector{E}, q::E, xalpha::E) where E
  R = parent(xalpha)
  empty!(t)
  while !iszero(q)
    q, r = divrem(q, xalpha)
    push!(t, r)
  end
end

function taylor_get_coeffs(q::E, xalpha::E) where E
  t = E[]
  taylor_get_coeffs(t, q, xalpha)
  return t
end

# opposite of taylor_get_coeffs
function taylor_from_coeffs(B::Vector{E}, xalpha::E) where E
  R = parent(xalpha)
  a = R(0)
  for i in length(B):-1:1
    a = a*xalpha + B[i]
  end
  return a
end

function taylor_set_coeff!(t::Vector{E}, i::Int, c::E) where E
  R = parent(c)
  while 1 + i > length(t)
    push!(t, R(0))
  end
  t[1 + i] = c
  while length(t) > 0 && iszero(t[end])
    popback!(t)
  end
end

#################### basic manipulation of Fac ################################

# a *= b^e
function mulpow!(a::Fac{T}, b::T, e::Int) where T
  @assert e >= 0
  if e == 0
    return
  end
  if is_constant(b)
    a.unit *= b^e
  elseif haskey(a.fac, b)
    a.fac[b] += e
  else
    a.fac[b] = e
  end
end


function mulpow!(a::Fac{T}, b::Fac{T}, e::Int) where T
  @assert !(a === b)
  @assert e >= 0
  if e == 0
    return
  end
  a.unit *= b.unit^e
  if isempty(a.fac) && e == 1
    a.fac = b.fac
  else
    for i in b.fac
      mulpow!(a, i[1], i[2]*e)
    end
  end
end

################ basic manipulation of polys #################################

function to_univar(a, v, Kx)
  return evaluate(a, [i == v ? gen(Kx) : Kx(0) for i in 1:nvars(parent(a))])
end

function from_univar(a, v, Kxyz)
  return evaluate(a, gen(Kxyz, v))
end

function gcdcofactors(a, b)
  g = gcd(a, b)
  if iszero(g)
    @assert iszero(a)
    @assert iszero(b)
    return (g, a, b)
  elseif isone(g)
    return (g, a, b)
  else
    return (g, divexact(a, g), divexact(b, g))
  end
end

# remove the content with respect to variable v
function primitive_part(a::E, v::Int) where E
  R = parent(a)
  d = degree(a, v)
  g = R(0)
  for i in 0:d
    ci = coeff(a, Int[v], Int[i])
    if !iszero(ci)
      g = gcd(g, ci)::E
    end
  end
  if iszero(g)
    return a
  elseif isone(g)
    return a
  else
    return divexact(a, g)
  end
end

function get_lc(a::E, v::Int) where E
  d = degree(a, v)
  @assert d >= 0
  return coeff(a, Int[v], Int[d])
end

function set_lc(a::E, v::Int, b::E) where E
  R = parent(a)
  d = degree(a, v)
  @assert d >= 0
  diff = (b - coeff(a, Int[v], Int[d]))
  if iszero(diff)
    return a
  else
    return a + diff*gen(R, v)^d
  end
end

function make_monic(a::E) where E
  if length(a) < 1
    return a
  end
  lc = coeff(a, 1)
  if isone(lc)
    return a
  else
    return inv(lc) * a
  end
end

function eval_one(a::E, v, alpha) where E
  R = parent(a)
  return divrem(a, gen(R, v) - alpha)[2]
end


################# generic partial fractions ###################################

#=
  R is a multivariate ring. We will be dealing with polynomials in l + 1
  variables, i.e. only the variables X, x_1, ..., x_l appear,
  where X = gen(R, mainvar) and x_i = gen(R, minorvar[i]).

  For fixed B[1], ..., B[r], precompute info for solving

    t/(B[1]*...*B[r]) = delta[1]/B[1] + ... + delta[r]/B[r] mod (x_i - alpha_i)^(deg_i + 1)

  for delta[1], ..., delta[r] given t in X, x_1, ..., x_l.

  alpha is an array of evaluation points
    x_1 = alpha[1]
    ...
    x_l = alpha[l]

  If, after evaluation at all x_j = alpha[j], the B[i] did not drop degree
  in X and are pairwise relatively prime in K[X], then the function returns
  true and a suitable pfracinfo. Otherwise, it returns false and junk

  Upon success, we are ready to solve for the delta[i] using pfrac.
  The only divisions that pfrac does in K are by the leading coefficients
  of the inv_prod_betas1 member of pfracinfo
=#

function pfracinit(
  B::Vector{E},
  mainvar,
  minorvars::Vector{Int},
  alphas::Vector
) where E

  r = length(B)       # number of factors
  l = length(minorvars)   # number of evaluated variables
  @assert r > 1
  @assert length(alphas) >= l

  R = parent(B[1])
  K = base_ring(R)

  # betas is a 1+l by r matrix with the original B[i] in the last row
  # and successive evaluations in the previous rows
  betas = [E[R(0) for i in 1:r] for j in 0:l]

  # prod_betas is like betas, but has B[1]*...*B[r]/B[i] in the i^th column
  # we don't need prod_betas, but rather
  #   prod_betas_coeffs = taylor of prod_betas in x_(1+j) - alpha[j]
  prod_betas_coeffs = [[E[] for i in 1:r] for j in 0:l]

  # inv_prod_betas1[i] will hold invmod(B[1]*...*B[r]/B[i], B[i]) in R[X]
  # after all x_j = alpha[j] have been evaluated away
  inv_prod_betas1 = E[R(0) for i in 1:r]

  # working space that need not be reallocated on each recursive call
  deltas = [E[R(0) for i in 1:r] for j in 0:l]
  delta_coeffs = [[E[] for i in 1:r] for j in 0:l]

  xalphas = E[gen(R, minorvars[j]) - R(alphas[j]) for j in 1:l]

  I = pfracinfo{E}(xalphas, betas, inv_prod_betas1, prod_betas_coeffs,
                                                          deltas, delta_coeffs)
  for i in 1:r
    I.betas[1+l][i] = deepcopy(B[i])
  end
  for j in l:-1:1
    for i in 1:r
      _, I.betas[j][i] = divrem(I.betas[j + 1][i], xalphas[j])
    end
  end

  for i in 1:r
    if degree(I.betas[1][i], mainvar) != degree(I.betas[l + 1][i], mainvar)
      # degree drop in univariates in X
      return false, I
    end
  end

  # univariate ring for gcdx
  S, x = PolynomialRing(K, "x")
  sub = [k == mainvar ? x : S(1) for k in 1:nvars(R)]

  for j in 0:l
    for i in 1:r
      p = R(1)
      for k in 1:r
        if k != i
          p *= I.betas[1 + j][k]
        end
      end
      if j > 0
        taylor_get_coeffs!(I.prod_betas_coeffs[1 + j][i], p, I.xalphas[j])
      else
        s = evaluate(betas[1][i], sub)
        t = evaluate(p, sub)
        g, s1, t1 = gcdx(s, t)
        if !is_constant(g)
          # univariates are not pairwise prime
          return false, I
        end
        I.inv_prod_betas1[i] = evaluate(divexact(t1, g), gen(R, mainvar))
        # leave prod_betas_coeffs[1][i] as zero, it doesn't matter
      end
    end
  end

  return true, I
end

#=
  Try to solve

    t/(B[1]*...*B[r]) = delta[1]/B[1] + ... + delta[r]/B[r] mod I

  where I = <(x_i - alpha_i)^(degs[i] + 1)>, and
      the x_i and alpha_i are those parameters of pfracinit, and
      the degs[i] are parameters of this function.

  With check = false, a solution to the above problem is generated without fail.
  With check = true, the solutions delta[j] are limited by

    deg_{x_i} delta[j] <= degs[i] - deg_{x_i}(B[1]*...*B[r]/B[j])

  The second return of pfrac (the array delta) is owned by I.
  So, at least its length should not be mutated.
=#
function pfrac(I::pfracinfo{E}, t::E, degs::Vector{Int}, check::Bool) where E
  return pfrac_recursive(I, t, degs, length(I.xalphas), check)
end

function pfrac_recursive(
  I::pfracinfo{E},
  t::E,
  degs::Vector{Int},
  lev::Int,
  check::Bool
) where E

  @assert 0 <= lev <= length(I.xalphas)
  @assert lev <= length(degs)

  r = length(I.inv_prod_betas1)

  deltas = I.deltas[1 + lev]

  if lev == 0
    for i in 1:r
      Q, deltas[i] = divrem(t*I.inv_prod_betas1[i], I.betas[1][i])
      # TODO check the denominator of deltas[i] and possibly return false
    end
    return true, deltas
  end

  newdeltas = I.deltas[lev]
  delta_coeffs = I.delta_coeffs[1 + lev]
  pbetas = I.prod_betas_coeffs[1 + lev]

  for i in 1:r
    empty!(delta_coeffs[i])
  end

  for l in 0:degs[lev]
    t, newt = divrem(t, I.xalphas[lev])
    for i in 1:r
      for s in 0:l-1
        if s < length(delta_coeffs[i]) && l - s < length(pbetas[i])
          newt -= delta_coeffs[i][1 + s] * pbetas[i][1 + l - s]
        end
      end
    end

    if iszero(newt)
      continue
    end

    ok, newdeltas = pfrac_recursive(I, newt, degs, lev - 1, check)
    if !ok
      return false, deltas
    end

    for i in 1:r
      if iszero(newdeltas[i])
        continue
      end
      if check && l + length(pbetas[i]) - 1 > degs[lev]
        return false, deltas
      end
      taylor_set_coeff!(delta_coeffs[i], l, newdeltas[i])
    end
  end

  for i in 1:r
    deltas[i] = taylor_from_coeffs(delta_coeffs[i], I.xalphas[lev])
  end

  return true, deltas
end

################# generic hensel lifting ######################################

#=
  Try to lift a factorization of A in 1 variable to 1 + n variables without
  any leading coefficient information.
=#
function hlift_without_lcc(
  A::E,
  Auf::Vector{E},       # univariate factorization in mainvar
  mainvar::Int,
  minorvars::Vector{Int},   # length n
  alphas::Vector
) where E

  R = parent(A)
  n = length(minorvars)
  r = length(Auf)
  @assert n > 0
  @assert r > 0

  if r < 2
    return true, [primitive_part(A, mainvar)]
  end

  lcA = get_lc(A, mainvar)
  A *= lcA^(r-1)

  degs = [degree(A, i) for i in minorvars]

  evals = E[R(0) for i in 1:n+1]
  lcevals = E[R(0) for i in 1:n+1]

  evals[n + 1] = A
  lcevals[n + 1] = lcA
  for i in n:-1:1
    evals[i] = eval_one(evals[i + 1], minorvars[i], alphas[i])
    lcevals[i] = eval_one(lcevals[i + 1], minorvars[i], alphas[i])
  end

  fac = [divexact(lcevals[1], get_lc(Auf[i], mainvar))*Auf[i] for i in 1:r]

  for k in 1:n
    ok, fac = hliftstep(fac, mainvar, minorvars[1:k], degs, alphas, evals[k+1], true)
    if !ok
      return false, fac
    end
  end

  return true, [make_monic(primitive_part(fac[i], mainvar)) for i in 1:r]
end

#=
  Try to lift a factorization of A in 1 variable to 1 + n variables with the
  assumption that divs[i] is a divisor of the leading coefficient of
  the i^th liftedfactor.
=#
function hlift_with_lcc(
  A::E,
  Auf::Vector{E},       # univariate factorization in mainvar
  divs::Vector{E},      # lead coeff divisors
  mainvar::Int,
  minorvars::Vector{Int},   # length n
  alphas::Vector,
) where E

  R = parent(A)
  K = base_ring(R)
  n = length(minorvars)
  r = length(Auf)
  @assert n > 0
  @assert r > 1

  fac = copy(Auf)

  m = get_lc(A, mainvar)
  for i in divs
    ok, m = divides(m, i)
    if !ok
      # lcc was definitely wrong
      return false, fac
    end
  end

  lcs = zeros(R, n + 1, r)
  for j in 1:r
    lcs[n + 1, j] = divs[j]*m
    for i in n:-1:1
      lcs[i, j] = eval_one(lcs[i + 1, j], minorvars[i], alphas[i])
    end
  end

  evals = zeros(R, n + 1)
  evals[n + 1] = A*m^(r - 1)
  for i in n:-1:1
    evals[i] = eval_one(evals[i + 1], minorvars[i], alphas[i])
  end

  tdegs = degrees(evals[n + 1])
  liftdegs = [tdegs[minorvars[i]] for i in 1:n]

  for j in 1:r
    @assert is_constant(lcs[1, j])
    fac[j] *= divexact(lcs[1, j], get_lc(fac[j], mainvar))
  end

  for i in 2:n+1
    tfac = [set_lc(fac[j], mainvar, lcs[i, j]) for j in 1:r]
    ok, fac = hliftstep(tfac, mainvar, minorvars[1:i-1], liftdegs, alphas, evals[i], true)
    if !ok
      return false, fac
    end
  end

  if !is_constant(m)
    fac = [primitive_part(i, mainvar) for i in fac]
  end

  return true, fac
end

function hliftstep(
  fac::Vector{E},
  mainvar::Int,
  minorvars::Vector{Int},
  liftdegs::Vector{Int},
  alphas::Vector,
  a::E,
  check::Bool
) where E

  r = length(fac)
  @assert r >= 2

  if r == 2
    return hliftstep_quartic2(fac, mainvar, minorvars, liftdegs, alphas, a, check)
  elseif r < 30
    return hliftstep_quartic(fac, mainvar, minorvars, liftdegs, alphas, a, check)
  else
    return hliftstep_quintic(fac, mainvar, minorvars, liftdegs, alphas, a, check)
  end
end


function hliftstep_quartic2(
  fac::Vector{E},
  mainvar::Int,
  minorvars::Vector{Int},
  liftdegs::Vector{Int},
  alphas::Vector,
  a::E,
  check::Bool
) where E

  R = parent(a)
  m = length(minorvars)

  @assert m > 0
  @assert length(liftdegs) >= m
  @assert length(alphas) >= m
  @assert length(fac) == 2

  xalpha = gen(R, minorvars[m]) - alphas[m]

  newfac = E[R(0), R(0)]

  Blen = Int[0, 0]
  B = [E[], E[]]
  for i in 1:2
    taylor_get_coeffs!(B[i], fac[i], xalpha)
    Blen[i] = length(B[i])
    # push extra stuff to avoid annoying length checks
    while length(B[i]) < liftdegs[m] + 1
      push!(B[i], R(0))
    end
  end

  ok, I = pfracinit([B[1][1], B[2][1]], mainvar, minorvars[1:m-1], alphas)
  @assert ok

  a, t = divrem(a, xalpha)
  @assert t == B[1][1] * B[2][1]

  M = zeros(R, liftdegs[m] + 1)

  for j in 1:liftdegs[m]
    a, t = divrem(a, xalpha)
    for i in 0:j
      p1 = B[1][1 + i] * B[2][1 + j - i]
      if !iszero(p1)
        t -= p1
      end
    end

    if iszero(t)
      continue
    end

    ok, deltas = pfrac(I, t, liftdegs, check)
    if !ok
      return false, newfac
    end

    tdeg = 0
    for i in 1:2
      B[i][1 + j] += deltas[i]
      if !iszero(B[i][j + 1])
        Blen[i] = max(Blen[i], j + 1)
      end
      tdeg += Blen[i] - 1
    end

    if check && tdeg > liftdegs[m]
##      println("high degree: ", tdeg, " > ", liftdegs[m])
      return false, newfac
    end

    M[1 + j] = B[1][1 + j]*B[2][1 + j]
  end

  for i in 1:2
    while length(B[i]) > Blen[i]
      @assert iszero(B[i][end])
      pop!(B[i])
    end
    newfac[i] = taylor_from_coeffs(B[i], xalpha)
  end

  return true, newfac
end


function hliftstep_quartic(
  fac::Vector{E},
  mainvar::Int,
  minorvars::Vector{Int},
  liftdegs::Vector{Int},
  alphas::Vector,
  a::E,
  check::Bool
) where E

  R = parent(a)
  r = length(fac)
  m = length(minorvars)

  @assert m > 0
  @assert length(liftdegs) >= m
  @assert length(alphas) >= m
  @assert r > 2

  xalpha = gen(R, minorvars[m]) - alphas[m]

  newfac = E[R(0) for i in 1:r]

  Blen = zeros(Int, r)
  B = [E[] for i in 1:r]
  U = [E[R(0) for j in 1:liftdegs[m] + 1] for i in 1:r]
  for i in 1:r
    taylor_get_coeffs!(B[i], fac[i], xalpha)
    Blen[i] = length(B[i])
    # push extra stuff to avoid anoying length checks
    while length(B[i]) < liftdegs[m] + 1
      push!(B[i], R(0))
    end
  end

  ok, I = pfracinit([B[i][1] for i in 1:r], mainvar, minorvars[1:m-1], alphas)
  @assert ok

  # lets pretend julia is 0-based for this awful mess

  k = r - 2
  U[1+k][1+0] = B[1+k][1+0] * B[1+k+1][1+0]
  k -= 1
  while k >= 1
    U[1+k][1+0] = B[1+k][1+0] * U[1+k+1][1+0]
    k -= 1
  end

  a, t = divrem(a, xalpha)
  @assert t == prod(B[i][1] for i in 1:r)

  for j in 1:liftdegs[m]
    k = r - 2

    U[1+k][1+j] = R(0)
    for i in 0:j
      U[1+k][1+j] += B[1+k][1+i] * B[1+k+1][1+j-i]
    end
    k -= 1
    while k >= 1
      U[1+k][1+j] = R(0)
      for i in 0:j
        U[1+k][1+j] += B[1+k][1+i] * U[1+k+1][1+j-i]
      end
      k -= 1
    end

    a, t = divrem(a, xalpha)
    for i in 0:j
      t -= B[1+0][1+i]*U[1+1][1+j-i]
    end

    if iszero(t)
      continue
    end

    ok, deltas = pfrac(I, t, liftdegs, check)
    if !ok
      return false, newfac
    end

    tdeg = 0
    for i in 1:r
      B[i][1+j] += deltas[i]
      if !iszero(B[i][1+j])
        Blen[i] = max(Blen[i], j + 1)
      end
      tdeg += Blen[i] - 1
    end

    if check && tdeg > liftdegs[m]
      return false, fac
    end

    k = r - 2
    t = B[1+k][1+0]*deltas[1+k+1] + deltas[1+k]*B[1+k+1][1+0]
    U[1+k][1+j] += t
    k -= 1
    while k >= 1
      t = B[1+k][1+0]*t + deltas[1+k]*U[1+k+1][1+0]
      U[1+k][1+j] += t
      k -= 1
    end
  end

  for i in 1:r
    while length(B[i]) > Blen[i]
      @assert iszero(B[i][end])
      pop!(B[i])
    end
    newfac[i] = taylor_from_coeffs(B[i], xalpha)
  end

  return true, newfac
end


function hliftstep_quintic(
  fac::Vector{E},
  mainvar::Int,
  minorvars::Vector{Int},
  liftdegs::Vector{Int},
  alphas::Vector,
  a::E,
  check::Bool
) where E

  R = parent(a)
  r = length(fac)
  m = length(minorvars)

  @assert m > 0
  @assert length(liftdegs) >= m
  @assert length(alphas) >= m
  @assert r > 2

  xalpha = gen(R, minorvars[m]) - alphas[m]

  betas = [eval_one(f, minorvars[m], alphas[m]) for f in fac]
  ok, I = pfracinit(betas, mainvar, minorvars[1:m-1], alphas)
  @assert ok

  newfac = [f for f in fac]
  err = a - prod(f for f in newfac)

  for j in 1:liftdegs[m]
    if iszero(err)
      return true, newfac
    end
    _, t = divrem(divexact(err, xalpha^j), xalpha)
    ok, deltas = pfrac(I, t, liftdegs, check)
    if !ok
      return false, newfac
    end
    for i in 1:r
      newfac[i] += deltas[i]*xalpha^j
    end
    err = a - prod(f for f in newfac)
  end

  return (!check || iszero(err)), newfac
end


###################### generic factoring ######################################

#=
  Factor a into irreducibles assuming a depends only on variable var
  Return (true, monic factors of a) if a is squarefree
         (false, junk)              if a is not squarefree
=#
function mfactor_irred_univar(a::E, var::Int) where E
  R = parent(a)
  K = base_ring(R)
  Kx, _ = PolynomialRing(K, "x")
  F = Hecke.factor(to_univar(a, var, Kx))
  res = E[]
  ok = true
  for f in F.fac
    ok = ok && (f[2] == 1)
    push!(res, make_monic(from_univar(f[1], var, R)))
  end
  return ok, res
end

#=
  Factor a into irreducibles assuming
    a depends only on variables xvar and yvar, and
    a is squarefree and primitive wrt xvar
  Return monic squarefree factors of a
=#
function mfactor_irred_bivar_char_zero(a::E, xvar::Int, yvar::Int) where E

  xdeg = degree(a, xvar)

  alpha = 0
  @goto got_alpha

@label next_alpha

  if alpha > 0
    alpha = -alpha
  else
    alpha = 1 - alpha
  end

@label got_alpha

  u = eval_one(a, yvar, alpha)
  if degree(u, xvar) != xdeg
    @goto next_alpha
  end

  sqrfree, ufac = mfactor_irred_univar(u, xvar)
  if !sqrfree
    @goto next_alpha
  end

  ok, cont, res = hlift_bivar_combine(a, xvar, yvar, alpha, ufac)
  if !ok
    @goto next_alpha
  end

  @assert is_constant(cont)

  return map(make_monic, res)
end

#=
  return (true, cont(a, x), array of factors) or
         (false, junk, junk) if the ufacs don't lift straight to bivariate ones

  TODO: allow this function to do a bit of zassenhaus and add a parameter to
        limit the size of the subsets.
=#
function hlift_bivar_combine(
  a::E,
  xvar::Int,
  yvar::Int,
  alpha,
  ufacs::Vector{E}  # factorization of a(x, y = alpha)
) where E

  R = parent(a)
  K = base_ring(R)
  r = length(ufacs)
  tfac = E[R(0) for i in 1:r]

  if r < 2
    tfac[1] = primitive_part(a, xvar)
    return true, divexact(a, tfac[1]), tfac
  end

  xdeg = degree(a, xvar)
  ydeg = degree(a, yvar)

  Ky, y = PolynomialRing(K, "x")

  yalpha = gen(R, yvar) - R(alpha)
  yalphapow = yalpha^(ydeg + 1)

  lc = coeff(a, Int[xvar], Int[xdeg])
  lc = evaluate(lc, [k == yvar ? y : Ky(0) for k in 1:nvars(R)])
  g, s, lcinv = gcdx((y - alpha)^(ydeg + 1), lc)
  @assert isone(g)
  lcinv = evaluate(lcinv, gen(R, yvar))

  monica = divrem(lcinv*a, yalphapow)[2]
  @assert isone(coeff(monica, Int[xvar], Int[xdeg]))

  ok, bfacs = hliftstep(ufacs, xvar, [yvar], [ydeg], [alpha], monica, false)
  if !ok
    return false, a, tfac
  end
  for i in 1:r
    @assert degree(a, xvar) >= 0
    tfac[i] = coeff(a, Int[xvar], Int[degree(a, xvar)]) * bfacs[i]
    tfac[i] = primitive_part(divrem(tfac[i], yalphapow)[2], xvar)
    a, r = divrem(a, tfac[i])
    if !iszero(r)
      return false, a, tfac
    end
  end

  return true, a, tfac
end

#=
  a and b are both factorizations. Make the bases coprime without changing
  the values of factorizations. TODO this is probably done somewhere else.
=#
function make_bases_coprime!(a::Array{Pair{E, Int}}, b::Array{Pair{E, Int}}) where E
  lena = length(a)
  lenb = length(b)
  for i in 1:lena
    for j in 1:lenb
      ai = a[i].first
      bj = b[j].first
      (g, ai, bi) = gcdcofactors(ai, bj)
      if !is_constant(g)
        a[i] = ai => a[i].second
        b[i] = bi => b[i].second
        push!(a, g => a[i].second)
        push!(b, g => b[i].second)
      end
    end
  end
  filter!(t->!is_constant(t.first), a)
  filter!(t->!is_constant(t.first), b)
end

# Return A/b^bexp
function divexact_pow(A::Fac{E}, b::E, bexp::Int) where E

  R = parent(A.unit)
  a = collect(A.fac)
  abases = E[t.first for t in a]
  aexps = Int[t.second for t in a]

  i = 1 # index strickly before which everthing is coprime to b

  while i <= length(abases) && !is_constant(b)
    abase_new, abases[i], b = gcdcofactors(abases[i], b)
    if is_constant(abase_new)
      i += 1
      continue
    end
    aexp_new = aexps[i] - bexp
    if aexp_new < 0
      error("non-exact division in divexact_pow")
    elseif aexp_new > 0
      push!(abases, abase_new)
      push!(aexps, aexp_new)
    end
    if is_constant(abases[i])
      deleteat!(abases, i)
      deleteat!(aexps, i)
    else
      i += 1
    end
  end

  if !is_constant(b)
    error("non-exact division in divexact_pow")
  end

  #return Fac{E}(R(1), Dict(abases .=> aexps))
  f = Fac{E}()
  f.unit = R(1)
  f.fac = Dict(abases .=> aexps)
  return f
end


function lcc_kaltofen_step!(
  divs::Vector{E},  # modifed
  Af::Fac{E},       # unmodified, possibly new one is returned
  Au::Vector{E},    # univariates in gen(v) from the lc's of bvar factors
  v::Int,           # the main variable for this step
  minorvars::Vector{Int},
  alphas::Vector
) where E

  R = parent(Af.unit)
  r = length(Au)
  @assert r == length(divs)
  Kx, _ = PolynomialRing(base_ring(R), string(gen(R,v)))

  Auf = [collect(Hecke.factor_squarefree(to_univar(Au[i], v, Kx)).fac) for i in 1:r]

  Afdegv = 0
  Afp = R(1)
  for i in Af.fac
    thisdeg = degree(i.first, v)
    Afdegv += thisdeg
    if thisdeg != 0
      Afp *= i.first
    end
  end

  t = Afp
  for i in 1:length(minorvars)
    t = eval_one(t, minorvars[i], alphas[i])
  end
  t = to_univar(make_monic(t), v, Kx)

  if degree(t) != Afdegv || Afdegv < 1
    return false, Af
  end

  for i in 1:r-1
    for j in i+1:r
      make_bases_coprime!(Auf[i], Auf[j])
    end
  end

  f = Set{elem_type(Kx)}()
  for i in Auf
    for j in i
      push!(f, make_monic(j.first))
    end
  end
  f = collect(f)

  if t != prod(i for i in f)
    return false, Af
  end

  liftarg = [from_univar(i, v, R) for i in f]
  ok, lifts = hlift_without_lcc(Afp, liftarg, v, minorvars, alphas)
  if !ok
    return false, Af
  end

  for i in 1:r
    for j in Auf[i]
      for k in 1:length(f)
        if f[k] == j.first
          Af = divexact_pow(Af, lifts[k], j.second)
          divs[i] *= lifts[k]^j.second
        end
      end
    end
  end
  return true, Af
end


#=
  Try to determine divisors of the leading coefficients of the factors of A.
  This is accomplished by looking at the bivariate factoration of A when
  all but one of the minor variables are evaluated away. The resulting
  univariate leading coefficients are lifted against the supplied
  leading_coefficient(A) factorization. return is Tuple{::Boole, ::Vector{E}}
  If the bool is true, then the method can be considered to have fully found
  the leading coefficients, otherwise not. In any case, the second return
  is a tentative guess at the leading coefficients.
=#
function lcc_kaltofen(
  lcAf::Fac{E},       # square free factorization of lc(A), not modified
  A::E,
  mainvar::Int,
  maindeg::Int,
  minorvars::Vector{Int},
  alphas::Vector,
  ufacs::Vector{E}    # univariate factors of (A evaluated at minor vars)
) where E

  R = parent(A)
  r = length(ufacs)

  @assert r > 1

  divs = E[R(1) for i in 1:r]
  ulcs = E[R() for i in 1:r]

  for vi in 1:length(minorvars)
    if isempty(lcAf.fac)
      break
    end

    other_minorvars = deleteat!(copy(minorvars), vi)
    other_alphas = deleteat!(copy(alphas), vi)

    beval = A
    for i in 1:length(other_minorvars)
      beval = eval_one(beval, other_minorvars[i], other_alphas[i])
    end
    @assert degree(beval, mainvar) == maindeg

    ok, cont, bfac = hlift_bivar_combine(beval, mainvar, minorvars[vi],
                                                             alphas[vi], ufacs)
    if !ok
      return false, divs
    end
    if !is_constant(cont)
      continue
    end

    divides_ok = true
    for k in 1:r
      ueval = divs[k]
      for i in 1:length(other_minorvars)
        ueval = eval_one(ueval, other_minorvars[i], other_alphas[i])
      end
      ok, ulcs[k] = divides(get_lc(bfac[k], mainvar), ueval)
      divides_ok = divides_ok && ok
    end
    if !divides_ok
      continue
    end
    ok, lcAf = lcc_kaltofen_step!(divs, lcAf, ulcs, minorvars[vi],
                                                 other_minorvars, other_alphas)
  end

  return isempty(lcAf.fac), divs

end

# factor a truely multivariate A in at least three variables
function mfactor_irred_mvar_char_zero(
  A::E,             # squarefree, primitve wrt mainvar, monic
  mainvar::Int,
  minorvars::Vector{Int}
) where E

  n = length(minorvars)
  R = parent(A)
  K = base_ring(R)
  @assert length(A) > 0

  evals = zeros(R, n + 1)
  alphas = zeros(K, n)
  alpha_modulus = 0
  lcc_fails_remaining = 3

  maindeg = degree(A, mainvar)

@label next_alpha

  alpha_modulus += 1
  for i in 1:n
    alphas[i] = K(rand(Int) % alpha_modulus)
  end

  evals[n + 1] = A
  for i in n:-1:1
    evals[i] = eval_one(evals[i + 1], minorvars[i], alphas[i])
    if degree(evals[i], mainvar) != maindeg
      @goto next_alpha
    end
  end

  # make sure univar is squarefree. TODO also zassenhaus pruning here
  ok, fac = mfactor_irred_univar(evals[1], mainvar)
  if !ok
    @goto next_alpha
  end

  r = length(fac)
  if r < 2
    return [A]
  end

  lcAf = mfactor_squarefree_char_zero(get_lc(A, mainvar))

  ok, divs = lcc_kaltofen(lcAf, A, mainvar, maindeg, minorvars, alphas, fac)
  if !ok
    lcc_fails_remaining -= 1
    if lcc_fails_remaining >= 0
      @goto next_alpha
    end
  end

  ok, fac = hlift_with_lcc(A, fac, divs, mainvar, minorvars, alphas)
  if !ok
    @goto next_alpha
  end

  return map(make_monic, fac)
end

########## factorization in three steps #######################################

# take out the content and lowest power wrt variable v
function mfactor_primitive(f::E, v::Int) where E
  R = parent(f)
  d = degree(f, v)
  g = R(0)
  smallest = d
  for i in 0:d
    ci = coeff(f, Int[v], Int[i])
    if !iszero(ci)
      g = gcd(g, ci)::E
      smallest = min(smallest, i)
    end
  end
  @assert !iszero(g)
  return (g, divexact(f, g*gen(R, v)^smallest)::E, smallest)
end

# assume a is primitive wrt each variable appearing in it
# return squarefree factors
function mfactor_sqrfree_char_zero(a::E) where E
  R = parent(a)
  @assert length(a) >= 1
  res = Fac{E}()
  res.unit = R(1)
  for v in 1:nvars(R)
    Sp = derivative(a, v)
    if !iszero(Sp)
      (Sm, Ss, Y) = gcdcofactors(a, Sp)
      k = 1
      while begin Z = Y - derivative(Ss, v); !iszero(Z) end
        (S, Ss, Y) = gcdcofactors(Ss, Z)
        mulpow!(res, S, k)
        k += 1
      end
      mulpow!(res, Ss, k)
      return res
    end
  end
  @assert is_constant(a)
  mulpow!(res, a, 1)
  return res
end

# assume a is primitive wrt each variable appearing in it and squarefree
# return irreducible factors
function mfactor_irred_char_zero(a::E) where E
  R = parent(a)
  K = base_ring(R)
  @assert length(a) > 0

  res = Fac{E}()
  res.unit = R(1)

  lc = coeff(a, 1)
  if !isone(lc)
    res.unit = lc
    a *= inv(lc)
  end

  degs = degrees(a)
  vars = Int[]    # variables that actually appear
  for v in 1:nvars(R)
    if degs[v] > 0
      push!(vars, v)
    end
  end

  if isempty(vars)
    @assert isone(a)
    return res
  end

  sort!(vars, by = (v -> degs[v]), alg=InsertionSort)

  if degs[1] == 1
    # linear is irreducible by assumption
    mulpow!(res, a, 1)
    return res
  end

  local f::Vector{E}

  if length(vars) == 1
    sqrfree, f = mfactor_irred_univar(a, vars[1])
    @assert sqrfree
  elseif length(vars) == 2
    f = mfactor_irred_bivar_char_zero(a, vars[1], vars[2])
  else
    f = mfactor_irred_mvar_char_zero(a, vars[1], vars[2:end])
  end

  for i in f
    mulpow!(res, i, 1)
  end
  return res
end


function mfactor_squarefree_char_zero(a::E) where E
  R = parent(a)
  K = base_ring(R)

  res = Fac{E}()
  tres = Fac{E}()

  if iszero(a)
    res.unit = R(0)   # not a unit :-(
    return res
  end

  # start with a monic version of a
  lc = coeff(a, 1)
  res.unit = R(lc)
  res.fac = Dict{E, Int}(1//lc * a => 1)

  # pure variable powers in the final factorization
  var_powers = zeros(Int, nvars(R))

  # ensure factors are primitive wrt any variable
  for v in 1:nvars(R)
    tres.unit = res.unit
    empty!(tres.fac)
    for p in res.fac
      (content, primitive, power) = mfactor_primitive(p[1], v)
      var_powers[v] += power
      mulpow!(tres, content, 1)
      mulpow!(tres, primitive, 1)
    end
    res, tres = tres, res
  end

  # ensure factors are squarefree
  tres.unit = res.unit
  empty!(tres.fac)
  for i in res.fac
    mulpow!(tres, mfactor_sqrfree_char_zero(i[1]), i[2])
  end
  res, tres = tres, res

  # put pure variable powers back in
  for v in 1:nvars(R)
    mulpow!(res, gen(R, v), var_powers[v])
  end

  return res
end

# factor a multivariate over an exact field of characteristic 0
function mfactor_char_zero(a::E) where E
  tres = mfactor_squarefree_char_zero(a)
  # ensure factors are irreducible
  res = Fac{E}()
  res.unit = tres.unit
  empty!(res.fac)
  for i in tres.fac
    mulpow!(res, mfactor_irred_char_zero(i[1]), i[2])
  end
  return res
end

function factor(a::MPolyElem)
  R = parent(a)
  K = base_ring(R)
  if elem_type(K) <: AbstractAlgebra.FieldElem && iszero(characteristic(K))
    return mfactor_char_zero(a)
  else
    error("factor not implemented for the ring $R")
  end
end

function factor_squarefree(a::MPolyElem)
  R = parent(a)
  K = base_ring(R)
  if elem_type(K) <: AbstractAlgebra.FieldElem && iszero(characteristic(K))
    return mfactor_squarefree_char_zero(a)
  else
    error("factor_squarefree not implemented for the ring $R")
  end
end

