module MpolyFact

using Hecke
import Hecke: Nemo

function Hecke.lead(f::fmpq_mpoly)
  return first(coeffs(f))
end

function Hecke.ismonic(f::fmpq_mpoly)
  return isone(lead(f))
end

function factor_bi(f::fmpq_mpoly, k::Int)
  P = parent(f)
  @assert nvars(P) == 2
  @assert ismonic(f)

  Qt, t = PolynomialRing(base_ring(f), :t, cached = false)
  s = -1
  local ff
  while true
    s += 1
    ff = evaluate(f, [t, Qt(s)])
    if issquarefree(ff)
      break
    end
  end

  lfp = collect(keys(factor(ff).fac))
  lf = map(x -> x(gens(P)[1]), lfp)
  la = elem_type(P)[]
  i = 1
  n = length(lf)
  while i < length(lfp)
    f1 = lfp[i]
    f2 = lfp[i+1]
    g, a, b = gcdx(f1, f2)
    @assert isone(g)
    push!(la, a(gens(P)[1]))
    push!(la, b(gens(P)[1]))
    push!(lfp, f1*f2)
    push!(lf, lfp[end](gens(P)[1]))
    i += 2
  end
  lf[end] = f

  N = 1
  mx = k
  ch = [mx]
  while ch[end] > N
    push!(ch, div(ch[end]+1, 2))
  end

  p = gens(P)[2] - s
  for k=length(ch)-1:-1:1
    p2 = (gens(P)[2]-s)^ch[k]
    i = length(lf)
    j = i-1
    while j > 0
      h = lf[j]
      g = lf[j-1]
      b = la[j]
      a = la[j-1]
      f = lf[i]

      fgh = divexact(f-g*h, p)
      G = divrem(fgh*b, g)[2]*p+g
      H = divrem(fgh*a, h)[2]*p+h
      t = divexact(1-a*G-b*H, p)
      B = divrem(t*b, g)[2]*p+b
      A = divrem(t*a, h)[2]*p+a
      if i < length(lf)
        lf[i] = G*H
      end
      _, lf[j-1] = divrem(G, p2)
      _, lf[j] = divrem(H, p2)
      _, la[j-1] = divrem(A, p2)
      _, la[j] = divrem(B, p2)
      i -= 1
      j -= 2
    end
    p = p2
  end
  return lf[1:n], s
end

function factor_bi2(f::MPolyElem, k::Int)
  P = parent(f)
  @assert nvars(P) == 2

  Qt, t = PolynomialRing(base_ring(f), :t, cached = false)
  Qts, s = PolynomialRing(Qt, :s, cached = false)
  f = evaluate(f, [s, t])
  @assert ismonic(f)

  s = -1
  local ff
  while true
    s += 1
    ff = Qt([x(s) for x = coefficients(f)])
    if issquarefree(ff)
      break
    end
  end

  lfp = collect(keys(factor(ff).fac))
  lf = map(x -> x(gen(Qts)), lfp)
  la = typeof(f)[]
  i = 1
  n = length(lf)
  while i < length(lfp)
    f1 = lfp[i]
    f2 = lfp[i+1]
    g, a, b = gcdx(f1, f2)
    @assert isone(g)
    push!(la, a(gen(Qts)))
    push!(la, b(gen(Qts)))
    push!(lfp, f1*f2)
    push!(lf, lfp[end](gen(Qts)))
    i += 2
  end
  lf[end] = f

  N = 1
  mx = k
  ch = [mx]
  while ch[end] > N
    push!(ch, div(ch[end]+1, 2))
  end

  function _mod(a, b)
    c = parent(a)()
    for i=0:degree(a)
      setcoeff!(c, i, rem(coeff(a, i), b))
    end
    return c
  end
  function _div(a, b)
    c = parent(a)()
    for i=0:degree(a)
      setcoeff!(c, i, divexact(coeff(a, i), b))
    end
    return c
  end


  p = gen(Qt) - s
  for k=length(ch)-1:-1:1
    p2 = (gen(Qt)-s)^ch[k]
    i = length(lf)
    j = i-1
    while j > 0
      h = lf[j]
      g = lf[j-1]
      @assert ismonic(g)
      @assert ismonic(h)
      b = la[j]
      a = la[j-1]
      f = lf[i]
      @assert ismonic(f)

      fgh = _div(f-g*h, p)
      G = pseudorem(fgh*b, g)*p+g
      H = pseudorem(fgh*a, h)*p+h
      t = _div(1-a*G-b*H, p)
      B = pseudorem(t*b, g)*p+b
      A = pseudorem(t*a, h)*p+a
      if i < length(lf)
        lf[i] = _mod(G*H, p2)
      end
      lf[j-1] = _mod(G, p2)
      lf[j] = _mod(H, p2)
      la[j-1] = _mod(A, p2)
      la[j] = _mod(B, p2)
      i -= 1
      j -= 2
    end
    p = p2
  end
  #now recombinationis missing - and bounds
  return lf[1:n], s
end

function (k::Nemo.GaloisField)(a::fmpq)
  return k(numerator(a))//k(denominator(a))
end

function (R::FmpzMPolyRing)(f::fmpq_mpoly)
  return map_coeffs(ZZ, f, parent = R)
end

function Hecke.roots(f::fmpq_mpoly, p::Int, k::Int)
  @assert nvars(parent(f)) == 2

  #f in Qxy
  Zx = Hecke.Globals.Zx
  ff = map_coeffs(ZZ, f)
  #TODO: 0 might not be a good evaluation point...
  #f needs to be irreducible over Q and g square-free
  g = evaluate(ff, [Zx(0), gen(Zx)])
  local d
  while true
    p = next_prime(p)
    gp = factor(g, GF(p))
    d = lcm([degree(x) for x = keys(gp.fac)])
    if d < degree(g)/2
      break
    end
  end
  F = QadicField(p, d, k)

  r = roots(g, F)

  Ft, t = F["t"]

  R = []
  for s = r
    o = Ft(inv(evaluate(derivative(g), s)))
    S = Ft(s)
    ti = t
    for i = 1:4
      ti *= ti
      _g = evaluate(ff, [t, S]) % ti
      S = (S - _g*o) % ti
      o = (o*(2-o*evaluate(derivative(ff, 2), [t, S]))) % ti
    end
    push!(R, S)
  end
  return R
end

function combination(R::Array, n::Int, d::Int)
  #R is a lost of roots, ie. polynomials over a q-Adic field
  #n is the t-adic precision
  #d a bound on the degree in "x" of the factors
  Ft = parent(R[1])
  t = gen(Ft)
  tn = t^n
  td = t^d

  #ps = [[div(x^i % tn, td^i) for i = 1:n] for x = R] 
  
  F = base_ring(Ft)
  k = degree(F)

  p = prime(F)
  ll = precision(F)

  m = identity_matrix(FlintZZ, length(R)) 
  i = 1
  j = 0
  while true
    @assert n> d*i
    n = matrix([[lift(coeff(coeff(div(x^i % tn, td^i), j), lk)) for lk = 0:k-1] for x = R])'
    nn = m[1:length(R), 1:length(R)]*n
    m = [m nn; zero_matrix(FlintZZ, ncols(nn), length(R)) p^ll*identity_matrix(FlintZZ, ncols(nn))]
    r, m = lll_with_removal(m, fmpz(length(R))^2)
    m = m[1:r, :]
    @show r
    if all(i->sum(m[i,j]^2 for j = 1:length(R)) <= length(R)^2, 1:r)
      return m[:, 1:length(R)]
    end
    j += 1
    if j > n-d*i
      i += 1
      j = 0
    end
  end

  return m[:, 1:length(R)]
end

function field(R::Array, m::fmpz_mat, d::Int)
  #we have roots, we need to combine roots for each row in m where the entry is pm 1
  #the coeffs then live is a number field, meaning that the elem sym functions or
  #the power sums will be needed
  #the field degree apears to be nrows(m)...

  #need primitive element, can use power sums up to #factors

  #we will ONLY find one factor, the others are galois conjugate
  #the field here is not necc. normal

  d_f = div(ncols(m), nrows(m))
  @assert ncols(m) == length(R)

  Ft = parent(R[1])
  F = base_ring(Ft)
  t = gen(Ft)
  td = t^d

  el = [[sum(R[i]^j % td for i=1:ncols(m) if m[lj, i] != 0) for j=1:d_f] for lj=1:nrows(m)]
  #assuming one coeff is primtive...
  i = 1
  j = 0
  K, mK = ResidueField(F)
  while true
    s = Set([mK(coeff(x[i], j)) for x = el])
    if length(s) == length(el)
      break
    end
    j += 1
    if j >= d
      j = 0
      i += 1
    end
  end

  pk = prime(F)^precision(F)
  p = [coeff(sum(coeff(x[i], j)^l for x = el), 0) for l=1:d_f-1]
  p = map(lift, p)
  p = map(x->rational_reconstruction(x, pk), p)
  @assert all(x->x[1], p)
  p = [x[2]//x[3] for x = p]

  k, a = number_field(Hecke.power_sums_to_polynomial(p))

  @show "using", k

  m = matrix([[(coeff(x[i], j)^l) for x = el] for l=0:degree(k)-1])
  kx, x = k["x"]
  P = elem_type(kx)[]

  for i = 1:d_f
    q = nf_elem[]
    for j=0:degree(el[1][i])
      n = matrix([[coeff(x[i], j)] for x = el])
      s = solve(m, n')
      @assert all(x->iszero(coeff(s[x, 1], 1)), 1:degree(k))
      s = [rational_reconstruction(lift(coeff(s[i, 1], 0))% pk, pk) for i=1:degree(k)]
      @assert all(x->x[1], s)
      push!(q, k([x[2]//x[3] for x = s]))
    end
    push!(P, kx(q))
  end
  @show P
  return Hecke.power_sums_to_polynomial(P)
end

function absolute_factorisation(f::fmpq_mpoly)
  p = next_prime(2^30)
  d = degree(f, 1)
  r = roots(f, p, d+2) #compute up to 16 in x
  z = combination(r, 16, d+2)
  return field(r, z, d)
end
  
end
