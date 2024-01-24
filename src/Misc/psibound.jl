import Nemo.setcoeff!, Nemo.lift, Hecke.lift, Nemo.rem

#function setcoeff!(g::ZZModRelPowerSeriesRingElem, i::Int64, a::Nemo.EuclideanRingResidueRingElem{Nemo.ZZRingElem})
#  setcoeff!(g, i, lift(a))
#end

function bernstein(h::Int, it::Any, Q = FlintQQ, cl = ceil, a::Int = 776)
  #use 771 and cl = floor to get decent upper bounds
  # more on the choice of 776 and 771 in Dan's paper

  #println("in bernstein with a=$a and cl(0.5) = $(cl(0.5))")
  R,t = power_series_ring(Q, a*h+1, "t", model = :capped_absolute)

  #implements https://cr.yp.to/papers/psi.pdf
  # for smoothness for ideals, replace next_prime by the list of the norms of the prime
  # ideals
  # the sums of the coefficients of exp(g) are bounds for psi

  res = iterate(it)
  p, st = res

  #st = start(it)
  #p, st = next(it, st)
  g = R(0)
  tp = R(0)
  lpp = Int(cl(Float64(log(p))/log(2)*a))


  function do_single!(g::SeriesElem, pp::Int, np::Int)
    i = pp
    nu = Q(np)*Q(pp)
    while i <= a*h
      A = coeff(g, i)
      A += divexact(nu, Q(i))
      setcoeff!(g, i, lift(A))
      i += pp
    end
  end

  done = false

  while true
    pp = lpp
    np = 0
    while pp == lpp && res !== nothing #!done(it, st)
      np += 1
      res = iterate(it, st)
      if res === nothing
        break
      else
        p, st = res
      end
      lpp = Int(cl(Float64(log(p))/log(2)*a))

      if iterate(it, st) === nothing
        done = true
      else
        done = false
      end

      if done
        break
      end
    end

    if done && pp == lpp
      np += 1
    end

    do_single!(g, pp, np)

    if done
      if pp != lpp
        do_single!(g, lpp, 1)
      end
      return g
    end
  end
end

function _exp(a::ZZModAbsPowerSeriesRingElem)
  R = base_ring(parent(a))
  R = residue_ring(FlintZZ, Int(modulus(R)), cached = false)[1]
  Rx = polynomial_ring(R, cached = false)[1]
  A = Rx()
  for i=0:length(a)
    setcoeff!(A, i, lift(coeff(a, i)))
  end
  E = Rx()
  ccall((:nmod_poly_exp_series, libflint), Nothing, (Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}, Int64), E, A, length(a))
  r = parent(a)()
  for i=0:Nemo.length(E)-1
    setcoeff!(r, i, lift(coeff(E, i)))
  end
  return r
end

function _psi_lower(N::ZZRingElem, pr, a::Int=776, cl = ceil)
  p = ZZRingElem(next_prime(2^60))
  n = nbits(N)
#  println("precision of $n")
  f = _exp(bernstein(n, pr, residue_ring(FlintZZ, p, cached = false)[1], cl, a))
  Rt, t = power_series_ring(FlintZZ, n*a+1, "t", model = :capped_absolute)
  f = lift(Rt, f)
  pp = p
  while pp < N
    p = next_prime(p)
#    println("p: $p, pp: $pp N:$N")
    g = _exp(bernstein(n, pr, residue_ring(FlintZZ, p, cached = false)[1], cl, a))
    @assert length(g) == length(f)
    for i=0:length(f)
      setcoeff!(f, i, crt(coeff(f, i), pp, lift(coeff(g, i)), p))
    end
    pp *= p
  end
  res = []
  s = 0
  j = 0
  for i=0:n
    while j <= i*a && j < length(f)
      s += coeff(f, j)
      j += 1
    end
    push!(res, s)
    if j >= length(f) break; end
  end
  return res, f  # res[i] <= psi(2^(i-1), B)
end

@doc raw"""
    psi_lower(N::Integer, B::Int, a::Int = 776) -> Vector{Int}, ZZAbsPowerSeriesRingElem
    psi_lower(N::ZZRingElem, B::Int, a::Int = 776) -> Vector{Int}, ZZAbsPowerSeriesRingElem

Uses Bernstein's ideas: https://cr.yp.to/papers/psi.pdf
to compute lower bounds on the psi function counting smooth numbers.
An array $L$ is returned s.th. $\psi(2^{i-1}, B) \ge L_i$ for
$1\le i\le \rceil \log_2(B)\lceil$.
The second return value is Bernstein's power series.

The optional other parameter $a$ controls the precision of the result,
it defaults to 776.
"""
function psi_lower(N::ZZRingElem, B::Int, a::Int = 776)
  return _psi_lower(ZZRingElem(N), PrimesSet{Int}(2, B), a, ceil)
end

function psi_lower(N::Integer, B::Int, a::Int = 776)
  return _psi_lower(ZZRingElem(N), PrimesSet{Int}(2, B), a, ceil)
end

@doc raw"""
    psi_upper(N::Integer, B::Int a::Int=771) -> Vector{Int}, ZZAbsPowerSeriesRingElem
    psi_upper(N::ZZRingElem, B::Int a::Int=771) -> Vector{Int}, ZZAbsPowerSeriesRingElem

Uses Bernstein's ideas: https://cr.yp.to/papers/psi.pdf
to compute upper bounds on the psi function counting smooth numbers.
An array $U$ is returned s.th. $\psi(2^{i-1}, B) \ge U_i$ for
$1\le i\le \rceil \log_2(B)\lceil$.
The second return value is Bernstein's power series.

The optional other parameter $a$ controls the precision of the result,
it defaults to 771.
"""
function psi_upper(N::ZZRingElem, B::Int, a::Int=771)
  return _psi_lower(N, PrimesSet{Int}(2, B), a, floor)
end

function psi_upper(N::Integer, B::Int, a::Int=771)
  return _psi_lower(ZZRingElem(N), PrimesSet{Int}(2, B), a, floor)
end

@doc raw"""
    show_psi(N::Integer, B::Int)
    show_psi(N::ZZRingElem, B::Int)

Uses \code{psi_lower} and \code{psi_upper} to find intervals for
$\psi(2^i, B)$ to be in for $0\le i\le \log_2(N)$.
Where $\psi(N, B) = \#\{1\le i\le N | \text{$i$ is $B$-smooth}\}$
"""
function show_psi(N::Integer, B::Union{Int, NfFactorBase})
  gl = psi_lower(N, B)[1]
  gu = psi_upper(N, B)[1]
  l = 0
  u = 0
  for i=1:length(gl)
    if isa(B, Int)
      print("psi(2^$(i-1), $B)")
    else
      print("psi(2^$(i-1), B)")
    end
    l = gl[i]
    u = gu[i]
    if l==u
      println(" == $l")
    else
      println(" in [$l, $u]")
    end
  end
end

function show_psi(N::ZZRingElem, B::Int)
  show_psi(BigInt(N), B)
end

@doc raw"""
    psi_lower(N::Integer, B::NfFactorBase) -> Vector{Int}, ZZAbsPowerSeriesRingElem
    psi_lower(N::ZZRingElem, B::NfFactorBase) -> Vector{Int}, ZZAbsPowerSeriesRingElem

    psi_upper(N::Integer, B::NfFactorBase) -> Vector{Int}, ZZAbsPowerSeriesRingElem
    psi_upper(N::ZZRingElem, B::NfFactorBase) -> Vector{Int}, ZZAbsPowerSeriesRingElem

Uses Bernstein's techniques to bound the number of ideals $A$
of norm bounded by $N$ that are smooth over the factor base $B$.
"""
function psi_lower(N::Integer, B::NfFactorBase, a::Int=776)
  lp = sort(ZZRingElem[norm(x) for x=B.ideals])
  return _psi_lower(ZZRingElem(N), lp, a, ceil)
end

function psi_lower(N::ZZRingElem, B::NfFactorBase, a::Int=776)
  lp = sort(ZZRingElem[norm(x) for x=B.ideals])
  return _psi_lower(N, lp, a, ceil)
end

function psi_upper(N::Integer, B::NfFactorBase, a::Int=771)
  lp = sort(ZZRingElem[norm(x) for x=B.ideals])
  return _psi_lower(ZZRingElem(N), lp, a, floor)
end

function psi_upper(N::ZZRingElem, B::NfFactorBase, a::Int=771)
  lp = sort(ZZRingElem[norm(x) for x=B.ideals])
  return _psi_lower(N, lp, a, floor)
end

#=
test:

julia> sp = PrimesSet(2, 100);
julia> fb = []; for x=sp push!(fb, ZZRingElem(x)); end;
julia> fb = FactorBase(fb)
julia> length(find(x->is_smooth(fb, ZZRingElem(x)), 1:256))
julia> @assert psi_lower(255, 100)[1][end] == ans

=#
