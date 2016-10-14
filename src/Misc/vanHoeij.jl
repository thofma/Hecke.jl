import Nemo.lift
function mahler_measure_bound(f::fmpz_poly)
  return root(sum([coeff(f, i)^2 for i=0:degree(f)])-1, 2)+1
end 

function _val(m::fmpz, p::fmpz)  ## not used here, but fast -> Bernstein
  n, r = divrem(m, p)
  if !iszero(r)
    return 0, m
  end
  m = n
  v = 1
  p2 = p^2
  v2, m = _val(m, p2)
  v += 2*v2
  n, r = divrem(m, p)
  if iszero(r)
    v += 1
    m = n
  end
  return v, m
end

function _log(p::fmpz, m::fmpz)
  return Int(ceil(log(m)/log(p)))
end

function lift(M::FmpzMatSpace, Mp::Union{nmod_mat,GenMat{GenRes{fmpz}}})
  @assert M.cols == cols(Mp) && M.rows == rows(Mp)
  N = M()
  for i=1:M.rows
    for j=1:M.cols
      N[i,j] = lift(Mp[i,j])
    end
  end
  return N
end

_last = 1
function vanHoeji(f_orig::fmpz_poly, trunk::Bool = true)

  f = f_orig 
  g = gcd(f, derivative(f))
  while !isone(g) 
    f = divexact(f, g)
    g = gcd(f, derivative(f))
  end
  # now f is squarefree...

  #Bounds:
  #according to Klueners et all, the coefficients of the log lattive of the factors
  # (f/f_i f_i') are bounded by 
  #            choose(n-1, i) n M(f)
  # in the worst case, one has to lift up to this bound - which is maximal for
  # i=n/2 roughly.

  p = next_prime(degree(f))
  while discriminant(PolynomialRing(ResidueRing(ZZ, p))[1](f)) == 0
    p = next_prime(p)
  end

  n = degree(f)
  mmb = mahler_measure_bound(f)*n
  cld_bound = function(i)
    return mmb*binom(n-1, i)
  end

  # following Bill's paper
  # we build the matrix gradually...

  k = _log(fmpz(p), cld_bound(div(n, 2)))+1
  d = Int(ceil(4*nbits(n)/nbits(p))) * 2  + Int(ceil(0.2 * k))
  k_max = k


  H = factor_mod_pk_init(f, p)

  while true
    k = k_max
    println("now at precision $k_max+$d")
    pk = fmpz(p)^(d+k_max)
    R = ResidueRing(FlintZZ, pk)
    Rx = PolynomialRing(R)[1]

    println("lifting")
    @time ff = factor_mod_pk(H, d+k_max)
    ky = collect(keys(ff))
    ky = [Rx(x) for x= ky]
    Rf = Rx(f)
    r = length(ky)
    m = MatrixSpace(FlintZZ, r, r)(1)
    # gradual feeding...
    # build the complete p-adic matrix first, then worry about the version 
    # for LLL:
    p_adic = MatrixSpace(R, r, n)()
    j = 1
    @time for fi in ky
      g = div(Rf, fi)
#      h = prod(ky[find(x -> x != fi, ky)])
#      @assert h == g
      @assert degree(g) == n - degree(fi)
      g *= derivative(fi)  # g = f/f[i] * f[i]' 
      @assert degree(g) == n-1
      for i=0:degree(g)
        p_adic[j, i+1] = coeff(g, i)
      end
      j += 1
    end

    curr_col = -1
    bd = -1
    while true
      # need to add column(s) to m - otherwise nothing will work

      c = curr_col + 1
      if c >= n
        break
      end
      curr_col += 1
      println("adding col, now at $curr_col, $(rows(m))")
      bd = _log(fmpz(p), cld_bound(c))+1 # bound for THIS coeff only
      if bd > k_max
        print_with_color(:red, "prec change for next iteration\n")
      end  
      k_max = max(k_max, bd)
      rm = rows(m)
      _n = MatrixSpace(R, min(r, rm), r)(sub(m, 1:min(r, rm), 1:r)) * sub(p_adic, 1:r, n-1-c+1:n-1-c+1)
      _n = lift(MatrixSpace(FlintZZ, min(r, rm), 1), _n)
      # now we need to down-scale this...
      for i=1:min(r, rm)
        if trunk && bd <= k
          _n[i,1] = div(_n[i,1] % fmpz(p)^(bd+d), fmpz(p)^bd)
        else
          _n[i,1] = div(_n[i,1], fmpz(p)^bd)
        end
      end
      m = hcat(m, vcat(_n, MatrixSpace(ZZ, rows(m)-rows(_n), 1)()))
      if k+d > bd
        m = vcat(m, MatrixSpace(FlintZZ, 1, cols(m))())
        if trunk && bd <= k
          m[rows(m), cols(m)] = fmpz(p)^(d)
        else
          m[rows(m), cols(m)] = fmpz(p)^(k+d-bd)
        end
      else
        print_with_color(:yellow, "\n\n zero diag added \n\n")
      end

      if curr_col <= 2 # *div(nbits(r), 1)
        println("not enough cols")
        continue
      end

      println("scale")
      for i = 1:r
        for j=1:rows(m)
          m[j,i] *= r
        end
      end
      println("lll")
      @time rk, l = lll_with_removal(m, r*fmpz(r)^2 + fmpz(r)^2*curr_col) 
      println("un scale")
      for i = 1:r
        for j=1:rows(l)
          l[j,i] = div(l[j,i], r)
        end
      end

      if rk <1
        print_with_color(:red, "\n\nshit - loosing everything\n\n")
        return m
        break
      end
      @assert rk > 0
      if rk < rows(m)
        println("loosing rows! now at $rk from $(rows(m))")
      end
      m = sub(l, 1:rk, 1:cols(m))

      _cmp = function(i,j)
        local k = 1
        while k< rk && l[k, i] == l[k, j] 
          k += 1
        end
        return cmp(l[k, i], l[k, j])
      end  
      _lt(i,j) = _cmp(i,j)<0

      s = sort(1:r, lt = _lt)

      i = 1
      de = 0
      bad = 0
      fact = Dict{typeof(f), Int}()
      cls = Set{Array{Int, 1}}()
      grp = Array{Int, 1}()
      while i <= r
        j = i+1
        push!(grp, s[i])
        while j<=r && _cmp(s[i],s[j])==0
          push!(grp, s[j])
          j += 1
        end
        push!(cls, grp)
        grp = Array{Int, 1}()
        i = j
      end

      println("found $cls of length $(length(cls)) for $(rows(m))")
      bad = 0
      if length(cls) == rows(m)
        println("testing")
        for grp in cls
          fa = lift(parent(f_orig), prod(ky[grp]))

          local k
          for k=0:degree(fa)
            x = coeff(fa, k)
            if x > div(pk,2)
              x -= pk
            end
            setcoeff!(fa, k, x)
          end
          if iszero(pseudorem(f, fa))
            fact[fa] = 1
            de += degree(fa)
          else
            println("crap $fa")
            bad += 1
            break
          end
        end
        if de >= n
          Rx = PolynomialRing(ResidueRing(FlintZZ, p))[1]
          Rf = Rx(f_orig)
          for k in keys(fact)
            fact[k] = valuation(Rf, Rx(k))[1]
          end
          return fact 
        end
        if bad > 3
          break
        end
      end
    end
    d *= 2
  end
end

