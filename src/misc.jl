
function basis_rels(b::Array{nf_elem, 1}, c; bd::fmpz = fmpz(10^35), no_p::Int = 4, no_rel::Int = 10000, no_coeff::Int = 4 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = fmpz(1)
  for i=1:no_rel
    zero!(a)
    for j=1:no_coeff
      cf = rand([-1, 1])
      p  = rand(1:nb)
      if cf==1
        Nemo.add!(a, a, b[p])
      else
        Nemo.sub!(a, a, b[p])
      end
    end
    n = norm_div(a, one, no_p)
    if cmpabs(num(n), bd) <= 0 
      if class_group_add_relation(c, a, n, one)
        a = b[1].parent()
      end
    end
  end
end


function rels_stat(b::Array{hecke.nf_elem, 1}; no_p = 4, no_rel::Int = 10000, no_coeff::Int = 4, fixed = 0, smooth=0 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = fmpz(1)

  stat = Dict{Int, Int}()
  if fixed != 0 
    stat[-1] = 0
  end
  if smooth != 0
    stat[-2] = 0
  end
  all_g = Array{Any, 1}()
  for i=1:no_rel
    zero!(a)
    for j=1:no_coeff
      cf = rand([-1, 1])
      p  = rand(1:nb)
      if cf==1
        Nemo.add!(a, a, b[p])
      else
        Nemo.sub!(a, a, b[p])
      end
    end
    if fixed!=0 && fixed(a) == a
      stat[-1] += 1
    end
    n = norm_div(a, one, no_p)
    k = div(ndigits(num(n), 2), 5)
    if haskey(stat, k)
      stat[k] += 1
    else
      stat[k] = 1
    end
    if smooth != 0 && is_smooth(smooth, num(n))[1]
      stat[-2] += 1
      push!(all_g, a)
    end  
  end
  return stat, all_g
end


function int_fb_max_real(f::Int, B::Int)
  lp = filter(isprime, 2:B)
  l1 = filter(x -> (x % f) ==1 || (x %f ) == f-1, lp) # the deg 1 primes
  filter!(x -> !(x in l1), lp)
  lr = filter(x -> f % x == 0, lp)  # ramified primes
  filter!(x -> !(x in lr), lp)
  lu = Array{Int, 1}()

  d = euler_phi(f)
  for r =2:d
    if d % r != 0
      continue
    end
    for p = lp
      if fmpz(p)^r  > B
        break
      end
      if powermod(p, r, f)==1 || powermod(p, r, f) == f-1
        push!(lu, p)
      end
    end
    filter!(x -> !(x in lu), lp)
  end

  return l1, lr, lu
end


function statistic{T}(st::Dict{Int,T})
  s = T(0)
  s2 = T(0)
  n = 0
  for k in keys(st)
    if k<1
      continue
    end
    t = st[k]
    s += k*t
    s2 += k^2*t
    n += t
  end
  av = s/n
  si = s2/n-av^2

  return av, si
end

function statistic{T}(st::Array{T, 1})
  s = T(0)
  s2 = T(0)
  n = length(st)
  for t in st
    s += t
    s2 += t^2
  end
  av = s/n
  si = s2/n-av^2

  return av, si
end

