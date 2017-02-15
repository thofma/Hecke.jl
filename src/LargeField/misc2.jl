
function basis_rels(b::Array{nf_elem, 1}, c; bd::fmpz = fmpz(10^35), no_b::Int = 250, no_rel::Int = 10000, no_coeff::Int = 4, no_id::fmpz = fmpz(0) )
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
    iszero(a) && continue
    n = norm_div(a, one, no_b)
    if cmpabs(num(n), bd) <= 0 
      if no_id != 0
        g = gcd(no_id, num(n))
        if g==1 || gcd(div(num(n), g), g) == 1
          if class_group_add_relation(c, a, n, one)
            a = b[1].parent()
          end
        end
      else
        if class_group_add_relation(c, a, n, one)
          a = b[1].parent()
        end
      end  
    end
  end
end

function basis_rels_2(b::Array{nf_elem, 1}, bd::fmpz = fmpz(10^35), no_b::Int = 250, no_rel::Int = 10000, no_coeff::Int = 4, no_id::fmpz = fmpz(0), smooth = 0 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = fmpz(1)
  rels = Array(Hecke.nf_elem, no_rel)
  i = 1
  l = 0
  while i < no_rel + 1
    l = l + 1
    #println(l)
    if l % 1000 == 0
      println("so far $l tries")
    end
    zero!(a)
    for j=1:no_coeff
      cf = rand([-1, 1])
      p  = rand(1:nb)
      if cf==1
        Nemo.add!(a, a, b[p])
      else
        Hecke.sub!(a, a, b[p])
      end
    end
    iszero(a) && continue
    if no_id != 0
      n = norm_div(a, no_id, no_b)
    else
      n = norm_div(a, one, no_b)
    end
    if smooth != 0
      !is_smooth(smooth, num(n))[1] && continue
    end
    if cmpabs(num(n), bd) <= 0 
      if no_id != 0
        g = gcd(no_id, num(n))
        if g==1 || gcd(div(num(n), g), g) == 1
          rels[i] = deepcopy(a)
          i = i +1
          println(i)
        end
      else
        rels[i] = deepcopy(a)
        i = i + 1
        println(i)
      end  
    end
  end
  return rels
end

function basis_rels_3(b::Array{nf_elem, 1}, no_b::Int = 250, no_rel::Int = 10000, no_coeff::Int = 5, no_id::fmpz = fmpz(1), smooth = 0 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  rels = Dict{fmpz, nf_elem}()
  i = 1
  l = 0
  while i < no_rel + 1
    l = l + 1
    #println(l)
    if l % 1000 == 0
      println("so far $l tries")
    end
    zero!(a)
    for j=1:no_coeff
      cf = rand([-1, 1])
      cf = 1
      p  = rand(1:nb)
      if cf==1
        Nemo.add!(a, a, b[p])
      else
        Hecke.sub!(a, a, b[p])
      end
    end
    iszero(a) && continue
    n = norm_div(a, no_id, no_b)
    if smooth != 0
      !is_smooth(smooth, num(n))[1] && continue
    end
    nn = abs(num(n))
    if !haskey(rels, nn)
      rels[nn] = deepcopy(a)
      i = i + 1
      println(i)
    end
  end
  return rels
end


function improve(c::Hecke.ClassGrpCtx)
  H = sub(c.M, 1:rows(c.M), 1:cols(c.M))
  Hecke.upper_triangular(H, mod = 17)
  p = setdiff(Set(1:cols(H)), Set([x.pos[1] for x=H.rows]))
  p = maximum(p)
  b = Hecke.bkz_basis(c.FB.ideals[p]);
#  b = rels_stat(b, ...)
  for x=b
    class_group_add_relation(c, b, n, one)
  end
end


function rels_stat(b::Array{Hecke.nf_elem, 1}; no_b = 250, no_rel::Int = 10000, no_coeff::Int = 4, fixed = 0, smooth=0 )
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
    if iszero(a) continue; end;
    if fixed!=0 && fixed(a) == a
      stat[-1] += 1
    end
    n = norm_div(a, one, no_b)
    k = div(ndigits(num(n), 2), 5)
    if haskey(stat, k)
      stat[k] += 1
    else
      stat[k] = 1
    end
    if smooth != 0 && is_smooth(smooth, num(n))[1]
      stat[-2] += 1
      push!(all_g, a)
      a =   a = b[1].parent()
    end  
  end
  return stat, all_g
end

function find_rels(b::Array{Hecke.nf_elem, 1}; no_b = 250, no_rel::Int = 10000, no_coeff::Int = 4, fixed = 0, smooth=0 )

  for i=10:50
    st, re = rels_stat(b, no_b = no_b, no_rel = no_rel, no_coeff = no_coeff, smooth =smooth)
    toNemo("/home/fieker/Rels128/rels128.$i", re, name="R$i");
  end
end

function find_rels2(b::Array{Hecke.nf_elem, 1}; no_b = 250, no_rel::Int = 10000, no_coeff::Int = 4, fixed = 0, smooth=0 )

  for i=100:150
    st, re = rels_stat(b, no_b = no_b, no_rel = no_rel, no_coeff = no_coeff, smooth =smooth)
    toNemo("/home/fieker/Rels128/rels128.$i", re, name="R$i");
  end
end

function int_fb_max_real(f::Int, B::Int)
  p = 2
  l1 = []
  lr = []
  lu = []
  sB = sqrt(B)


  while p <=  B
    if p % f == 1 || p % f == f-1
      push!(l1, p)
    elseif f % p == 0
      push!(lr, p)
    elseif p <= sB
      pp = fmpz(p)^2
      while pp <= B
        if pp % f == 1 || pp % f == -1
          push!(lu, p)
          break
        else
          pp *= p
        end
      end  
    end
    p = next_prime(p)
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

# If M is upper-triangular with more columns then rows,
# this function returns the non-pivot column indices.
function _find_missing_pivot(M::Smat)
  return setdiff(Set(1:cols(M)), Set([y.pos[1] for y = M.rows ])) 
end

function res_degree_in_max_real(p::Int, n::Int)
  r = valuation(n, 2)[2]
  r != 1 && error("Not yet implemented")
  f = Hecke.modord(p, n)
  return (powermod(p, div(f,2), n) == n-1) ? (return div(f, 2)) : (return f)
end

#function elem_type(::AnticNumberField)
#  return Nemo.nf_elem
#end
