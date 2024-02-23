
function basis_rels(b::Vector{AbsSimpleNumFieldElem}, c; bd::ZZRingElem = ZZRingElem(10^35), no_b::Int = 250, no_rel::Int = 10000, no_coeff::Int = 4, no_id::ZZRingElem = ZZRingElem(0) )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = ZZRingElem(1)
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
    if cmpabs(numerator(n), bd) <= 0
      if no_id != 0
        g = gcd(no_id, numerator(n))
        if g==1 || gcd(div(numerator(n), g), g) == 1
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

function basis_rels_2(b::Vector{AbsSimpleNumFieldElem}, bd::ZZRingElem = ZZRingElem(10^35), no_b::Int = 250, no_rel::Int = 10000, no_coeff::Int = 4, no_id::ZZRingElem = ZZRingElem(0), smooth = 0 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = ZZRingElem(1)
  rels = Array{Hecke.AbsSimpleNumFieldElem}(no_rel)
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
      !is_smooth(smooth, numerator(n))[1] && continue
    end
    if cmpabs(numerator(n), bd) <= 0
      if no_id != 0
        g = gcd(no_id, numerator(n))
        if g==1 || gcd(div(numerator(n), g), g) == 1
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

function basis_rels_3(b::Vector{AbsSimpleNumFieldElem}, no_b::Int = 250, no_rel::Int = 10000, no_coeff::Int = 5, no_id::ZZRingElem = ZZRingElem(1), smooth = 0 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  rels = Dict{ZZRingElem, AbsSimpleNumFieldElem}()
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
      !is_smooth(smooth, numerator(n))[1] && continue
    end
    nn = abs(numerator(n))
    if !haskey(rels, nn)
      rels[nn] = deepcopy(a)
      i = i + 1
      println(i)
    end
  end
  return rels
end

function local_norm!(n::ZZRingElem, ap::Vector{fqPolyRepFieldElem}, me::Hecke.modular_env)
  nn = UInt(1)
  np = UInt(1)
  for j=1:length(ap)
    ccall((:fq_nmod_norm, libflint), Nothing, (Ref{ZZRingElem}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), n, ap[j], ap[j].parent)
    nn = ccall((:n_mulmod2_preinv, libflint), UInt, (UInt, UInt, UInt, UInt), nn, UInt(n), me.up, me.upinv)
  end
  ccall((:fmpz_set_ui, libflint), Nothing, (Ref{ZZRingElem}, UInt), n, nn)
  return n
end

function local_norm(a::AbsSimpleNumFieldElem, me::Hecke.modular_env)
  Fpx = me.Fpx
  aa = Fpx(a)
  ff = Fpx(parent(a).pol)
  np = resultant(aa, ff, !true)
  return ZZRingElem(np)
end

function basis_rels_4(b::Vector{AbsSimpleNumFieldElem}, no_b::Int = 250, no_rel::Int = 10000, no_coeff::Int = 5, smooth = 0 )
  a = b[1].parent()
  t = b[1].parent()

  K = b[1].parent

  n = degree(K)

  if Int==Int32
    p = 2^30
  else
    p = 2^60
  end
  sp = PrimesSet(p, 2*p, 1024, 1)
  st = start(sp)
  p, st = next(sp, st)
  lp = [ZZRingElem(p)]
  i = no_b
  while i>0
    p, st = next(sp, st)
    push!(lp, ZZRingElem(p))
    i -= nbits(p[end])
  end

  crt_env = Hecke.crt_env(lp)
  np = Array{ZZRingElem}(length(lp))
  for i=1:length(lp)
    np[i] = ZZRingElem(0)
  end


  lpx = [modular_init(K, p) for p=lp]
  bp = Array{fqPolyRepFieldElem}(length(lpx), n, n)
  for i=1:length(lpx)
    for k=1:n
      ap = Hecke.modular_proj(b[k], lpx[i])
      for l=1:n
        bp[i, k, l] = ap[l]
      end
    end
  end
#  bp = [[deepcopy(Hecke.modular_proj(x, me)) for x = b] for me = lpx]

  tmp = Array{fqPolyRepFieldElem}(length(lpx), n)
  for i=1:length(lpx)
    for j=1:n
      tmp[i,j] = zero(parent(bp[i, 1, 1]))
    end
  end

#  tmp = [[zero(parent(x)) for x=bp[i][1]] for i=1:length(lpx)]

  lc = Vector{Int}()
  for i=1:no_coeff
    push!(lc, 0)
  end

  nb = length(b)

  rels = Dict{ZZRingElem, Vector{Int}}()
  i = 1
  ll = 0
  sum_nb = 0
  while i < no_rel + 1
    ll = ll + 1
    if ll % 1000 == 0
      println("so far $ll tries, avg nbits of norm ", sum_nb/ll)
    end
    for j=1:no_coeff
      p  = rand(1:nb)
      @inbounds lc[j] = p
    end
#    println("lc: $lc")
    for j=1:length(lpx)
      for k=1:n
        @inbounds ccall((:fq_nmod_set, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}), tmp[j, k], bp[j, lc[1], k])
        for l = 2:no_coeff
#          tmp[j][k] +=  bp[j][lc[l]][k]
          @inbounds add!(tmp[j, k], tmp[j, k], bp[j, lc[l], k])
        end
      end
#      @assert tmp[j] == Hecke.modular_proj(sum(b[lc]), lpx[j])
      local_norm!(np[j], tmp[j,:], lpx[j])
#      println(lpx[j])
#      println(np[j])
#      println(local_norm(sum(b[lc]), lpx[j]))
#      @assert local_norm(sum(b[lc]), lpx[j]) == np[j]
    end


    no = Hecke.crt_signed(np, crt_env)
    sum_nb += nbits(no)
#    println("testing $no")

    if smooth != 0
      !is_smooth(smooth, no)[1] && continue
    end
    nn = abs(no)
    if !haskey(rels, nn)
      rels[nn] = deepcopy(lc)
      i = i + 1
      println(i)
    else
      println("again $nn")
    end
  end
  return rels
end

function local_norm!(n::ZZRingElem, ap::zzModMatrix, me::Hecke.modular_env)
  nn = UInt(1)
  np = UInt(1)
  for j=1:nrows(ap)
    np = Nemo.getindex_raw(ap, j, 1)
    nn = ccall((:n_mulmod2_preinv, libflint), UInt, (UInt, UInt, UInt, UInt), nn, np, me.up, me.upinv)
  end
  ccall((:fmpz_set_ui, libflint), Nothing, (Ref{ZZRingElem}, UInt), n, nn)
  return n
end

function basis_rels_5(b::Vector{AbsSimpleNumFieldElem}, no_b::Int = 250, no_rel::Int = 10000, no_coeff::Int = 5, smooth = 0 )
  a = b[1].parent()
  t = b[1].parent()

  K = b[1].parent

  n = degree(K)

  if Int==Int32
    p = 2^30
  else
    p = 2^60
  end
  sp = PrimesSet(p, 2*p, 1024, 1)
  st = start(sp)
  p, st = next(sp, st)
  lp = [ZZRingElem(p)]
  i = no_b
  while i>0
    p, st = next(sp, st)
    push!(lp, ZZRingElem(p))
    i -= nbits(p[end])
  end
  println("using primes ", lp, " for modular norm")

  crt_env = Hecke.crt_env(lp)
  np = Array{ZZRingElem}(length(lp))
  for i=1:length(lp)
    np[i] = ZZRingElem(0)
  end


  lpx = [modular_init(K, p) for p=lp]
  bp = Array{fpMatrix}(length(lpx))
  for i=1:length(lpx)
    bp[i] = zero_matrix(GF(lpx[i].p, cached=false), n, n)
    for k=1:n
      ap = modular_proj(b[k], lpx[i])
      for l=1:n
        bp[i][l, k] = coeff(ap[l], 0)
      end
    end
  end
#  bp = [[deepcopy(modular_proj(x, me)) for x = b] for me = lpx]

  tmp = Array{fpMatrix}(length(lpx))
  lcp = Array{fpMatrix}(length(lpx))
  for i=1:length(lpx)
    tmp[i] = zero_matrix(GF(lpx[i].p, cached=false), n, 1)
    lcp[i] = zero_matrix(GF(lpx[i].p, cached=false), n, 1)
  end

  lc = Vector{Int}()
  for i=1:no_coeff
    push!(lc, 0)
  end

  nb = length(b)

  rels = Dict{ZZRingElem, Vector{Int}}()
  i = 1
  ll = 0
  sum_nb = 0
  @inbounds while i < no_rel + 1
    ll = ll + 1
    if ll % 1000 == 0
      println("so far $ll tries, avg nbits of norm ", sum_nb/ll)
    end
    for j=1:no_coeff
      lc[j]=0
    end
    for j=1:no_coeff
      p  = rand(1:nb)
      while p in lc
        p = rand(1:nb)
      end
      lc[j] = p
    end
    zero = false;
    for j=1:length(lpx)
      zero!(lcp[j])
      for k=lc
        Nemo.setindex_raw!!(lcp[j], Nemo.getindex_raw(lcp[j], k, 1) + UInt(1), k, 1)
        #should be unlikely - but seems to happen a lot:
        # duplication!
      end
      mul!(tmp[j], bp[j], lcp[j])
      local_norm!(np[j], tmp[j], lpx[j])
      if np[j] == UInt(0) zero = true; break; end;
#      if local_norm(sum(b[lc]), lpx[j]) != np[j]
#        return j, lpx, np[j], tmp[j], lc, bp, lcp
#      end
    end

    if zero continue; end


    no = crt_signed(np, crt_env)
#    @assert no == norm(sum(b[lc]))
    sum_nb += nbits(no)
    if iszero(no) continue; end #cannot (should not) happen. Tested above
#    println("testing $no")

    if smooth != 0
      !is_smooth(smooth, no)[1] && continue
    end
    nn = abs(no)
    if !haskey(rels, nn)
#      z = sum(b[lc])
#      nz = norm_div(z, ZZRingElem(1), no_b)
#      @assert norm_div(sum(b[lc]), ZZRingElem(1), no_b) == no
      rels[nn] = deepcopy(lc)
      i = i + 1
      println(i)
    else
      println("again $nn")
    end
  end
  return rels
end


#=

Qx,x = polynomial_ring(FlintQQ, "a")
K, a = cyclotomic_real_subfield(1024, "a");
@time fb_int = Hecke.int_fb_max_real(1024, 2^20);
h = Hecke.auto_of_maximal_real(K, 3);
b = [K(1), a]
while length(b) < 256 push!(b, h(b[end])); end
fb_int = FactorBase(ZZRingElem[x for x = vcat(fb_int[1], fb_int[2], fb_int[3])]);
@time Hecke.basis_rels_4(b, 600, 10, 5, fb_int)
@time Hecke.basis_rels_5(b, 600, 10, 5, fb_int)

Qx,x = polynomial_ring(FlintQQ, "a")
K, a = cyclotomic_real_subfield(512, "a");
@time fb_int = Hecke.int_fb_max_real(512, 2^18);
h = Hecke.auto_of_maximal_real(K, 3);
b = [K(1), a]
while length(b) < 128 push!(b, h(b[end])); end
fb_int = FactorBase(ZZRingElem[x for x = vcat(fb_int[1], fb_int[2], fb_int[3])]);
@time basis_rels_4(b, 300, 100, 5, fb_int)
@time basis_rels_5(b, 300, 100, 5, fb_int)



=#

function improve(c::Hecke.ClassGrpCtx)
  H = sub(c.M, 1:nrows(c.M), 1:ncols(c.M))
  Hecke.upper_triangular(H, mod = 17)
  p = setdiff(Set(1:ncols(H)), Set([x.pos[1] for x=H.rows]))
  p = maximum(p)
  b = Hecke.bkz_basis(c.FB.ideals[p]);
#  b = rels_stat(b, ...)
  for x=b
    class_group_add_relation(c, b, n, one)
  end
end


function rels_stat(b::Vector{Hecke.AbsSimpleNumFieldElem}; no_b = 250, no_rel::Int = 10000, no_coeff::Int = 4, fixed = 0, smooth=0 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = ZZRingElem(1)

  stat = Dict{Int, Int}()
  if fixed != 0
    stat[-1] = 0
  end
  if smooth != 0
    stat[-2] = 0
  end
  all_g = Vector{Any}()
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
    k = div(ndigits(numerator(n), 2), 5)
    if haskey(stat, k)
      stat[k] += 1
    else
      stat[k] = 1
    end
    if smooth != 0 && is_smooth(smooth, numerator(n))[1]
      stat[-2] += 1
      push!(all_g, a)
      a =   a = b[1].parent()
    end
  end
  return stat, all_g
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
      pp = ZZRingElem(p)^2
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


function statistic(st::Dict{Int,T}) where T
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

function statistic(st::Vector{T}) where T
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
function _find_missing_pivot(M::SMat)
  return setdiff(Set(1:ncols(M)), Set([y.pos[1] for y = M.rows ]))
end

function res_degree_in_max_real(p::Int, n::Int)
  r = remove(n, 2)[2]
  r != 1 && error("Not yet implemented")
  f = Hecke.modord(p, n)
  return (powermod(p, div(f,2), n) == n-1) ? (return div(f, 2)) : (return f)
end
