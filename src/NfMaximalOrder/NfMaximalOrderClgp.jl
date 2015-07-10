################################################################################
#
#  NfMaxOrdClgrp.jl : Class group computation of maximal orders in number fields
#
################################################################################

# (C) 2015 Claus Fieker

################################################################################
#
# Todo: 
#  - using/ implement limit in enum
#  - make sure the precision for LLL is high enough (by checking that the
#    resulting elements have a reasonable norm/ length? theory?)
#  - add reasonable verbose printing
#  - write hnf from upper_triangular
#  - understand/use profiling information (memory, ...)     
#
# Clean up:
#  - sort the various data-types files
#  - write show functions
#  - remove debugging prints
#  - arrange the functions in e.g. Sparse in a reasonable order
#  - rename some of them
#  - export 
#  - use iterators in add_scaled and transform?
#
# Note: enumerating x,0,0,0 is pointless unless x==1
#
################################################################################

add_verbose_scope(:ClassGroup)
add_verbose_scope(:ClassGroup_time)
add_verbose_scope(:ClassGroup_gc)

add_assert_scope(:ClassGroup)
set_assert_level(:ClassGroup, 1)
set_assert_level(:LatEnum, 1)


import Base.size;

################################################################################
#
#  Factor base over (Euclidean) Rings
#
################################################################################

# Note that T must admit gcd's and base must consists of elements x for which
# valuation(_, x) is definied.

type FactorBase{T}
  prod::T
  base::Set{T}
end

# assume that the set consists of pairwise coprime elements
function FactorBase{T}(x::Set{T}; check::Bool = true)
  if !check
    z = FactorBase{T}(prod(x), x)
    return z
  else
    error("not yet implemented")
  end
end

function show(io::IO, B::FactorBase)
  print(io, "Factor base with \n$(B.base) and type $(typeof(B.prod))")
end

function is_smooth{T}(c::FactorBase{T}, a::T)
  g = gcd(c.prod, a)
  while g != 1 
    a = div(a, g)
    g = gcd(g, a)
  end
  return a == 1
end

function factor{T}(c::FactorBase{T}, a::T)
  f = Dict{T, Int}()
  for i in c.base
    if mod(a, i)==0
      v = valuation(a, i)
      f[i] = v[1]
      a = v[2]
      if a == 1 
        break
      end
    end
  end
  assert(a==1)
  return f
end

function factor{T}(c::FactorBase{T}, a::fmpq)
  f = Dict{T, Int}()
  n = num(a)
  d = den(a)
  for i in c.base
    if mod(d, i)==0
      v = valuation(d, i)
      if isdefined(f, :i)
        f[i] -= v[1]
      else
        f[i] = -v[1]
      end
      d = v[2]
      if d == 1 && n == 1
        break
      end
    end
    if mod(n, i)==0
      v = valuation(n, i)
      if isdefined(f, :i)
        f[i] += v[1]
      else
        f[i] = v[1]
      end
      n = v[2]
      if d == 1 && n==1
        break
      end
    end
  end
  @hassert :ClassGroup 1 d == 1 && n == 1 
  return f
end

################################################################################
#
#  NfFactorBase : Factor bases for number fields 
#  A factor basis is mostly a collection of prime ideals, designed,
#  if possible, to allow for rapid testing if elements are smooth.
#
################################################################################

type NfFactorBase
  fb::Dict{fmpz, Array{Tuple{Int, NfMaximalOrderIdeal}, 1}}
  size::Int
  fb_int::FactorBase{fmpz}
  ideals::Array{NfMaximalOrderIdeal, 1}
  rw::Array{Int, 1}
  mx::Int

  function NfFactorBase()
    r = new(Dict{fmpz, Array{Tuple{Int, MaximalOrderIdeal}, 1}}())
    r.size = 0
    return r
  end
end

function NfFactorBase(O::NfMaximalOrder, B::Int;
                      complete::Bool = true, degree_limit::Int = 5)
  lp = prime_ideals_up_to(O, B, complete = complete,
                          degree_limit = degree_limit)
  lp = sort(lp, lt = function(a,b) return norm(a) > norm(b); end)
  FB = NfFactorBase()
  FB.size = length(lp)
  FB.ideals = lp

  # Magic constant 20?
  FB.rw = Array(Int, 20)
  FB.mx = 20

  for i = 1:length(lp)
    if !haskey(FB.fb, lp[i].gen_one)
      FB.fb[lp[i].gen_one] = [(i, lp[i])]
    else
      push!(FB.fb[lp[i].gen_one], (i, lp[i]))
    end
  end

  FB.fb_int = FactorBase(Set(keys(FB.fb)); check = false)

  return FB
end

################################################################################
#
#  Factor number field element over factor base. Put valuations into row i of
#  the relation matrix M. The matrix M needs to have at least as many columns
#  as the FB has ideals.
#
################################################################################

function factor!(M::fmpz_mat, i::Int, FB::NfFactorBase, a::nf_elem;
                 error::Bool = true, n::fmpq = abs(norm(a)))
  return _factor!(M, i, FB, a, error, n)
end
function _factor!(M::fmpz_mat, i::Int, FB::NfFactorBase, a::nf_elem,
                 error::Bool = true, n::fmpq = abs(norm(a)))
  d = factor(FB.fb_int, num(n)*denominator(a))
  cor = []
  for p in keys(d)
    for (j, P) in FB.fb[p]
      M[i, j] = valuation(a, P)
      if M[i,j] != 0
        push!(cor, j)
      end
      if M[i,j] < 0 
        n = n*norm(P)^(-M[i, j])
      else
        n = n/norm(P)^M[i, j]
      end  
    end
  end
  if error
    @hassert :ClassGroup 1 n == 1
  else
    if n != 1
      for j in cor
        M[i,j] = 0
      end
    end
    return n == 1
  end
  return true
end

function factor!{T}(M::Smat{T}, i::Int, FB::NfFactorBase, a::nf_elem;
                    error = true, n = abs(norm(a)))
  return _factor(M, i, FB, a, error, n)
end
function _factor!{T}(M::Smat{T}, i::Int, FB::NfFactorBase, a::nf_elem,
                    error::Bool = true, n::fmpq = abs(norm(a)))
  d = factor(FB.fb_int, num(n)*denominator(a))
  rw = FB.rw
  lg::Int = 0
  for p in keys(d)
    vp = valuation(n, p)[1]
    for (j, P) in FB.fb[p]
      v = valuation(a, P)
      if v != 0
        vp -= P.splitting_type[2]*v
        lg += 1
        if lg <= FB.mx
          rw[lg] = j
          rw[lg + 1] = v
        else
          push!(rw, j)
          push!(rw, v)
        end
        lg += 1
      end
    end
    if vp != 0
      if error
        @hassert :ClassGroup 1 vp == 0
      end
      return false
    end
  end
  if lg > 0
    if length(rw) > FB.mx
      FB.mx = length(rw)
    end
    @hassert :ClassGroup lg > 1
    @hassert :ClassGroup iseven(lg)
    nrw = Array{Tuple{Int, Int}}(div(lg, 2))
    for i = 1:div(lg, 2)
      nrw[i] = (rw[2*(i-1)+1], rw[2*i])
    end
    sort!(nrw, lt=function(a,b) return a[1] < b[1]; end)
    @hassert :ClassGroup 1 length(nrw) > 0
    push!(M, SmatRow{T}(nrw))
    return true
  else 
    # factor failed or I have a unit.
    # sparse rel mat must not have zero-rows.
    return false
  end
end

function factor(FB::NfFactorBase, a::nf_elem)
  M = MatrixSpace(FlintZZ, 1, FB.size)()
  factor!(M, 1, FB, a)
  return M
end
################################################################################
#
#  Class group data structure
#
################################################################################
type ClassGrpCtx{T}  # T should be a matrix type: either fmpz_mat or Smat{}
  FB::NfFactorBase
  M::T                    # the relation matrix, columns index by the
                          # factor basis, rows by the relations
  R::Array{nf_elem, 1}    # the relations
  RS::Set{nf_elem}
  H::T                    # the last hnf, at least the non-trivial part
                          # of it
  last_H::Int             # the number of rows of M that went into H
  last_piv1::Array{Int, 1}
  mis::Set{Int}
  h::fmpz
  c::roots_ctx
  rel_cnt::Int
  bad_rel::Int
  hnf_call::Int
  hnf_time::Float64
  last::Int
  sum_norm::fmpz

  val_base::fmpz_mat      # a basis for the possible infinite ranodmization 
                          # vectors: conditions are
                          #  - sum over all = 0
                          #  - indices correspoding to complex pairs are
                          #    identical
                          # done via lll + nullspace
  function ClassGrpCtx()
    r = new()
    r.R = Array{nf_elem, 1}[]
    r.RS = Set(r.R)
    return r
  end  
end


################################################################################
#
#  Relations based on ideals
#
################################################################################

type IdealRelationsCtx{Tx, TU, TC}
  A::NfMaximalOrderIdeal
  v::Array{Int, 1}  # the infinite valuation will be exp(v[i])
  E::enum_ctx{Tx, TU, TC}
  c::fmpz           # the last length
  cnt::Int
  bad::Int
  M::fmpz_mat
  vl::Int
  rr::Range{Int}

  function IdealRelationsCtx(clg::ClassGrpCtx, A::NfMaximalOrderIdeal;
                  prec::Int64 = 100, val::Int64=0, limit::Int64 = 0)
    v = MatrixSpace(FlintZZ, 1, rows(clg.val_base))(Base.rand(-val:val, 1,
                    rows(clg.val_base)))*clg.val_base
    E = enum_ctx_from_ideal(clg.c, A, v, prec = prec, limit = limit,
       Tx = Tx, TU = TU, TC = TC)::enum_ctx{Tx, TU, TC}
    I = new()
    I.E = E
    I.A = A
    I.c = 0
    I.cnt = 0
    I.bad = 0
    I.vl = 0
    I.rr = 1:0
    I.M = MatrixSpace(FlintZZ, 1, I.E.n)()
    return I
  end


end

function show(io::IO, I::IdealRelationsCtx)
  println(io, "IdealRelationCtx for ", I.A)
  println(io, "  current length bound ", I.c, " stats: ", I.cnt, " and ", I.bad)
end


################################################################################
#
#  The main class group part
#
################################################################################

global AllRels
function class_group_init(O::NfMaximalOrder, B::Int;
                          complete::Bool = true, degree_limit::Int = 5, T::DataType = Smat{BigInt})
  global AllRels = []
  clg = ClassGrpCtx{T}()

  clg.bad_rel = 0
  clg.rel_cnt = 0
  clg.last = 0
  clg.sum_norm = 0

  clg.FB = NfFactorBase(O, B, complete = complete, degree_limit = degree_limit)
  clg.M = T()
  clg.c = conjugates_init(nf(O).pol)
  for I in clg.FB.ideals
    class_group_add_relation(clg, nf(O)(I.gen_one))
    class_group_add_relation(clg, nf(O)(I.gen_two))
  end
  n = degree(O)
  l = MatrixSpace(FlintZZ, n, 1+clg.c.r2)()
  for i = 1:n
    l[i,1] = 1
  end
  for i = 1:clg.c.r2
    l[clg.c.r1+2*i, i+1] = 1
    l[clg.c.r1+2*i-1, i+1] = -1
  end
  # what I want is a lll-reduced basis for the kernel
  # it probably should be a sep. function
  # however, there is nullspace - which is strange...
  l,t = hnf_with_transform(l)
  t = sub(t, (1+clg.c.r2+1):rows(l), 1:rows(l))
  l = lll(t)
  clg.val_base = l
  return clg
end

function class_group_add_relation{T}(clg::ClassGrpCtx{T}, a::nf_elem)
  if a==0
    return false
  end
  if a in clg.RS 
    return false
  end
#  global AllRels
#  push!(AllRels, a)
  n = abs(norm(a))
  clg.sum_norm += num(n*n)
  #print("trying relation of length ", Float64(length(clg.c, a)),
  #      " and norm ", Float64(n));
  if !is_smooth(clg.FB.fb_int, num(n)*denominator(a))
    clg.bad_rel += 1
    #println(" -> fail")
    return false
  end
  if _factor!(clg.M, length(clg.R)+1, clg.FB, a, false, n)
    push!(clg.R, a)
    push!(clg.RS, a)
    @hassert :ClassGroup 1 rows(clg.M) == length(clg.R)
    clg.rel_cnt += 1
    @v_do :ClassGroup 1 println(" -> OK, rate currently ",
           clg.bad_rel/clg.rel_cnt, " this ", clg.bad_rel - clg.last,
           ", avg (norm^2) ",
           Float64(BigInt(clg.sum_norm)/(clg.bad_rel-clg.last+1)))
    clg.last = clg.bad_rel
    clg.sum_norm = 0
    return true
  else
    #println(" -> 2:fail")
    clg.bad_rel += 1
    return false
  end
end

################################################################################
#
#  Naive relation search: Based on coefficient size only
#
################################################################################

function class_group_random_ideal_relation(clg::ClassGrpCtx, r::Int,
                                           I::NfMaximalOrderIdeal = Base.rand(clg.FB.ideals))
  s = 1
  if r < 2
    r = 2
  end
  for i = 1:r 
    I = prod(I, Base.rand(clg.FB.ideals))
    I, g = reduce_ideal_class(I)
    s *= g
  end
  return s;
end 

################################################################################
#
# Naive relation search: Tries random linear combinations of lll reduced basis
# The lll is done on the coefficient lattice.   
#
################################################################################
function class_group_small_elements_relation(clg::ClassGrpCtx,
                A::NfMaximalOrderIdeal, cnt::Int = degree(order(A)))
  l = FakeFmpqMat(lll(basis_mat(A)))*basis_mat(order(A))
  K = nf(order(A))
  if cnt <= degree(A.parent.order)
    lb = Array(nf_elem, degree(K))
    for i = 1:cnt
      lb[i] = element_from_mat_row(K, l.num, i)//l.den
    end
    return lb
  end
  r = Int(Base.ceil((2*cnt)^(1/degree(K))))
  r = -div(r+1, 2):div(r+1, 2)
  ll = Array(typeof(K()), degree(K))
  for i = 1:degree(K)
    ll[i] = element_from_mat_row(K, l.num, i)//l.den
  end
  lb = Array(typeof(K()), cnt)
  for i = 1:cnt
    lb[i] = rand(ll, r)
  end
  return lb
end

################################################################################
#
# More interesting search: Enumeration and other things on the minkowski side
#
################################################################################

#scales the i-th column of a by 2^d[1,i]
function mult_by_2pow_diag!(a::Array{BigFloat, 2}, d::fmpz_mat)
  s = size(a)
  R = RealRing()
  tmp_mpz = R.z1
  for i = 1:s[1]
    for j = 1:s[2]
      e = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ptr{BigInt}, Ptr{BigFloat}), &tmp_mpz, &a[i,j])
      ccall((:mpfr_set_z_2exp, :libmpfr), Void, (Ptr{BigFloat}, Ptr{BigInt}, Clong, Int32), &a[i,j], &tmp_mpz, e+Clong(d[1,j]), Base.MPFR.ROUNDING_MODE[end])
    end
  end
end

#converts BigFloat -> fmpz via round(a*2^l), in a clever(?) way
function round_scale(a::Array{BigFloat, 2}, l::Int)
  s = size(a)
  b = MatrixSpace(FlintZZ, s[1], s[2])()
  R = RealRing()
  tmp_mpz = R.z1
  tmp_fmpz = R.zz1
  tmp_mpfr = R.t1
  for i = 1:s[1]
    for j = 1:s[2]
      e = a[i,j].exp
      a[i,j].exp += l
      ccall((:mpfr_round, :libmpfr), Int32, (Ptr{BigFloat}, Ptr{BigFloat}, Int32), &tmp_mpfr, &a[i,j], Base.MPFR.ROUNDING_MODE[end]) 
      a[i,j].exp = e
      f = ccall((:mpfr_get_z_2exp, :libmpfr), Clong, (Ptr{BigInt}, Ptr{BigFloat}),
        &tmp_mpz, &tmp_mpfr)
      ccall((:fmpz_set_mpz, :libflint), Void, (Ptr{fmpz}, Ptr{BigInt}),
        &tmp_fmpz, &tmp_mpz)
      if f > 0  
        ccall((:fmpz_mul_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Culong), &tmp_fmpz, &tmp_fmpz, f)
      else
        ccall((:fmpz_tdiv_q_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Culong), &tmp_fmpz, &tmp_fmpz, -f);
      end
      setindex!(b, tmp_fmpz, i, j)
    end
  end
  return b
end

function shift!(g::fmpz_mat, l::Int)
  for i=1:rows(g)
    for j=1:cols(g)
      z = ccall((:fmpz_mat_entry, :libflint), Ptr{fmpz}, (Ptr{fmpz_mat}, Int, Int), &g, i-1, j-1)
      if l > 0
        ccall((:fmpz_mul_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, l)
      else
        ccall((:fmpz_tdiv_q_2exp, :libflint), Void, (Ptr{fmpz}, Ptr{fmpz}, Int), z, z, -l)
      end
    end
  end
  return g
end
 
#CF todo: use limit!!!
function lll(rt_c::roots_ctx, A::NfMaximalOrderIdeal, v::fmpz_mat;
                prec::Int = 100, limit::Int = 0)
  c = minkowski_mat(rt_c, nf(order(A)), prec) ## careful: current iteration
  b = FakeFmpqMat(basis_mat(A))*basis_mat(order(A))
  if !isdefined(rt_c, :cache)
    rt_c.cache = 0*c
  end
  d = rt_c.cache
  mult!(d, b.num, c)
                                           ## c is NOT a copy, so don't change.
  if !iszero(v)
    @v_do :ClassGroup 1 println("using inf val", v)
    old = get_bigfloat_precision()
    set_bigfloat_precision(4*prec)
    mult_by_2pow_diag!(d, v);
    set_bigfloat_precision(old)
  end
  old = get_bigfloat_precision()
  set_bigfloat_precision(prec)
  g = round_scale(d, prec)
  @hassert :ClassGroup 1 !iszero(g)
  set_bigfloat_precision(old)
  g = g*g'
  shift!(g, -prec)
  g += rows(g)*one(parent(g))

  l, t = lll_gram_with_transform(g)
  return l, t
end

################################################################################
#
#  Algorithm of Schmettow
#
################################################################################

function one_step(c::roots_ctx, b::NfMaximalOrderFracIdeal,
                p::NfMaximalOrderIdeal; prec::Int = 100)
  b = p*b
  simplify(b)
  g1 = short_elem(c, b, prec = prec)
  b = g1*inv(b) 
  simplify(b)
  g2 = short_elem(c, b, prec = prec) 
  return simplify(g2*inv(b)), g1, g2
end

function short_elem(c::roots_ctx, A::NfMaximalOrderFracIdeal,
                v::fmpz_mat=MatrixSpace(FlintZZ, 1,1)(); prec::Int = 100)
  return divexact(short_elem(c, A.num, v, prec = prec), A.den)
end

function short_elem(c::roots_ctx, A::NfMaximalOrderIdeal,
                v::fmpz_mat = MatrixSpace(FlintZZ, 1,1)(); prec::Int = 100)
  K = nf(order(A))
  temp = FakeFmpqMat(basis_mat(A))*basis_mat(order(A))
  b = temp.num
  b_den = temp.den
  l, t = lll(c, A, v, prec = prec)
  w = window(t, 1,1, 1, cols(t))
  c = w*b
  q = element_from_mat_row(K, c, 1)
  q = divexact(q, b_den)
  return q
end

function enum_ctx_from_ideal(c::roots_ctx, A::NfMaximalOrderIdeal,
                v::fmpz_mat;prec::Int = 100, limit::Int = 0, Tx::DataType = Int, TU::DataType = Float64, TC::DataType = Float64)
  l, t = lll(c, A, v, prec = prec, limit = limit)
  temp = FakeFmpqMat(basis_mat(A))*basis_mat(order(A))
  b = temp.num
  b_den = temp.den
  K = nf(order(A))
  if limit == 0
    limit = rows(l)
  end
  #E = enum_ctx_from_gram(l, FlintZZ(2)^prec, Tx = BigInt, TC = Rational{BigInt},
  #                TC = Rational{BigInt}, limit = limit)
  E = enum_ctx_from_gram(l, FlintZZ(2)^prec, Tx = Tx, TC = TC, TU = TU,
                  limit = limit)::enum_ctx{Tx, TC, TU}
  E.t = t*b
  E.t_den = b_den
  n = E.n
  b = E.G[n,n]
  enum_ctx_start(E, b)
  return E
end

global _start = 0.0
function class_group_small_real_elements_relation_start(clg::ClassGrpCtx,
                A::NfMaximalOrderIdeal; prec::Int = 200, val::Int = 0,
                limit::Int = 0)
  global _start
  @v_do :ClassGroup_time 2 rt = time_ns()
  I = IdealRelationsCtx{Int, Float64, Float64}(clg, A, prec = prec, val = val, limit = limit)
  @v_do :ClassGroup_time 2 _start += time_ns()-rt
  return I
end

global _elt = Uint(0)

function class_group_small_real_elements_relation_next(I::IdealRelationsCtx)
  global _elt, _next
  K = nf(order(I.A))
  while true
    if enum_ctx_next(I.E)
      # println("elt is", I.E.x)
      # should we (again) add content_is_one()?
      if !isone(content(I.E.x))
        continue
      end
      @v_do :ClassGroup_time 2 rt = time_ns()
      I.M = I.E.x * I.E.t
      q = element_from_mat_row(K, I.M, 1)
      q = divexact(q,I.E.t_den)
      #println("found ", q, " of length ", length(q), " and norm ", norm(q))
      @v_do :ClassGroup_time 2 _elt += time_ns()- rt
      return q
    end
    #println("restart for ", I.A, I.E.c)
    enum_ctx_start(I.E, I.E.c*2)
  end
end

# Do better: re-use partial hnf, check rank mod p, ...

const modu = next_prime(2^20)
function class_group_current_result(clg::ClassGrpCtx)
  global modu
  full_rank = false
  if isdefined(clg, :H)
    full_rank = rows(clg.H) == cols(clg.H)
    new_rel = sub(clg.M, (clg.last_H+1):rows(clg.M), 1:cols(clg.M))
    last_diag = [clg.H[i,i] for i =1:min(rows(clg.H), cols(clg.H))]
    vcat!(clg.H, new_rel)
    h = clg.H
    t = time_ns()
    if ! full_rank
      upper_triangular(h, mod = modu)
    else
      upper_triangular(h)
    end
    clg.hnf_time += time_ns()-t
    clg.hnf_call += 1
    diag = [clg.H[i,i] for i =1:min(rows(clg.H), cols(clg.H))]
    if diag == last_diag
      deleteat!(clg.M.rows, (clg.last_H+1):length(clg.R))
      deleteat!(clg.R, (clg.last_H+1):length(clg.R))
      clg.M.r = length(clg.M.rows)
      @vprint :ClassGroup 1 "pruning again...\n"
    end
  else
    full_rank = false
    t = time_ns()
    h = sub(clg.M, 1:clg.M.r, 1:clg.M.c)
    upper_triangular(h)
    clg.hnf_time += time_ns()-t
    clg.hnf_call += 1
    last_H = 0
  end
  @v_do :ClassGroup 1 println("rank is currently ", rows(h), " need to be ",
                  cols(h), clg.M)
  clg.H = h
  clg.last_H = length(clg.R)
  if length(clg.R)/rows(h) > 4
    error("no enough useful relations")
  end
    
  piv = Array(Int, 0)
  for i = 1:rows(h)
    push!(piv, h.rows[i].entry[1].col)
  end
  mis = setdiff(Set(1:cols(h)), Set(piv))

  if length(mis) > 0
    clg.mis = mis
    clg.h = FlintZZ(0)
    return (fmpz(0), mis)::Tuple{fmpz, Set{Int64}}
  end

  if full_rank
    clg.h = FlintZZ(abs(prod([h[i,i] for i=1:cols(h)])))
  else
    @vprint :ClassGroup 1 "1st non-modular"
    @v_do :ClassGroup 4 toMagma("/tmp/big.m", clg.M)
    h = copy(clg.M)
    @vtime :ClassGroup 1 upper_triangular(h)
    clg.H = h
    clg.h = FlintZZ(abs(prod([h[i,i] for i=1:cols(h)])))
  end

  clg.mis = Set(1:0)
  return (clg.h, clg.mis)::Tuple{fmpz, Set{Int}}
end

################################################################################
#
#  Main loop to find relations
#
################################################################################

function class_group_find_relations(clg::ClassGrpCtx; val = 0, prec = 100,
                limit = 10)
  clg.hnf_time = 0.0
  clg.hnf_call = 0
  clg.rel_cnt = 0
  clg.bad_rel = 0

  n = degree(clg.FB.ideals[1].parent.order)
  t = time_ns()
  I = []
  for i in clg.FB.ideals
    f = class_group_small_real_elements_relation_start(clg, i, limit = limit,
                    prec = prec)
    push!(I, f)
    f.vl = val
    while true
      class_group_small_real_elements_relation_next(I[end])

      f = class_group_add_relation(clg,
                      class_group_small_real_elements_relation_next(I[end]))
      if f
        I[end].cnt += 1
        break
      else
        I[end].bad += 1
        if I[end].bad > (clg.bad_rel/clg.rel_cnt)*2
          @v_do :ClassGroup 2 println("too slow in getting s.th. for ", i,
                          "good: ", I[end].cnt,  " bad: ",  I[end].bad,
                          " ratio: ", (clg.bad_rel/clg.rel_cnt))
          break
        end
      end
    end
    @v_do :ClassGroup_gc 1 gc()
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-t)/1e9,
                  " sec for small elts, so far ", clg.hnf_time/1e9,
                  " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)

  s = time_ns()

  h, piv = class_group_current_result(clg)

  idl = clg.FB.ideals
  want_extra = 5
  bad_h = false
  while h != 1 && (h==0 || want_extra > 0)
    for i in sort([ x for x in piv], lt = >)
      E = I[i]
      lt = max(100, Base.round((clg.bad_rel/clg.rel_cnt)*2))
      a = 1
      limit_cnt = 0
      rnd = length(clg.FB.ideals)
      rnd = max(rnd-10, 1):rnd
      while true
        if (E.cnt==0 && E.bad > lt) || (E.cnt != 0 && (bad_h ||
                          (E.bad+E.cnt)/E.cnt > lt))
          @v_do :ClassGroup 2 println("cnt ", E.cnt, " bad ", E.bad)
          @v_do :ClassGroup 2 println("re-starting for ideal ", i,
                          "\nrandomizing ", rnd, " and ", E.rr)
          if limit_cnt < 5
            rnd = max((rnd.start-10), 1):rnd.stop
            E.rr = 1:(2*E.rr.stop+1)
            E.vl = Int(Base.round(E.vl*1.2))
            @v_do :ClassGroup 3 println("random parameters now ", E.rr,
                            " and ", E.vl)
          end
          A = idl[i] * prod([idl[Base.rand(rnd)] for i= E.rr])
          I[i] = class_group_small_real_elements_relation_start(clg, A,
                          val = E.vl, limit = limit, prec = prec)
          I[i].rr = E.rr
          I[i].vl = E.vl
          E = I[i]
          @v_do :ClassGroup 3 println("confirm random parameters now ", E.rr,
                          " and ", E.vl)
          @v_do :ClassGroup 3 println("confirm random parameters now ",
                          I[i].rr, " and ", I[i].vl)
          limit_cnt += 1
        end
        b = class_group_small_real_elements_relation_next(E)
        if class_group_add_relation(clg, b*a)
          E.cnt += 1
          if length(clg.R) - clg.last_H > 20
            break
          end
          break
        else
          E.bad += 1
        end
      end
    end
    last_h = h
    l_piv = piv
    h, piv = class_group_current_result(clg)
    if h != 0
      piv = Set([Base.rand(div(clg.FB.size, 2):clg.FB.size) for i=1:1])
      @v_do :ClassGroup 1 println("full rank: current h = ", h,
                      " want ", want_extra, " more")
      if h == last_h 
        want_extra -= 1
      else
        want_extra = 15
      end
    end
    if length(l_piv) - length(piv) < length(l_piv)/2
      bad_h = true
    else
      bad_h = false
    end
    @v_do :ClassGroup_gc 1 gc()
  end

  @v_do :ClassGroup 1 println("used ", (time_ns()-s)/1e9, " total so far ",
                  clg.hnf_time/1e9, " sec for hnf in ", clg.hnf_call, " calls");
  @v_do :ClassGroup 1 println("added ", clg.rel_cnt, " good relations and ",
                  clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)
  return class_group_current_result(clg)
end

################################################################################
#
#  Conversion to Magma
#
################################################################################

function toMagma(f::IOStream, clg::ClassGrpCtx)
  print(f, "K<a> := NumberField(", nf(order(clg.FB.ideals[1])).pol, ");\n");
  print(f, "M := MaximalOrder(K);\n");
  print(f, "fb := [ ")
  for i=1:clg.FB.size
    print(f, "ideal<M| ", clg.FB.ideals[i].gen_one, ", ",
                    elem_in_nf(clg.FB.ideals[i].gen_two), ">")
    if i < clg.FB.size
      print(f, ",\n")
    end
  end
  print(f, "];\n")

  print(f, "R := [ ")
  for i = 1:length(clg.R)
    print(f, clg.R[i])
    if i < length(clg.R)
      print(f, ",\n")
    end
  end
  print(f, "];\n")

  toMagma(f, clg.M, name = "MM")
end

function toMagma(s::ASCIIString, c::ClassGrpCtx)
  f = open(s, "w")
  toMagma(f, c)
  close(f)
end

