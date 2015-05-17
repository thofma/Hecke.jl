import Base: Array, isprime
export prime_ideals, factor

#=
TODO: 
  using/ implement limit in enum
  make sure the precisio for LLL is high enough (by checking that the resulting elements have a reasonable norm/ length? theory?)
  add reasonable verbose printing
  write hnf from upper_triangular
  clean-up
    sort the various data-types files
    write show functions
    remove debugging prints
    arrange the functions in e.g. Sparse in a reasonable order
      rename some of them
      export 
      use iterators in add_scaled and transform?
 understand/use profiling information (memory, ...)     

 Note: enumerating x,0,0,0 is pointless unless x==1
=#


################################################################################
#
# general prime decomposition, convert into "proper" Julia constructs
#
################################################################################
function my_prime_decomposition(O::PariMaximalOrder, p::Union(fmpz, Integer))
  p = ZZ(p)
  if  mod(ZZ(index(O)),p) == 0
    l = prime_decomposition(O, p)
    P = IdealSet(O)
    i = P(l[1])
    r = Array(typeof(i), lg(l.data)-1)
    r[1] = i
    for i = 2:lg(l.data)-1
      r[i] = P(l[i])
    end
    return r
  else
    r = prime_dec_nonindex(O, Int(p))
    return [x[1] for x=r]
  end
end

################################################################################
#
# all primes up to a given bound
#  complete controls if all primes over prime numbers <= B are taken
#  or
#  ideals of bounded norm
#
################################################################################
function prime_ideals(O::PariMaximalOrder, B::Int; complete = true, degree_limit = 5)
  p = 1
 
  r = []
  while p < B
    p = next_prime(p)
    if p > B
      return r
    end
    li = my_prime_decomposition(O, p)
    if !complete
      for P in li
        if norm(P) <= B && P.splitting_type[2] < degree_limit
          push!(r, P)
        end
      end
    else
      r = vcat(r, li)
    end
  end
  return r
end

################################################################################
#
# factorisation of ideals and elements
#  in general and over a factor bases
#
################################################################################

################################################################################
# gmp-factorisation into julia dictionaries
################################################################################
function my_factor(A::BigInt)
  D = Dict{BigInt, Int}()
  a = factor(A)
  for i = 1:a.len 
    D[a.d[i][1]] = a.d[i][2]
  end
  return D
end

function my_factor(A::fmpz)
  D = Dict{fmpz, Int}()
  a = factor(A)
  for i = 1:a.len 
    D[a.d[i][1]] = a.d[i][2]
  end
  return D
end

function factor(A::MaximalOrderIdeal)
  lf = my_factor(minimum(A) * A.den)
  lF = Dict{typeof(A), Int}()
  n = norm(A)
  O = A.parent.order
  for (i, (p, v)) in enumerate(lf)
    lP = my_prime_decomposition(O, p)
    for P in lP
      v = valuation(A, P)
      if v != 0
        lF[P] = v
        n = n//norm(P)^v
      end
      if A.den==1 && n==1 
        return lF
      end
    end
  end
  return lF
end

################################################################################
# a factor basis is mostly a collection of prime ideals
# designed, if possible, to allow for rapid testing if elements are smooth
#
################################################################################
type FactorBase
  fb::Dict{fmpz, Array{Tuple{Int, MaximalOrderIdeal}, 1}}
  size::Int
  fb_int::smooth_ctx
  ideals::Array{MaximalOrderIdeal, 1}
  rw::Array{Int, 1}
  mx::Int

  function FactorBase()
    r = new(Dict{fmpz, Array{Tuple{Int, MaximalOrderIdeal}, 1}}())
    r.size = 0
    return r
  end
end

function factor_base(O::PariMaximalOrder, B::Int; complete = true, degree_limit = 5)
  lp = prime_ideals(O, B, complete = complete, degree_limit = degree_limit)
  lp = sort(lp, lt = function(a,b) return norm(a) > norm(b); end)
  FB = FactorBase()
  FB.size = length(lp)
  FB.ideals = lp
  FB.rw = Array(Int, 20)
  FB.mx = 20

  for i = 1:length(lp)
    if !haskey(FB.fb, lp[i].gen_one)
      FB.fb[lp[i].gen_one] = [(i, lp[i])]
    else
      push!(FB.fb[lp[i].gen_one], (i, lp[i]))
    end
  end

  FB.fb_int = is_smooth_init(Set(keys(FB.fb)))

  return FB
end

################################################################################
# factor element over factor base. put valuations into row i of the
#  relation matrix M
#  M needs to have at least as many columns as the FB has ideals
################################################################################

function factor!(M::fmpz_mat, i::Int, FB::FactorBase, a::nf_elem; error = true, n = abs(norm(a)))
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
    assert(n==1)
  else
    if n!=1
      for j in cor
        M[i,j] = 0
      end
    end
    return n==1
  end
  return true
end

function factor!{T}(M::Smat{T}, i::Int, FB::FactorBase, a::nf_elem; error = true, n = abs(norm(a)))
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
          rw[lg+1] = v
        else
          push!(rw, j)
          push!(rw, v)
        end
        lg += 1
      end
    end
    if vp != 0
      if error
        assert(vp==0)
      end
      return false
    end
  end
  if lg >0
    if length(rw) > FB.mx
      FB.mx = length(rw)
    end
    @assert lg > 1
    @assert iseven(lg)
    nrw = Array{Tuple{Int, Int}}(div(lg, 2))
    for i=1:div(lg, 2)
      nrw[i] = (rw[2*(i-1)+1], rw[2*i])
    end
    sort!(nrw, lt=function(a,b) return a[1]<b[1]; end)
    @assert length(nrw) > 0
    push!(M, SmatRow{T}(nrw))
    return true
  else 
    # factor failed or I have a unit.
    # sparse rel mat must not have zero-rows.
    return false
  end
end

function factor(FB::FactorBase, a::nf_elem)
  M = MatrixSpace(ZZ, 1, FB.size)()
  factor!(M, 1, FB, a)
  return M
end
################################################################################
################################################################################
#
#
# basic lattice enumeration code
# 
#
################################################################################
################################################################################
#(sh/c)ould be indexed by the type of G and C
#in fact, since G is not used after the creation, maybe we should drop it...
#realisticly, x (hence L, U) can be small types mostly
#missing: support for lower bound
#         reference vector
#         support for all points
#           if all points are wanted, the spiraling out, enumerating
#           coordinates from the center outwards is counter-productive
#lower bounds should be non-trivial speed-up by effectively generating the L, U for
#the other bound as well and using this for exclusion.
# see other comment below
#
# now that x is a fmpz_mat, the type for x is not really used
type enum_ctx{Tx, TC, TU}
  G::fmpz_mat
  n::Int
  limit :: Int # stop recursion at level limit, defaults to n
  d::Union(Integer, fmpz) #we actually want G/d
  C::Array{TC, 2} # the pseudo-cholesky form - we don't have fmpq_mat
  last_non_zero::Int
  x::fmpz_mat # 1 x n
  U::Array{TU, 1}
  L::Array{TU, 1}
  l::Array{TU, 1}
  tail::Array{TU, 1}
  c::fmpz # the length of the elements we want
  t::fmpz_mat # if set, a transformation to be applied to all elements
  t_den::fmpz
  function enum_ctx()
    return new()
  end
end

function show(io::IO, E::enum_ctx)
  println(io, "EnumCtx")
  println(io, "curr. length ", E.c, " elt ", E.x, "(", (typeof(E.x), typeof(E.C), typeof(E.U)), ")")
end

#need to only compute the top l x l submatrix when using limited enum
function pseudo_cholesky(G::fmpz_mat, den=1; 
                 TC::Type=Rational{BigInt}, limit = rows(G))
  n = cols(G)
  assert(rows(G) == n)

  limit = min(limit, n)

  t = ZZ()

  C = Array(TC,limit,limit)
  for i=1:limit
    for j=1:limit
      C[i,j] = TC(getindex!(t, G, i,j))/TC(den)
    end
  end

  for i = 1:limit-1 
    for j = i+1:limit
      C[j,i] = C[i,j]
      C[i,j] = C[i,j]/C[i,i]
    end
    for k = i+1:limit
      for l = i+1:limit
        C[k,l] = C[k,l] - C[k,i]*C[i,l]
      end
    end
  end
  for j = 1:limit-1
    @assert C[j,j] >0
    for i=j+1:limit
      C[i,j] = 0
    end
  end
  @assert C[limit,limit] >0
  return C
end

function enum_ctx_from_basis(B::fmpz_mat, den::fmpz = ZZ(1); Tx::Type = BigInt, TC::Type = Rational{BigInt}, TU::Type = Rational{BigInt}, limit = rows(B))
  G = gram(B)
  return enum_ctx_from_gram(G, den*den, Tx=Tx, TC=TC, TU=TU, limit = limit)
end

function enum_ctx_from_gram(G::fmpz_mat, den = 1; Tx = BigInt, TC = Rational{BigInt}, TU = Rational{BigInt}, limit = rows(G))
  E = enum_ctx{Tx, TC, TU}()
  E.G = G
  n = E.n =rows(G) 
  E.limit = limit = min(limit, n)
  E.d = den
  E.C = pseudo_cholesky(E.G, den, TC = TC, limit = limit)
  E.x = MatrixSpace(ZZ, 1, n)()
    #coeffs limit+1:n are going to be zero, always
  E.L = Array(TU, limit) #lower and
  E.U = Array(TU, limit) #upper bounds for the coordinates

  E.l = Array(TU, limit) #current length
  E.tail = Array(TU, limit)
  return E
end

function enum_ctx_local_bound{T}(a::Rational{T}, b::Rational{T})
  #return L <= U sth.
  #L = ceil(a-sqrt(b)), U = floor(a+sqrt(b))
  #solves (gives bounds) for (a-x)^2 <= b
  @assert b>=0
  d = den(b)
  i = isqrt(num(b*d*d))
  L = Base.ceil(a-i//d)
  U = Base.floor(a+i//d)
  if (a-L)^2 >b 
    L +=1
  end
  if (a-U)^2>b
    U -= 1
  end

#println("local bound for ", a, " and ", b)
#println("is ", L, " and ", U)
  return L, U
end

function enum_ctx_local_bound{Number}(a::Number, b::Number)
  #return L <= U sth.
  #L = ceil(a-sqrt(b)), U = floor(a+sqrt(b))
  #solves (gives bounds) for (a-x)^2 <= b
  @assert b>=0
  i = sqrt(b)
  L = Base.ceil(a-i)
  U = Base.floor(a+i)
#println("local bound for ", a, " and ", b)
#println("is ", L, " and ", U)
  return L, U
end


function enum_ctx_start{A,B,C}(E::enum_ctx{A,B,C}, c::fmpz)
  E.c = c
  zero!(E.x)
  for i=1:E.limit
    E.l[i] = C(E.c)/C(E.d)
    E.tail[i] = 0
    L, U = enum_ctx_local_bound(C(0), C(B(E.c//E.d)/E.C[i,i]))
    @assert typeof(L) == C
    @assert typeof(U) == C
    @assert typeof(E.L) == Array{C, 1}
    E.U[i] = U
    E.L[i] = L
  end
  E.U[1] = min(E.U[1], 1)
  E.L[1] = -E.U[1]
  E.last_non_zero = 1
end

#for pol-red-abs we need s.th. else I think
#
#
#missing: lower bound
#         reference vector (eventually)
#         length
#         proper lattice type


function enum_ctx_advance_level{A,B,C}(E::enum_ctx{A,B,C}, i::Int)
#  println("i: ", i, "                                   "[1:2*i], "|")
  t = ZZ()
  if i == E.last_non_zero-1
    E.x[1, i] = getindex!(t, E.x, 1, i) + 1
  elseif i == E.last_non_zero
#    @assert E.x[1, i] == 0
    E.last_non_zero += 1
    E.x[1, i] = getindex!(t, E.x, 1, i) + 1
  else
    s = E.U[i] + E.L[i]
    x = A(getindex!(t, E.x, 1, i))
    if s < 2*x  # larger than the middle
      E.x[1, i] = -x + A(Base.floor(s))
    else
      E.x[1, i] = -x + A(Base.floor(s))+1
    end
  end
end

function enum_ctx_next{A,B,C}(E::enum_ctx{A,B,C})
  n::Int = 1
  n = E.limit
  i=1
  t = ZZ()
  while true 
    enum_ctx_advance_level(E, i)
    t = getindex!(t, E.x, 1, i)
    if E.L[i] <= C(t) <= E.U[i] #coordinate is valid
      if i==1
        return true
      else
        i -= 1
      end
    else # coordinate is invalid
      i += 1
      if i>n
        return false
      end
      continue
    end

    @assert i<n
    while true
      t1 = A(getindex!(t, E.x, 1, i+1))
      E.tail[i] = E.C[i, i+1]*t1
      for j = i+2:n
        E.tail[i] += E.C[i, j] * A(getindex!(t, E.x, 1, j))
      end
      E.l[i]    = E.l[i+1] - E.C[i+1, i+1]*(t1 + E.tail[i+1])^2
      
      if E.l[i] >= 0
        Z = C(B(E.l[i])/E.C[i,i])
        @assert E.l[i] >= 0
        @assert E.C[i,i] > 0
        @assert Z >= 0
        L, U = enum_ctx_local_bound(-E.tail[i], Z)
        @assert typeof(L) == C
        E.L[i] = L
        E.U[i] = U
        
        x = A(Base.ceil((E.L[i] +E.U[i])/2))
        E.x[1, i] = x
        if -E.L[i] == E.U[i] && E.last_non_zero == i+1
          E.last_non_zero = i
          @assert x == 0 
        end
        if x <= E.U[i] # coordinate is valid`
          i -= 1            # go further up
          if i==0
            return true
          end
          continue
        else  # coordinate invalid, need to truy next on i+1
          i += 1
          if i>n
            return false
          end
          break
        end
      else # intervall too short
        i += 1
        if i>n
          return false
        end
        break
      end
    end
  end
  return true
end

function enum_ctx_short_elements{A,B,C}(E::enum_ctx{A,B,C}, c::fmpz, limit=-1)
  enum_ctx_start(E, c)
  if enum_ctx_next(E)
    l = transpose(E.x)
  end
  while enum_ctx_next{A,B,C}(E) && (limit == -1 || limit >= Base.size(l, 1))
    l = vcat(l, transpose(E.x))
  end
  return l
end

################################################################################
#
# relations based on ideals
#
################################################################################
type ideal_relations_ctx
  A::MaximalOrderIdeal
  v::Array{Int, 1}  # the infinite valuation will be exp(v[i])
  E::enum_ctx
  c::fmpz # the last length
  cnt::Int
  bad::Int
  M :: fmpz_mat
  vl::Int
  rr::Range{Int}

  function ideal_relations_ctx()
    return new()
  end
end
function show(io::IO, I::ideal_relations_ctx)
  println(io, "IdealRelationCtx for ", I.A)
  println(io, "  current length bound ", I.c, " stats: ", I.cnt, " and ", I.bad)
end


################################################################################
#
#
# The main class group part
#   starting with the class group data structure
#
#
################################################################################
type ClassGrpCtx{T}
  FB::FactorBase

  M::Union(fmpz_mat, Smat{T}) 
               # the relation matrix, columns index by the factor basis
               # rows by the relations
  R::Array{nf_elem, 1} # the relations
  RS::Set{nf_elem}

  H::Union(fmpz_mat, Smat{T}) # the last hnf, at least the non-trivial part of it
  last_H::Int      # the number of rows of M that went into H
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

  val_base::fmpz_mat # a basis for the possible infinite ranodmization 
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

function class_group_init(O::PariMaximalOrder, B::Int; complete = true, degree_limit = 5)
  clg = ClassGrpCtx{BigInt}()

  clg.bad_rel = 0
  clg.rel_cnt = 0
  clg.last = 0
  clg.sum_norm = 0

  clg.FB = factor_base(O, B, complete = complete, degree_limit = degree_limit)
  clg.M = Smat{BigInt}()
  clg.c = conjugates_init(O.pari_nf.nf.pol)
  for I in clg.FB.ideals
    class_group_add_relation(clg, O.pari_nf.nf(I.gen_one))
    class_group_add_relation(clg, O.pari_nf.nf(I.gen_two))
  end
  n = degree(O)
  l = MatrixSpace(ZZ, n, 1+clg.c.r2)()
  for i=1:n
    l[i,1] = 1
  end
  for i=1:clg.c.r2
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

function class_group_add_relation(clg::ClassGrpCtx, a::nf_elem)
  if a==0
    return false
  end
  if a in clg.RS 
    return false
  end
  n = abs(norm(a))
  clg.sum_norm += num(n*n)
#  print("trying relation of length ", Float64(length(clg.c, a)),  " and norm ", Float64(n));
  if !is_smooth(clg.FB.fb_int, num(n)*denominator(a))
    clg.bad_rel += 1
#    println(" -> fail")
    return false
  end
  if factor!(clg.M, length(clg.R)+1, clg.FB, a, error=false, n = n)
    push!(clg.R, a)
    push!(clg.RS, a)
    @assert rows(clg.M) == length(clg.R)
    clg.rel_cnt += 1
    println(" -> OK, rate currently ", clg.bad_rel/clg.rel_cnt, " this ", clg.bad_rel - clg.last, ", avg (norm^2) ", Float64(BigInt(clg.sum_norm)/(clg.bad_rel-clg.last+1)))
    clg.last = clg.bad_rel
    clg.sum_norm = 0
    return true
  else
#    println(" -> 2:fail")
    clg.bad_rel += 1
    return false
  end
end
################################################################################
# Naive relation search: based on coeff size only
################################################################################
function class_group_random_ideal_relation(clg::ClassGrpCtx, r::Int, I = Base.rand(clg.FB.ideals))
  s = 1
  if r<2
    r = 2
  end
  for i=1:r 
    I = prod(I, Base.rand(clg.FB.ideals))
    I, g = reduce_ideal_class(I)
    s *= g
  end
  return s;
end 

################################################################################
# Naive relation search: tries random lin. comb of lll reduced basis
#         lll is done on the coeff. lattice.   
################################################################################
function class_group_small_elements_relation(clg::ClassGrpCtx, A::MaximalOrderIdeal, cnt = degree(A.parent.order))
  b = basis_mat(A)
  l = lll(b[1])
  K = A.parent.order.pari_nf.nf
  if cnt <= degree(A.parent.order)
    lb = Array(typeof(K()), degree(K))
    for i = 1:cnt
      lb[i] = element_from_mat_row(K, l, i)//b[2]
    end
    return lb
  end
  r = Int(Base.ceil((2*cnt)^(1/degree(K))))
  r = -div(r+1, 2):div(r+1, 2)
  

  ll = Array(typeof(K()), degree(K))
  for i = 1:degree(K)
    ll[i] = element_from_mat_row(K, l, i)//b[2]
  end

  lb = Array(typeof(K()), cnt)
  for i = 1:cnt
    lb[i] = rand(ll, r)
  end

  return lb
end
################################################################################
#
# more interesting search: enumeration and other things on the minkowski side
#
################################################################################
function lll(c::roots_ctx, A::MaximalOrderIdeal, v::fmpz_mat; prec::Int64 = 100, limit::Int64=0)
  c = minkowski_mat(c, A.parent.order.pari_nf.nf, prec)
  if !iszero(v)
    println("using inf val", v)
    old = get_bigfloat_precision()
    set_bigfloat_precision(4*prec)
    e = convert(typeof(c[1,1]), exp(1))
    sc = diagm([e^Int(v[1, i]) for i=1:cols(v)])
    c = c*sc
    set_bigfloat_precision(old)
  end
  b = basis_mat(A)
  c = b[1]*c
  old = get_bigfloat_precision()
  set_bigfloat_precision(prec)
  g = round(scale(c, BigInt(2)^(prec)))
  @assert !iszero(g)
  set_bigfloat_precision(old)
  g = g*g'
  n = rows(g)
  for i=1:n
    for j=1:n
      g[i,j] = div(g[i,j], ZZ(2)^prec)
    end
  end
  g += n*one(parent(g))

  l, t = lll_gram_with_transform(g)
  return l, t
end

function one_step(c::roots_ctx, b::MaximalOrderFracIdeal, p::MaximalOrderIdeal; prec::Int64 = 100)
  b = p*b
  simplify(b)
  g1 = short_elem(c, b, prec = prec)
  b = g1*inv(b) 
  simplify(b)
  g2 = short_elem(c, b, prec = prec) 
  return simplify(g2*inv(b)), g1, g2
end

function short_elem(c::roots_ctx, A::MaximalOrderFracIdeal, v::fmpz_mat=MatrixSpace(ZZ, 1,1)(); prec::Int64 = 100)
  return divexact(short_elem(c, A.I, v, prec = prec), A.den)
end

function short_elem(c::roots_ctx, A::MaximalOrderIdeal, v::fmpz_mat=MatrixSpace(ZZ, 1,1)(); prec::Int64 = 100)
  K = A.parent.order.pari_nf.nf
  b, b_den = basis_mat(A)
  l, t = lll(c, A, v, prec = prec)
  w = window(t, 1,1, 1, cols(t))
  c = w*b
  q = element_from_mat_row(K, c, 1)
  q = divexact(q, b_den)
  return q
end

function enum_ctx_from_ideal(clg::ClassGrpCtx, A::MaximalOrderIdeal, v::fmpz_mat;prec::Int64 = 100, limit::Int64 = 0)
  l, t = lll(clg.c, A, v, prec = prec, limit = limit)
  b, b_den = basis_mat(A)

  K = A.parent.order.pari_nf.nf

  if limit == 0
    limit = rows(l)
  end
#  E = enum_ctx_from_gram(l, ZZ(2)^prec, Tx = BigInt, TC = Rational{BigInt}, TC = Rational{BigInt}, limit = limit)
  E = enum_ctx_from_gram(l, ZZ(2)^prec, Tx = Int, TC = Float64, TU = Float64, limit = limit)
  E.t = t*b
  E.t_den = b_den
  n = E.n
  b = E.G[n,n]
  enum_ctx_start(E, b)
  return E
end

function class_group_ideal_ctx(clg::ClassGrpCtx, A::MaximalOrderIdeal; prec::Int64 = 100, val::Int64=0, limit::Int64 = 0)
  I = ideal_relations_ctx()
  I.A = A
  v = MatrixSpace(ZZ, 1, rows(clg.val_base))(Base.rand(-val:val, 1, rows(clg.val_base)))*clg.val_base
  I.E = enum_ctx_from_ideal(clg, A, v, prec = prec, limit = limit)
  I.c = 0
  I.cnt = 0
  I.bad = 0
  I.vl = 0
  I.rr = 1:0
  I.M = MatrixSpace(ZZ, 1, I.E.n)()
  return I
end

function class_group_small_real_elements_relation_start(clg::ClassGrpCtx, A::MaximalOrderIdeal; prec::Int64 = 200, val::Int64 = 0, limit::Int64 = 0)
  I = class_group_ideal_ctx(clg, A, prec = prec, val = val, limit = limit)
  return I
end

function class_group_small_real_elements_relation_next(I::ideal_relations_ctx)

  K = I.A.parent.order.pari_nf.nf
  while true
    if enum_ctx_next(I.E)
#      println("elt is", I.E.x)
      if !content_is_one(I.E.x) 
        continue
      end
       I.M = I.E.x * I.E.t
      q = element_from_mat_row(K, I.M, 1)
      q = divexact(q,I.E.t_den)
#      println("found ", q, " of length ", length(q), " and norm ", norm(q))
      return q
    end
    println("restart for ", I.A, I.E.c)
    enum_ctx_start(I.E, I.E.c*2)
  end
end

function is_zero_row(M::fmpz_mat, i::Int)
  for j = 1:cols(M)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function is_zero_row{T <: Integer}(M::Array{T, 2}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

function is_zero_row(M::Array{fmpz, 2}, i::Int)
  for j = 1:Base.size(M, 2)
    if M[i,j] != 0 
      return false
    end
  end
  return true
end

#do better: re-use partial hnf, check rank mod p, ...

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
      println("pruning again...")
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

  println("rank is currently ", rows(h), " need to be ", cols(h), clg.M)
  
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
    clg.h = 0
    return 0, mis
  end

  if full_rank
    clg.h = abs(prod([h[i,i] for i=1:cols(h)]))
  else
    println("1st non-modular")
    toMagma("/tmp/big.m", clg.M)
    h = copy(clg.M)
    @time upper_triangular(h)
    clg.H = h
    clg.h = abs(prod([h[i,i] for i=1:cols(h)]))
  end

  clg.mis = Set(1:0)
  return clg.h, clg.mis
end
################################################################################
# main loop to find relations
################################################################################
function class_group_find_relations(clg::ClassGrpCtx; val = 0, prec = 100, limit = 10)
  clg.hnf_time = 0.0
  clg.hnf_call = 0
  clg.rel_cnt = 0
  clg.bad_rel = 0

  n = degree(clg.FB.ideals[1].parent.order)
  t = time_ns()
  I = []
  for i in clg.FB.ideals
    f = class_group_small_real_elements_relation_start(clg, i, limit = limit, prec = prec)
    push!(I, f)
    f.vl = val
    while true
      f = class_group_add_relation(clg, class_group_small_real_elements_relation_next(I[end]))
      if f
        I[end].cnt += 1
        break
      else
        I[end].bad += 1
        if I[end].bad > (clg.bad_rel/clg.rel_cnt)*2
          println("too slow in getting s.th. for ", i, "good: ", I[end].cnt,  " bad: ",  I[end].bad, " ratio: ", (clg.bad_rel/clg.rel_cnt))
          break
        end
      end
    end
    gc()
  end

  println("used ", (time_ns()-t)/1e9, " sec for small elts, so far ", clg.hnf_time/1e9, " sec for hnf in ", clg.hnf_call, " calls");
  println("added ", clg.rel_cnt, " good relations and ", clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)

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
        if (E.cnt==0 && E.bad > lt) || (E.cnt != 0 && (bad_h ||(E.bad+E.cnt)/E.cnt > lt))
          println("cnt ", E.cnt, " bad ", E.bad)
          println("re-starting for ideal ", i, "randomizing ", rnd, " and ", E.rr)
          if limit_cnt < 5
            rnd = max((rnd.start-10), 1):rnd.stop
            E.rr = 1:(2*E.rr.stop+1)
            E.vl = Int(Base.round(E.vl*1.2))
            println("random parameters now ", E.rr, " and ", E.vl)
          end
          A = idl[i] * prod([idl[Base.rand(rnd)] for i= E.rr])
          I[i] = class_group_small_real_elements_relation_start(clg, A, val = E.vl, limit = limit, prec = prec)
          I[i].rr = E.rr
          I[i].vl = E.vl
          E = I[i]
          println("confirm random parameters now ", E.rr, " and ", E.vl)
          println("confirm random parameters now ", I[i].rr, " and ", I[i].vl)
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
      println("full rank: current h = ", h, " want ", want_extra, " more")
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
    gc()
  end


  println("used ", (time_ns()-s)/1e9, " total so far ", clg.hnf_time/1e9, " sec for hnf in ", clg.hnf_call, " calls");
  println("added ", clg.rel_cnt, " good relations and ", clg.bad_rel, " bad ones, ratio ", clg.bad_rel/clg.rel_cnt)
  return class_group_current_result(clg)
end
################################################################################
################################################################################
#
# other stuff:
#  fmpz_mat -> Array(BigInt, 2)
#
################################################################################
################################################################################
function Array(a::fmpz_mat)
  A = Array(BigInt, rows(a), cols(a))
  for i = 1:rows(a)
    for j = 1:cols(a)
      A[i,j] = a[i,j]
    end 
  end
  return A
end


################################################################################
#
# other stuff:
#  export various types to a Magma or Nemo readable file
#
################################################################################
# fmpz_mat -> nemo file
# use as include(...)
################################################################################
function toNemo(io::IOStream, A::fmpz_mat; name = "A")
  println(io, name, " = MatrixSpace(ZZ, ", rows(A), ", ", cols(A), ")([")
  for i = 1:rows(A)
    for j = 1:cols(A)
      print(io, A[i,j])
      if j < cols(A)
        print(io, " ")
      end
    end
    if i<rows(A)
      println(io, ";")
    end
  end
  println(io, "]);")
  println(io, "println(\"Loaded ", name, "\")")
end

function toNemo(s::ASCIIString, A::fmpz_mat)
  f = open(s, "w")
  toNemo(f, A)
  close(f)
end

################################################################################
# fmpz_mat -> magma file
# use as read(...)
################################################################################
function toMagma(io::IOStream, A::fmpz_mat; name = "A")
  println(io, name, " := Matrix(Integers(), ", rows(A), ", ", cols(A), ", [")
  for i = 1:rows(A)
    for j = 1:cols(A)
      print(io, A[i,j])
      if j < cols(A)
        print(io, ", ")
      end
    end
    if i<rows(A)
      println(io, ",")
    end
  end
  println(io, "]);")
  println(io, "\"Loaded ", name, "\";")
end

function toMagma(s::ASCIIString, A::fmpz_mat)
  f = open(s, "w")
  toMagma(f, A)
  close(f)
end

################################################################################
# Smat -> magma file
# use as read(...)
################################################################################
function toMagma(io::IOStream, A::Smat; name = "A")
  println(io, name, " := SparseMatrix(Integers(), ", rows(A), ", ", cols(A), ", [")
  for i = 1:rows(A)
    for xx = 1:length(A.rows[i].entry) 
      x = A.rows[i].entry[xx]
      print(io, "<", i, ", ", x.col, ", ", x.val, ">")
      if xx < length(A.rows[i].entry) || i<rows(A)
        print(io, ", ")
      end
    end
    println(io, "")
  end
  println(io, "]);")
  println(io, "\"Loaded ", name, "\";")
end

function toMagma(s::ASCIIString, A::Smat)
  f = open(s, "w")
  toMagma(f, A)
  close(f)
end

################################################################################
#export factor base, relations and rel mat to Magma
################################################################################

function toMagma(f::IOStream, clg::ClassGrpCtx)
  print(f, "K<a> := NumberField(", clg.FB.ideals[1].parent.order.pari_nf.nf.pol, ");\n");
  print(f, "M := MaximalOrder(K);\n");
  print(f, "fb := [ ")
  for i=1:clg.FB.size
    print(f, "ideal<M| ", clg.FB.ideals[i].gen_one, ", ", clg.FB.ideals[i].gen_two, ">")
    if i<clg.FB.size
      print(f, ",\n")
    end
  end
  print(f, "];\n")

  print(f, "R := [ ")
  for i=1:length(clg.R)
    print(f, clg.R[i])
    if i<length(clg.R)
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


