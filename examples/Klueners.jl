function find_12t118(f, B) 
  g, s = galois_group(f)
  @assert transitive_group_identification(g) == (4, 3)
  k, a = number_field(f, cached = false)
  K, mkK = normal_closure(k)

  zk = maximal_order(k)
  #this should be the norm of the rel. disc for the S3 extension
  #S3 -> disc = A B^2 for A the conductor of the quadratic field and
  #             B and ideal in the same (small) field the conductor of the C3
  #N(A) = disc(ZK)/disc(zk)^4

  ZK = lll(maximal_order(K))
  nA = divexact(discriminant(ZK), discriminant(zk)^2)
  #disc(zk)^3 * nA * nB^2 <= B,
  nB = div(B, discriminant(zk)^3*nA)
#  if nB > 3*10^5
#    out = open("/tmp/JK-118", "a")
#    print(out, "incomplete $f, $nB too large\n")
#    close(out)
#  end
  nB = min(nB, 10^8)

  #in K: N(B) = nB^2 (deg 2 ext)
  #this bound for Carlo:
  #disc(ZK)^3*nB^2
  bnd = discriminant(ZK)^3*nB^2
  @show :bound, bnd
  c3 = Hecke.abelian_extensions(K, [3], discriminant(ZK)^3*nB^2)
  for A = c3
    if degree(normal_closure(A)) != 27
      continue
    end
    return A
    G, s = galois_group(A, QQ)
    if small_group_identification(G) == (216, 159)
      q = number_field(A)
      qa = absolute_simple_field(q)[1]
      qa = simplify(qa)[1]
      s = subfields(qa, degree = 12)
      out = open("/tmp/JK-118", "a")
      for x = s
        xx = simplify(x[1])[1]
        println(out, "$(defining_polynomial(xx)), $(discriminant(maximal_order(xx)))")
      end
      close(out)
      @show f, A
    else
      @show small_group_identification(G)
    end
  end
end


mutable struct Sqfr{T}
  data::Vector{T}
  val::Vector{ZZRingElem}
  d2v::Function
  B::ZZRingElem
  function Sqfr(d::Vector{T}, d2v::Function, B::ZZRingElem) where T
    val = map(d2v, d)
    p = sortperm(val)
    return new{T}(d[p], val[p], d2v, B)
  end
end

function Base.iterate(S::Sqfr)
  return S.data[1]^0, (Int[], ZZ(1))
end

function Base.iterate(S::Sqfr, t::Tuple{Vector{Int}, ZZRingElem})
  if length(t[1]) == 0
    if S.val[1] <= S.B
      return S.data[1], ([1], S.val[1])
    else
      return nothing
    end
  end
  st = t[1][end]+1
  B = t[2]
  if st <= length(S.data) && S.val[st] * B <= S.B
    p = t[1]
    push!(p, st)
    return prod(S.data[p]), (p, B*S.val[st])
  end
  p = t[1]
  while true
    st = pop!(p)+1
    B = divexact(B, S.val[st-1])
    if st <= length(S.data) && S.val[st] * B <= S.B
      push!(p, st)
      return prod(S.data[p]), (p, B*S.val[st])
    end
    if isempty(p)
      return nothing
    end
  end
end

Base.IteratorSize(::Sqfr) = Base.SizeUnknown()
Base.HasEltype(::Sqfr{T}) where T = T
Base.eltype(::Type{PrimeIdealsSet}) = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}

function Base.intersect(A::FinGenAbGroup, B::FinGenAbGroup...)
  for b = B
    A = intersect(A, b)
  end
  return A
end

function s3_extensions(k::AbsSimpleNumField, d::ZZRingElem, _T::Int = 0)
  zk = maximal_order(k)
  dk = abs(discriminant(zk))
  K, mkK = normal_closure(k)
  A, mA = automorphism_group(PermGroup, K)

  genk = mkK(gen(k))

  s = [a for a in A if !isone(a) && mA(a)(genk) == genk]
  @assert length(s) == 1
  ss = s[1]


  tau = rand(A)
  while sub(A, [ss, tau])[1] != A
    tau = rand(A)
  end

  ord4 = [g for g = A if order(g) == 4][1]

  X = character_table(A, 3)
  T = X[findfirst(x->!isone(x)  && x(ord4) == 1, X)]
  @show :target, T


  #this should be the norm of the rel. disc for the S3 extension
  #S3 -> disc = A B^2 for A the conductor of the quadratic field and
  #             B and ideal in the same (small) field the conductor of the C3
  #N(A) = disc(ZK)/disc(zk)^4

  ZK = lll(maximal_order(K))
  nA = divexact(discriminant(ZK), discriminant(zk)^2)
  #disc(zk)^3 * nA * nB^2 <= B,
  nB = div(d, discriminant(zk)^3*nA)

  kr = ray_class_field(relative_simple_extension(mkK)[1])
  kr = Hecke.rewrite_with_conductor(kr)

  @show :should_use, nB, log(nB)/log(10)
  nB = min(nB, ZZ(10^3))

  P = PrimeIdealsSet(zk, 1, iroot(nB, 2), coprimeto = 3)
  #if the norm of P is larger than sqrt(B) only one prime can be added..
  #hence does not occur in any combinatorics...
  #(thus saves memory as it is not stored)

  #possibly better strategy
  # while iterating over sqrt(B) ideals with norm <= B
  # store the ones with norm <= sqrt(B)
  # then once the loop over S is over, do the one over PI >= sqrt(B)
  # and supplement with the stored, sorted smaller ones.
  #
  # apart from s.th. soaking up memory, it works better this way
  cnt = 0
  pos = 0
  function fil(x)
    cnt += 1
    res = norm(x) <= nB && 
          (norm(x) % 3 == 1 ||
             norm(x)^prime_decomposition_type(kr, x)[2] % 3 == 1)
    pos += res
    if cnt % 100 == 0
      @show cnt, pos  #for fun to see s.th. moving
    end
    return res
  end
  P = Iterators.filter(fil, P)
  _P = collect(P)
  if length(_P) == 0
    push!(_P, 1*zk)
  end
  S = Sqfr(_P, norm, nB)

  l3 = prime_decomposition(zk, 3)

  wild = [1*zk]
  for (P, e) = l3
    b = floor(Int, 3//2*(1+e))
    wild = reduce(vcat, [[P^i * x for x = wild] for i=1:b])
  end
  sort!(wild, lt = (a,b) -> norm(a) <= norm(b))

  con_cnt = 0
  idl_cnt = 0

  function one_ideal(C)
    idl_cnt += 1
    fl = open("/tmp/last", "w")
    print(fl, "$C\n")
    close(fl)
    @show r = ray_class_field(minimum(C)*ZK, n_quo = 3)
    degree(r) == 1 && return
    if degree(r) > 1000
      @show :big
      return one_ideal_big(r, C)
    end
    R = gmodule(r, mA)
    @assert R.G == domain(mA) == AbstractAlgebra.Group(R)
    ac = action(R, ss)
    s = stable_subgroups(R.M, [ac], quotype = [3], op = (R, x) -> sub(R, x, false))
    for B = s
      CC = mapreduce(x->image(FinGenAbGroupHom(B[2]*action(R, x)), false)[2], (x,y) -> intersect(x, y, false)[2], domain(mA))
      if divexact(degree(r), order(domain(CC))) != 27
        @show degree(r), order(codomain(CC))
        continue
      end
      A = fixed_field(r, B[2])
      con_cnt += 1
      @show minimum(conductor(A)[1]), minimum(C)
      minimum(conductor(A)[1]) == minimum(C) || continue
      AA = fixed_field(r, CC)
#      @assert degree(normal_closure(A)) == 27 

      G, s = galois_group(AA, QQ)
      if small_group_identification(G) == (216, 159)
        q = number_field(A)
        qa = absolute_simple_field(q)[1]
        qa = simplify(qa)[1]
        s = subfields(qa, degree = 12)
        out = open("/tmp/JK-118-2", "a")
        x = s[1]
        xx = simplify(x[1])[1]
        @show defining_polynomial(xx), discriminant(maximal_order(xx))
        println(out, "$(defining_polynomial(xx)), $(discriminant(maximal_order(xx)))")
        close(out)
        @show k, A
      else
        @show small_group_identification(G)
      end
      @time Base.GC.gc()
    end
  end

  function one_ideal_big(r, C)
    idl_cnt += 1
    degree(r) == 1 && return
    R = gmodule(r, mA)
    @assert R.G == domain(mA) == AbstractAlgebra.Group(R)
    ac = action(R, ss)

    RR = gmodule(GF(3), R)
    @assert RR.G == R.G
    i = indecomposition(RR)
    i1 = [x for x = i if dim(x[1]) == 1]
    if length(i1) == 0
      return
    end
    i2 = [x for x = i if dim(x[1]) == 2]
    if length(i2) == 0
      return
    end

    ii = Dict{Vector{fpMatrix}, Vector{Int}}()
    target = nothing
    for x = 1:length(i1)
      v = map(mat, i1[x][1].ac)
      if !all(isone, v) && trace(action(i1[x][1], ord4).matrix) == 1
        if target === nothing
          target = v
        else
          @assert target == v
        end
      end

      if haskey(ii, v)
        push!(ii[v], x)
      else
        ii[v] = [x]
      end
    end
    if target === nothing
      return
    end

    m2, map2 = sub(R.M, reduce(vcat, [lift(mat(x[2])) for x = i2]), !false)
    sub_m2 = Hecke.stable_subgroups(m2, [FinGenAbGroupHom(map2*x*pseudo_inv(map2)) for x = R.ac], quotype = [3, 3], op = (R, x) -> sub(R, x, !false))
    m1 = []
    target_ind = 0
    for (k,v) = ii
      m, mp = sub(R.M, reduce(vcat, [lift(mat(i1[x][2])) for x = v]))
      push!(m1, mp)
      if target == k
        target_ind = length(m1)
      end
    end

    for i=1:length(m1)
      if i != target_ind
        continue
      end
      sub_m1 = subgroups(domain(m1[i]), quotype = [3])
      if length(m1) == 1
        rest = sub(R.M, [R.M[0]])
      else
        rest = sub(R.M, reduce(vcat, [matrix(m1[j]) for j=1:length(m1) if i != j]), !false)
      end
      for s = sub_m2
        rr = rest[1]+map2(s[2](s[1])[1])[1]
        for t = sub_m1
          A = rr + t[2](t[1])[1]
#          @assert all(x->Hecke.iseq((action(R, x)(A))[1], A), gens(R.G))
          @assert order(R.M)//order(A) == 27
          fl, mmA = issubgroup(A, R.M)
          @assert fl
          q, mq = quo(R.M, mmA)
          @assert order(q) == 27
          st = hom(q, q, [mq(action(R, ss, preimage(mq, a))) for a = gens(q)])
#          if all(x->st(x) == x, gens(q))
#            @show :wrong
#            continue
#          end
          stau = hom(q, q, [mq(action(R, tau, preimage(mq, a))) for a = gens(q)])
          @assert is_bijective(st)
          all_x = []
          for x = Hecke.stable_subgroups(q, [st], quotype = [3])
            qq, mqq = quo(q, x[1])
            if all(x->mqq(st(preimage(mqq, x))) == x, gens(qq))
              continue
            end
            ima = stau(x[1])[1]
            if Hecke.is_eq(ima, x[1])
              continue
            end
            ima = intersect(ima, x[1])
            while true
              s = order(ima)
              ima = intersect(ima, st(ima)[1])
              if order(ima) == 1
                break
              end
              ima = intersect(ima, stau(ima)[1]) 
              if order(ima) == 1 || order(ima) == s
                break
              end
            end
            if order(ima) != 1
              B = (A+preimage(mq, x[2](x[1])[1])[1])
#              @show  order(ima), degree(normal_closure(fixed_field(r, B)))
#              @assert degree(normal_closure(fixed_field(r, B))) == div(27, order(ima))
#              @show :too_small2, order(ima)
              continue
            end

            B = (A+preimage(mq, x[2](x[1])[1])[1])
            _A = fixed_field(r, B)
            @assert degree(_A) == 3

            con = conductor(_A)[1] 
            @show con_cnt += 1
            @show minimum(con), minimum(C)
            minimum(con) != minimum(C) && continue

            AA = fixed_field(r, A)
#            @assert AA == normal_closure(_A)
#            @assert is_normal(AA)
            @assert degree(AA) == 27

            G, s = galois_group(AA, QQ)
            if small_group_identification(G) == (216, 159)
              _q = number_field(_A)
              qa = absolute_simple_field(_q)[1]
              qa = simplify(qa)[1]
              s = subfields(qa, degree = 12)
              out = open("/tmp/JK-118-2", "a")
              x = s[1]
              xx = simplify(x[1])[1]
              @show defining_polynomial(xx), discriminant(maximal_order(xx))
              println(out, "$(defining_polynomial(xx)), $(discriminant(maximal_order(xx)))")
              close(out)
              @show k, A
            else
              @show small_group_identification(G)
            end
            @time Base.GC.gc()
          end #for x
        end #for t
      end #for s
    end #for i
  end #function



  if _T != 0
    return one_ideal(_T*ZK)
  end
  @show nB

  small_id = AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}[]

  Q = PrimeIdealsSet(zk, iroot(nB+1, 2), nB, coprimeto = 3)
  Q = Iterators.filter(fil, Q)

  id_cnt = 0

  for I = S 
    for J = wild
      id_cnt += 1
      nIJ = norm(I) * norm(J)
      if nIJ <= nB
        if nIJ <= iroot(nB, 2)
          push!(small_id, I*J)
        end
        @show norm(I) * norm(J), minimum(I*J)
        C = Hecke.induce_image(mkK, I*J, target = ZK)
        one_ideal(C)
      else
        break
      end
    end
    if id_cnt % 200 == 0
      @time Base.GC.gc()
    end
  end

  sort!(small_id, lt = (a,b) -> norm(a) <= norm(b))
  @show length(small_id)
  for q = Q
    for I = small_id
      id_cnt += 1
      if norm(q) * norm(I) <= nB
        @show norm(I) * norm(q)
        C = Hecke.induce_image(mkK, I*q, target = ZK)
        one_ideal(C)
      else
        break
      end
      if id_cnt % 200 == 0
        @time Base.GC.gc()
      end
    end
  end
  @show Base.summarysize(K)
end


function s3_extensions2(k::AbsSimpleNumField, d::ZZRingElem, _T::Int = 0)
  zk = maximal_order(k)
  dk = abs(discriminant(zk))
  K, mkK = normal_closure(k)
  A, mA = automorphism_group(PermGroup, K)

  genk = mkK(gen(k))

  s = [a for a in A if !isone(a) && mA(a)(genk) == genk]
  @assert length(s) == 1
  ss = s[1]
  tau = rand(A)
  while sub(A, [ss, tau])[1] != A
    tau = rand(A)
  end

  ord4 = [g for g = A if order(g) == 4][1]

  X = character_table(A, 3)
  T = X[findfirst(x->!isone(x)  && x(ord4) == 1, X)]
  @show :target, T

  #this should be the norm of the rel. disc for the S3 extension
  #S3 -> disc = A B^2 for A the conductor of the quadratic field and
  #             B and ideal in the same (small) field the conductor of the C3
  #N(A) = disc(ZK)/disc(zk)^4

  ZK = lll(maximal_order(K))
  nA = divexact(discriminant(ZK), discriminant(zk)^2)
  #disc(zk)^3 * nA * nB^2 <= B,
  nB = div(d, discriminant(zk)^3*nA)

  kr = ray_class_field(relative_simple_extension(mkK)[1])
  kr = Hecke.rewrite_with_conductor(kr)

  @show :should_use, nB, log(nB)/log(10)
  nB = min(nB, ZZ(10^3))

  P = PrimeIdealsSet(zk, 1, iroot(nB, 2), coprimeto = 3)
  #if the norm of P is larger than sqrt(B) only one prime can be added..
  #hence does not occur in any combinatorics...
  #(thus saves memory as it is not stored)

  #possibly better strategy
  # while iterating over sqrt(B) ideals with norm <= B
  # store the ones with norm <= sqrt(B)
  # then once the loop over S is over, do the one over PI >= sqrt(B)
  # and supplement with the stored, sorted smaller ones.
  #
  # apart from s.th. soaking up memory, it works better this way

  #next step: for the galois-cohomology we need galois-stable moduli
  #hence actually use the minimum.
  #thus for all the ideals above, we only need the minima...

  cnt = 0
  pos = 0
  function fil(x)
    cnt += 1
    res = norm(x) <= nB && 
          (norm(x) % 3 == 1 ||
             norm(x)^prime_decomposition_type(kr, x)[2] % 3 == 1)
    if res
      G = gmodule(A, units_mod_ideal(minimum(x)*ZK)[2], mA)
      G = gmodule(GF(3), G)
      i = indecomposition(G)
      res = any(x->dim(x[1]) == 2 || natural_character(x[1]) == T, i)
      if !res
        #TODO: suboptimal: we need ONLY ideals where there is a 
        #      either a deg 2 or a 'T' component in the module
      end
    end
    pos += res
    if cnt % 100 == 0
      @show cnt, pos  #for fun to see s.th. moving
    end
    return res
  end
  P = Iterators.filter(fil, P)
  _P = collect(P)
  if length(_P) == 0
    push!(_P, 1*zk)
  end
  __P = collect(Set(minimum(x) for x = _P))
  S = Sqfr(__P, x->x, nB)

  l3 = prime_decomposition(zk, 3)

  wild = [1*zk]
  for (P, e) = l3
    b = floor(Int, 3//2*(1+e))
    wild = reduce(vcat, [[P^i * x for x = wild] for i=1:b])
  end
  sort!(wild, lt = (a,b) -> norm(a) <= norm(b))
  _wild = sort(collect(Set(minimum(x) for x = wild)))

  con_cnt = 0
  idl_cnt = 0

  function one_ideal(C)
    @show :oneIdeal
    idl_cnt += 1
    fl = open("/tmp/last", "w")
    print(fl, "$C\n")
    close(fl)
    r = ray_class_field(C*ZK, n_quo = 3)
    degree(r) == 1 && return
    R = gmodule(r, mA)
    @assert R.G == domain(mA) == AbstractAlgebra.Group(R)
    ac = action(R, ss)


    RR = gmodule(GF(3), R)
    @assert RR.G == R.G
    i = indecomposition(RR)
    i1 = [x for x = i if dim(x[1]) == 1]
    if length(i1) == 0
      return
    end
    i2 = [x for x = i if dim(x[1]) == 2]
    if length(i2) == 0
      return
    end

    ii = Dict{Vector{fpMatrix}, Vector{Int}}()
    target = nothing
    for x = 1:length(i1)
      v = map(mat, i1[x][1].ac)
      if !all(isone, v) && trace(action(i1[x][1], ord4).matrix) == 1
        if target === nothing
          target = v
        else
          @assert target == v
        end
      end

      if haskey(ii, v)
        push!(ii[v], x)
      else
        ii[v] = [x]
      end
    end
    if target === nothing
      return
    end

    m2, map2 = sub(R.M, reduce(vcat, [lift(mat(x[2])) for x = i2]), !false)
    sub_m2 = Hecke.stable_subgroups(m2, [FinGenAbGroupHom(map2*x*pseudo_inv(map2)) for x = R.ac], quotype = [3, 3], op = (R, x) -> sub(R, x, !false))
    m1 = []
    target_ind = 0
    for (k,v) = ii
      m, mp = sub(R.M, reduce(vcat, [lift(mat(i1[x][2])) for x = v]))
      push!(m1, mp)
      if target == k
        target_ind = length(m1)
      end
    end

    for i=1:length(m1)
      if i != target_ind
        continue
      end
      sub_m1 = subgroups(domain(m1[i]), quotype = [3])
      if length(m1) == 1
        rest = sub(R.M, [R.M[0]])
      else
        rest = sub(R.M, reduce(vcat, [matrix(m1[j]) for j=1:length(m1) if i != j]), !false)
      end
      for s = sub_m2
        rr = rest[1]+map2(s[2](s[1])[1])[1]
        for t = sub_m1
          A = rr + t[2](t[1])[1]
#          @assert all(x->Hecke.iseq((action(R, x)(A))[1], A), gens(R.G))
          @assert order(R.M)//order(A) == 27
          fl, mmA = issubgroup(A, R.M)
          @assert fl
          q, mq = quo(R.M, mmA)
          @assert order(q) == 27
          st = hom(q, q, [mq(action(R, ss, preimage(mq, a))) for a = gens(q)])
#          if all(x->st(x) == x, gens(q))
#            @show :wrong
#            continue
#          end
          stau = hom(q, q, [mq(action(R, tau, preimage(mq, a))) for a = gens(q)])
          @assert is_bijective(st)
          all_x = []
          for x = Hecke.stable_subgroups(q, [st], quotype = [3])
            qq, mqq = quo(q, x[1])
            if all(x->mqq(st(preimage(mqq, x))) == x, gens(qq))
              continue
            end
            ima = stau(x[1])[1]
            if Hecke.is_eq(ima, x[1])
              continue
            end
            ima = intersect(ima, x[1])
            while true
              s = order(ima)
              ima = intersect(ima, st(ima)[1])
              if order(ima) == 1
                break
              end
              ima = intersect(ima, stau(ima)[1]) 
              if order(ima) == 1 || order(ima) == s
                break
              end
            end
            if order(ima) != 1
              B = (A+preimage(mq, x[2](x[1])[1])[1])
#              @show  order(ima), degree(normal_closure(fixed_field(r, B)))
#              @assert degree(normal_closure(fixed_field(r, B))) == div(27, order(ima))
#              @show :too_small2, order(ima)
              continue
            end

            B = (A+preimage(mq, x[2](x[1])[1])[1])
            _A = fixed_field(r, B)
            @assert degree(_A) == 3

            con = conductor(_A)[1] 
            @show con_cnt += 1
#            norm(con) <= nB || continue

            AA = fixed_field(r, A)
#            @assert AA == normal_closure(_A)
#            @assert is_normal(AA)
            @assert degree(AA) == 27

            G, s = galois_group(AA, QQ)
            global last_AA = (_A, ss)
            if small_group_identification(G) == (216, 159)
              _q = number_field(_A)
              sss = Hecke.new_extend_aut(_A, [mA(ss)])[1]
              beta = sss(_q[1]) + _q[1]
              f = minpoly(beta, QQ)
              if degree(f) != 12
                qa = absolute_simple_field(_q)[1]
                qa = simplify(qa)[1]
                s = subfields(qa, degree = 12)
                x = s[1]
              else
                x = number_field(f, cached = false)
              end
              out = open("/tmp/JK-118", "a")
              xx = simplify(x[1])[1]
              @show defining_polynomial(xx), discriminant(maximal_order(xx))
              println(out, "$(defining_polynomial(xx)), $(discriminant(maximal_order(xx)))")
              close(out)
              @show k, A
            else
              @show small_group_identification(G)
            end
            @time Base.GC.gc()
          end #for x
        end #for t
      end #for s
    end #for i
  end #function

  if _T != 0
    return one_ideal(ZZ(_T))
  end

  @show nB

  small_id = ZZRingElem[]

  Q = PrimesSet(max(ZZ(4), iroot(nB+1, 2)), nB)

  id_cnt = 0

  for I = S 
    for J = _wild
      id_cnt += 1
      nIJ = I*J
      if nIJ <= nB
        if nIJ <= iroot(nB, 2)
          push!(small_id, I*J)
        end
        @show I, J, I*J
        one_ideal(I*J)
      else
        break
      end
    end
    if id_cnt % 200 == 0
      @time Base.GC.gc()
    end
  end

  sort!(small_id)
  @show length(small_id)
  for q = Q
    for I = small_id
      id_cnt += 1
      if q * I <= nB
        one_ideal(q*I)
      else
        break
      end
      if id_cnt % 200 == 0
        @time Base.GC.gc()
      end
    end
  end
  @show Base.summarysize(K)
end



#=
function eval_par(S::Sqfr, F::Function, n::Int = 4, limit::Int = 10)
  chn = []
  res = Int[]
  for I = S
    limit -=1 
    if limit < 0
      return res, chn
    end
    while length(chn) >= n
      for i = 4:-1:1
        if istaskdone(chn[i][2])
          try 
            push!(res, fetch(chn[i][2]))
          catch e
            if !isa(e, TaskFailedException)
              rethrow(e)
            end
            @show chn[i][1]
          end
          deleteat!(chn, i)
          break
        end
      end
    end
    @show limit
    push!(chn, (I, Threads.@spawn F($I)))
  end
  return res, chn
end

=#
