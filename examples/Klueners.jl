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
Base.eltype(::Type{PrimeIdealsSet}) = NfOrdIdl

function Base.intersect(A::GrpAbFinGen, B::GrpAbFinGen...)
  for b = B
    A = intersect(A, b)
  end
  return A
end

function s3_extensions(k::AnticNumberField, d::ZZRingElem)
  zk = maximal_order(k)
  dk = abs(discriminant(zk))
  K, mkK = normal_closure(k)
  A, mA = automorphism_group(PermGroup, K)

  genk = mkK(gen(k))

  s = [a for a in A if !isone(a) && mA(a)(genk) == genk]
  @assert length(s) == 1
  ss = s[1]

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
  nB = min(nB, ZZ(10^5))

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
    push!(_P, 1*ZK)
  end
  S = Sqfr(_P, norm, nB)

  l3 = prime_decomposition(zk, 3)

  wild = [1*zk]
  for (P, e) = l3
    b = floor(Int, 3//2*(1+e))
    wild = vcat([[P^i * x for x = wild] for i=1:b]...)
  end
  sort!(wild, lt = (a,b) -> norm(a) <= norm(b))

  function one_ideal(C)
    r = ray_class_field(minimum(C)*ZK, n_quo = 3)
    degree(r) == 1 && return
    R = gmodule(r, mA)
    @assert R.G == domain(mA) == AbstractAlgebra.Group(R)
    ac = action(R, ss)
    s = stable_subgroups(R.M, [ac], quotype = [3], op = (R, x) -> sub(R, x, false))
    for B = s
      CC = mapreduce(x->image(GrpAbFinGenMap(B[2]*action(R, x)), false)[2], (x,y) -> intersect(x, y, false)[2], domain(mA))
      if divexact(degree(r), order(codomain(CC))) != 27
        continue
      end
      A = fixed_field(r, B[1])
      conductor(A)[1] == C || continue
      AA = fixed_field(r, CC)
#      @assert degree(normal_closure(A)) == 27 

      G, s = galois_group(AA, QQ)
      if small_group_identification(G) == (216, 159)
        q = number_field(A)
        qa = absolute_simple_field(q)[1]
        qa = simplify(qa)[1]
        s = subfields(qa, degree = 12)
        out = open("/tmp/JK-118", "a")
        x = s[1]
        xx = simplify(x[1])[1]
        @show defining_polynomial(xx), discriminant(maximal_order(xx))
        println(out, "$(defining_polynomial(xx)), $(discriminant(maximal_order(xx)))")
        close(out)
        @show k, A
      else
        @show small_group_identification(G)
      end
    end
  end

  @show nB

  small_id = NfOrdIdl[]

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
        @show :bingo
        C = Hecke.induce_image(mkK, I*J, target = ZK)
        one_ideal(C)
      else
        break
      end
    end
    if id_cnt % 150 == 0
 #     @time Base.GC.gc()
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
      if id_cnt % 150 == 0
#        @time Base.GC.gc()
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
