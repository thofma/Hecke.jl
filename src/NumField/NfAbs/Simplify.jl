export simplify

add_verbose_scope(:Simplify)

@doc Markdown.doc"""
    simplify(K::AnticNumberField; canonical::Bool = false) -> AnticNumberField, NfToNfMor

Tries to find an isomorphic field $L$ given by a "simpler" defining polynomial.
By default, "simple" is defined to be of smaller index, testing is done only
using a LLL-basis of the maximal order.

If `canonical` is set to `true`, then a canonical defining polynomial is found,
where canonical is using the definition of PARI's `polredabs`, which is described in
http://beta.lmfdb.org/knowledge/show/nf.polredabs.

Both version require a LLL reduced basis for the maximal order.
"""
function simplify(K::AnticNumberField; canonical::Bool = false, cached = true)
  Qx, x = PolynomialRing(FlintQQ, "x")
  
  if degree(K) == 1
    L = number_field(x - 1, cached = cached, check = false)[1]
    return L, hom(L, K, gen(K), check = false)
  end
  if canonical
    a, f1 = polredabs(K)
    f = Qx(f1)
  else
    n = degree(K)
    OK = maximal_order(K)
    if isdefined(OK, :lllO)
      ZK = OK.lllO
    else
      b = _simplify(OK)
      if b != gen(K)
        f1 = Qx(minpoly(representation_matrix(OK(b))))
        L1 = NumberField(f1, cached = cached, check = false)[1]
        #Before calling again the simplify on L1, we need to define the maximal order of L1
        mp = hom(L1, K, b, check = false)
        _compute_preimg(mp)
        B = basis(OK, K)
        BOL1 = Vector{nf_elem}(undef, degree(L1))
        for i = 1:degree(L1)
          BOL1[i] = mp\(B[i])
        end
        OL1 = NfOrd(BOL1, false)
        OL1.ismaximal = 1
        Hecke._set_maximal_order(L1, OL1)
        @vprint :Simplify 3 "Trying to simplify $(L1.pol)\n"
        L2, mL2 = simplify(L1)
        return L2, mL2*mp
      end
      prec = 100 + 25*div(n, 3) + Int(round(log(abs(discriminant(OK)))))
      OK1 = _ordering_by_T2(OK)
      @vtime :Simplify 3 ZK = _lll_for_simplify(OK1, prec = prec)
      OK.lllO = ZK
    end
    @vtime :Simplify 3 a = _simplify(ZK)
    if a == gen(K)
      f = K.pol
    else
      @vtime :Simplify 3 f = Qx(minpoly(representation_matrix(OK(a))))
    end
  end
  L = NumberField(f, cached = cached, check = false)[1]
  m = hom(L, K, a, check = false)
  return L, m
end

function _simplify(O::NfOrd)
  K = nf(O)
  Qx, x = PolynomialRing(FlintQQ)
  Zx = PolynomialRing(FlintZZ, "x", cached = false)[1]
  f = Zx(K.pol*denominator(K.pol))
  
  a = O(gen(K)*denominator(K.pol), false)
  p, d = _find_prime(f)

  B = basis(O, copy = false)
  nrep = min(3, degree(K))
  Bnew = NfOrdElem[]
  for i = 1:length(B)
    push!(Bnew, B[i])
    for j = 1:nrep
      push!(Bnew, B[i]+B[j])
      push!(Bnew, B[i]-B[j])
    end
  end
  #First, we search for elements that are primitive using block systems
  F = FlintFiniteField(p, d, "w", cached = false)[1]
  Ft = PolynomialRing(F, "t", cached = false)[1]
  ap = zero(Ft)
  fit!(ap, degree(K)+1)
  rt = roots(f, F)
  
  n = degree(K)
  indices = Int[]
  for i = 1:length(Bnew)
    if isone(denominator(Bnew[i].elem_in_nf))
      continue
    end 
    b = _block(Bnew[i].elem_in_nf, rt, ap)
    if length(b) == n
      push!(indices, i)
    end
  end
  #Now, we select the one of smallest T2 norm
  I = t2(a)    
  for i = 1:length(indices)
    t2n = t2(Bnew[indices[i]].elem_in_nf)
    if t2n < I
      a = Bnew[indices[i]]
      I = t2n
    end
  end
  return a.elem_in_nf
end


 #a block is a partition of 1:n
 #given by the subfield of parent(a) defined by a
 #the embeddings used are in R
 #K = parent(a)
 # then K has embeddings into the finite field (parent of R[1])
 # given by the roots (in R) of the minpoly of K
 #integers in 1:n are in the same block iff a(R[i]) == a(R[j])
 #the length of such a block (system) is the degree of Q(a):Q, the length
 # of a block is the degree K:Q(a)
 # a is primitive iff the block system has length n
function _block(a::nf_elem, R::Array{fq_nmod, 1}, ap::fq_nmod_poly)
  # TODO:
  # Maybe this _tmp business has to be moved out of this function too
  _R = GF(Int(characteristic(base_ring(ap))), cached = false)
  _Ry, _ = PolynomialRing(_R, "y", cached = false)
  _tmp = _Ry()
  nf_elem_to_gfp_poly!(_tmp, a, false) # ignore denominator
  set_length!(ap, length(_tmp))
  for i in 0:(length(_tmp) - 1)
    setcoeff!(ap, i, base_ring(ap)(_get_coeff_raw(_tmp, i)))
  end
#  ap = Ft(Zx(a*denominator(a)))
  s = fq_nmod[evaluate(ap, x) for x = R]
  b = Vector{Int}[]
  a = BitSet()
  i = 0
  n = length(R)
  while i < n
    i += 1
    if i in a
      continue
    end
    z = s[i]
    push!(b, findall(x->s[x] == z, 1:n))
    for j in b[end]
      push!(a, j)
    end
  end
  return b
end

#given 2 block systems b1, b2 for elements a1, a2, this computes the
#system for Q(a1, a2), the compositum of Q(a1) and Q(a2) as subfields of K
function _meet(b1::Vector{Vector{Int}}, b2::Vector{Vector{Int}})
  b = Vector{Int}[]
  for i=b1
    for j = i
      for h = b2
        if j in h
          s = intersect(i, h)
          if ! (s in b)
            push!(b, s)
          end
        end
      end
    end
  end
  return b
end

function _find_prime(f::fmpz_poly)
  p = 2^20
  d = 1
  while true
    p = next_prime(p)
    R = GF(p, cached=false)
    Rt = PolynomialRing(R, "t", cached = false)[1]
    fR = change_base_ring(R, f, parent = Rt)
    if degree(fR) != degree(f) || !issquarefree(fR)
      continue
    end
    FS = factor_shape(fR)
    d = lcm([x for (x, v) in FS])
    if d < degree(fR)^2
      break
    end
  end
  return p, d
end

function polredabs(K::AnticNumberField)
  #intended to implement 
  # http://beta.lmfdb.org/knowledge/show/nf.polredabs
  #as in pari
  #TODO: figure out the separation of T2-norms....
  ZK = lll(maximal_order(K))
  I = index(ZK)^2
  D = discriminant(ZK)
  B = basis(ZK, copy = false)
  Zx = FlintZZ["x"][1]
  f = Zx(K.pol)
  p, d = _find_prime(f)
  
  F = FlintFiniteField(p, d, "w", cached = false)[1]
  Ft = PolynomialRing(F, "t", cached = false)[1]
  ap = zero(Ft)
  fit!(ap, degree(K)+1)
  rt = roots(f, F)
  
  n = degree(K)

  b = _block(B[1].elem_in_nf, rt, ap)
  i = 2
  while length(b) < degree(K)
    bb = _block(B[i].elem_in_nf, rt, ap)
    b = _meet(b, bb)
    i += 1
  end
  i -= 1
#  println("need to use at least the first $i basis elements...")
  pr = 100
  old = precision(BigFloat)
  E = enum_ctx_from_ideal(ideal(ZK, 1), zero_matrix(FlintZZ, 1, 1), prec = pr, TU = BigFloat, TC = BigFloat)
  setprecision(BigFloat, pr)
  while true
    try
      if E.C[end] + 0.0001 == E.C[end]  # very very crude...
        pr *= 2
        continue
      end
      break
    catch e
      if isa(e, InexactError) || isa(e, LowPrecisionLLL) || isa(e, LowPrecisionCholesky)
        pr *= 2
        continue
      end
      rethrow(e)
    end
    setprecision(BigFloat, pr)
    E = enum_ctx_from_ideal(ideal(ZK, 1), zero_matrix(FlintZZ, 1, 1), prec = pr, TU = BigFloat, TC = BigFloat)
  end

  l = zeros(FlintZZ, n)
  l[i] = 1

  scale = 1.0
  enum_ctx_start(E, matrix(FlintZZ, 1, n, l), eps = 1.01)

  a = gen(K)
  all_a = nf_elem[a]
  la = length(a)*BigFloat(E.t_den^2)
  Ec = BigFloat(E.c//E.d)
  eps = BigFloat(E.d)^(1//2)

  found_pe = false
  while !found_pe
    while enum_ctx_next(E)
#      @show E.x
      M = E.x*E.t
      q = elem_from_mat_row(K, M, 1, E.t_den)
      bb = _block(q, rt, ap)
      if length(bb) < n
        continue
      end
      found_pe = true
#  @show    llq = length(q)
#  @show sum(E.C[i,i]*(BigFloat(E.x[1,i]) + E.tail[i])^2 for i=1:E.limit)/BigInt(E.t_den^2)
      lq = Ec - (E.l[1] - E.C[1, 1]*(BigFloat(E.x[1,1]) + E.tail[1])^2) #wrong, but where?
#      @show lq/E.t_den^2

      if lq < la + eps
        if lq > la - eps
          push!(all_a, q)
#          @show "new one", q, minpoly(q), bb
        else
          a = q
          all_a = nf_elem[a]
          if lq/la < 0.8
#            @show "re-init"
            enum_ctx_start(E, E.x, eps = 1.01)  #update upperbound
            Ec = BigFloat(E.c//E.d)
          end
          la = lq
  #        @show Float64(la/E.t_den^2)
        end  
      end
    end
    scale *= 2
    enum_ctx_start(E, matrix(FlintZZ, 1, n, l), eps = scale)
    Ec = BigFloat(E.c//E.d)
  end

  setprecision(BigFloat, old)
  all_f = Tuple{nf_elem, fmpq_poly}[(x, minpoly(x)) for x=all_a]
  all_d = fmpq[abs(discriminant(x[2])) for x= all_f]
  m = minimum(all_d)
  L1 = Tuple{nf_elem, fmpq_poly}[]
  for i = 1:length(all_f)
    if all_d[i] == m
      push!(L1, all_f[i])
    end
  end
  L2 = Tuple{nf_elem, fmpq_poly}[minQ(x) for x=L1]
  if length(L2) == 1
    return L2[1]
  end
  L3 = sort(L2, lt = il)

  return L3[1]
end

function Q1Q2(f::PolyElem)
  q1 = parent(f)()
  q2 = parent(f)()
  g = gen(parent(f))
  for j=0:degree(f)
    if isodd(j)
      q2 += coeff(f, j)*g^div(j, 2)
    else
      q1 += coeff(f, j)*g^div(j, 2)
    end
  end
  return q1, q2
end

function minQ(A::Tuple{nf_elem, fmpq_poly})
  a = A[1]
  f = A[2]
  q1, q2 = Q1Q2(f)
  if lead(q1)>0 && lead(q2) > 0
    return (-A[1], f(-gen(parent(f)))*(-1)^degree(f))
  else
    return (A[1], f)
  end
end
  
function int_cmp(a, b)
  if a==b
    return 0
  end
  if abs(a) == abs(b)
    if a>b
      return 1
    else
      return -1
    end
  end
  return cmp(abs(a), abs(b))
end

function il(F, G)
  f = F[2]
  g = G[2]
  i = degree(f)
  while i>0 && int_cmp(coeff(f, i), coeff(g, i))==0 
    i -= 1
  end
  return int_cmp(coeff(f, i), coeff(g, i))<0
end

################################################################################
#
#  LLL for simplify
#
################################################################################

function _ordering_by_T2(M::NfOrd)
  
  K = nf(M)
  B = basis(M, K)
  ints = fmpz[lower_bound(t2(x), fmpz) for x in B]
  p = sortperm(ints)
  On = NfOrd(B[p])
  On.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  return On
end

function lll_precomputation(M::NfOrd, prec::Int)

  n = degree(M)
  K = nf(M)
  natt = div(n, 2)
  g = identity_matrix(FlintZZ, n)
  new_prec = prec
  block = 1
  while block < 3
    @vprint :Simplify 3 "Simplifying block $(block)\n"
    if block == 1
      rg = collect(1:natt)
    else
      rg = collect((natt+1):n)
    end
    new_prec, g1 = _lll_sublattice(M, rg, prec = prec)
    _copy_matrix_into_matrix(g, first(rg), first(rg), g1)
    if new_prec == prec
      block += 1
    else
      prec = new_prec
    end
  end
  @vprint :Simplify 3 "Precision: $(new_prec)\n"
  On = NfOrd(K, g*basis_matrix(M, copy = false))
  On.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  #In pratice, we have changed the main diagonal blocks of the gram matrix. 
  #Now, we do the other blocks
  g = identity_matrix(FlintZZ, n)
  new_prec = prec
  block = 1
  natt = div(n, 4)
  first_part = 1:natt
  second_part = (natt+1):(2*natt)
  third_part = (2*natt+1):3*natt
  fourth_part = (3*natt+1):n
  while block < 3
    @vprint :Simplify 3 "Simplifying block $(block)\n"
    if block == 1
      b1 = first_part
      b2 = third_part
    else
      b1 = second_part
      b2 = fourth_part
    end
    rg = vcat(b1, b2)
    new_prec, g1 = _lll_sublattice(On, rg, prec = prec)
    _copy_matrix_into_matrix(g, first(b1), first(b1), view(g1, 1:length(b1), 1:length(b1)))
    _copy_matrix_into_matrix(g, first(b1), first(b2), view(g1, 1:length(b1), length(b1)+1:length(rg)))
    _copy_matrix_into_matrix(g, first(b2), first(b2), view(g1, length(b1)+1:length(rg), length(b1)+1:length(rg)))
    _copy_matrix_into_matrix(g, first(b2), first(b1), view(g1, length(b1)+1:length(rg), 1:length(b1)))
    if new_prec == prec
      block += 1
    else
      prec = new_prec
    end
  end
  @vprint :Simplify 3 "Precision: $(new_prec)\n"
  On1 = NfOrd(K, g*basis_matrix(On, copy = false))
  On1.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On1.index = M.index
  end
  if isdefined(M, :disc)
    On1.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On1.gen_index = M.gen_index
  end
  g = identity_matrix(FlintZZ, n)
  block = 1
  while block < 3
    @vprint :Simplify 3 "Simplifying block $(block)\n"
    if block == 1
      b1 = first_part
      b2 = fourth_part
    else
      b1 = second_part
      b2 = third_part
    end
    rg = vcat(b1, b2)
    new_prec, g1 = _lll_sublattice(On1, rg, prec = prec)
    _copy_matrix_into_matrix(g, first(b1), first(b1), view(g1, 1:length(b1), 1:length(b1)))
    _copy_matrix_into_matrix(g, first(b1), first(b2), view(g1, 1:length(b1), length(b1)+1:length(rg)))
    _copy_matrix_into_matrix(g, first(b2), first(b2), view(g1, length(b1)+1:length(rg), length(b1)+1:length(rg)))
    _copy_matrix_into_matrix(g, first(b2), first(b1), view(g1, length(b1)+1:length(rg), 1:length(b1)))
    if new_prec == prec
      block += 1
    else
      prec = new_prec
    end
  end
  On2 = NfOrd(K, g*basis_matrix(On1, copy = false))
  On2.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On2.index = M.index
  end
  if isdefined(M, :disc)
    On2.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On2.gen_index = M.gen_index
  end
  @vprint :Simplify 3 "Precomputation finished with precision $(prec)\n"
  return prec, On2
end



function _lll_sublattice(M::NfOrd, u::Vector{Int}; prec = 100)
  K = nf(M)
  n = degree(M)
  l = length(u)
  prec = max(prec, 10*n)
  local g::fmpz_mat
  local d::fmpz_mat
  ctx = Nemo.lll_ctx(0.99, 0.51, :gram)
  att = 0 
  #TODO: If one can compute the exact discriminant of the lattice, we could check correctness. 
  # At the moment it is just heuristic.
  while true
    att += 1
    @vprint :Simplify 3 "Attempt number : $(att)\n"  
    while true
      try
        d = minkowski_gram_mat_scaled(M, prec)
        break
      catch e
        prec = prec*2
      end
    end
    @vprint :Simplify 3 "Minkowski matrix computed\n"
    g = identity_matrix(FlintZZ, l)
    d1 = sub(d, u, u)
    prec = div(prec, 2)
    shift!(d1, -prec)  #TODO: remove?

    for i=1:l
      fmpz_mat_entry_add_ui!(d1, i, i, UInt(l))
    end
    @vtime :Simplify 3 ccall((:fmpz_lll, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{Nemo.lll_ctx}), d1, g, ctx)

    if nbits(maximum(abs, g)) <= div(prec, 2)
      prec *= 2
      break
    end
    @vprint :Simplify 3 "Still in the loop\n"
    prec *= 4
  end
  return prec, g
end


function _weak_lll(M::NfOrd)
  if isdefined(M, :lllO)
    return M.lllO
  else
    return _lll_for_simplify(M)
  end
end


function _lll_for_simplify(M::NfOrd; prec = 100)

  K = nf(M)

  if istotally_real(K)
    #in this case the gram-matrix of the minkowski lattice is the trace-matrix
    #which is exact. 
    BM = _lll_gram(ideal(M, 1))[2]
    O1 = NfOrd(K, BM*basis_matrix(M, copy = false))
    O1.ismaximal = M.ismaximal
    if isdefined(M, :index)
      O1.index = M.index
    end
    if isdefined(M, :disc)
      O1.disc = M.disc
    end
    if isdefined(M, :gen_index)
      O1.gen_index = M.gen_index
    end
    M.lllO = O1
    return O1
  end

  if degree(K) == 2 && discriminant(M) < 0
    #in this case the gram-matrix of the minkowski lattice is related to the
    #trace-matrix which is exact.
    #could be extended to CM-fields
    BM = _lll_quad(ideal(M, 1))[2]
    O1 = NfOrd(K, BM*basis_matrix(M, copy = false))
    O1.ismaximal = M.ismaximal
    if isdefined(M, :index)
      O1.index = M.index
    end
    if isdefined(M, :disc)
      O1.disc = M.disc
    end
    if isdefined(M, :gen_index)
      O1.gen_index = M.gen_index
    end
    M.lllO = O1
    return O1
  end

  n = degree(M)
  prec = max(prec, 10*n)
  disc = abs(discriminant(M))
  if n > 10
    prec, M = lll_precomputation(M, prec)
  end
  local g::fmpz_mat
  local d::fmpz_mat
  ctx = Nemo.lll_ctx(0.75, 0.51, :gram)
  att = 0 
  while true
    att += 1
    @vprint :Simplify 3 "Attempt number : $(att)\n"
    
    while true
      try
        d = minkowski_gram_mat_scaled(M, prec)
        break
      catch e
        prec = prec*2
      end
    end
    @vprint :Simplify 3 "Minkowski matrix computed\n"
    diag_d = prod_diagonal(d)
    g = identity_matrix(FlintZZ, n)
    
    prec = div(prec, 2)
    shift!(d, -prec)  #TODO: remove?

    for i=1:n
      fmpz_mat_entry_add_ui!(d, i, i, UInt(nrows(d)))
    end
    @vtime :Simplify 3 ccall((:fmpz_lll, :libflint), Nothing, (Ref{fmpz_mat}, Ref{fmpz_mat}, Ref{Nemo.lll_ctx}), d, g, ctx)
    
    if nbits(maximum(abs, g)) <= div(prec, 2)
      fl = true
      disc = abs(discriminant(M))
      di = root(disc, n)+1
      di *= fmpz(2)^(div(n+1,2)+prec)
      if cmpindex(d, 1, 1, di) > 0 
        fl = false
      else
        pr = prod_diagonal(d)
        if pr > fmpz(2)^(div(n*(n-1), 2)+(n*prec)) * disc 
          fl = false
        end
      end
      if fl
        break
      end
    end
    On = NfOrd(K, g*basis_matrix(M, copy = false))
    On.ismaximal = M.ismaximal
    if isdefined(M, :index)
      On.index = M.index
    end
    if isdefined(M, :disc)
      On.disc = M.disc
    end
    if isdefined(M, :gen_index)
      On.gen_index = M.gen_index
    end
    prec *= 2
    d1 = minkowski_gram_mat_scaled(On, prec)
    if prod_diagonal(d1) < diag_d
      @vprint :Simplify 3 "I use the transformation\n"
      M = On
    else
      prec *= 2
    end
    @vprint :Simplify 3 "Still in the loop\n"
  end
  ## lattice has lattice disc = order_disc * norm^2
  ## lll needs to yield a basis sth
  ## l[1,1] = |b_i|^2 <= 2^((n-1)/2) disc^(1/n)  
  ## and prod(l[i,i]) <= 2^(n(n-1)/2) disc
  
  On = NfOrd(K, g*basis_matrix(M, copy = false))
  On.ismaximal = M.ismaximal
  if isdefined(M, :index)
    On.index = M.index
  end
  if isdefined(M, :disc)
    On.disc = M.disc
  end
  if isdefined(M, :gen_index)
    On.gen_index = M.gen_index
  end
  #Now, I compute a LLL basis with parameters 0.99, 0.51
  res = lll(On, prec = prec)
  @vprint :Simplify 3 "LLL finished\n"
  return res
end
