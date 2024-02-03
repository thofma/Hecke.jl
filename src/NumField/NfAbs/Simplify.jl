add_verbosity_scope(:Simplify)

@doc raw"""
    simplify(K::AbsSimpleNumField; canonical::Bool = false) -> AbsSimpleNumField, NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}

Tries to find an isomorphic field $L$ given by a "simpler" defining polynomial.
By default, "simple" is defined to be of smaller index, testing is done only
using a LLL-basis of the maximal order.

If `canonical` is set to `true`, then a canonical defining polynomial is found,
where canonical is using the definition of PARI's `polredabs`, which is described in
http://beta.lmfdb.org/knowledge/show/nf.polredabs.

Both versions require a LLL reduced basis for the maximal order.
"""
function simplify(K::AbsSimpleNumField; canonical::Bool = false, cached::Bool = true, save_LLL_basis::Bool = true)
  Qx, x = polynomial_ring(FlintQQ, "x")

  if degree(K) == 1
    L = number_field(x - 1, cached = cached, check = false)[1]
    return L, hom(L, K, gen(K), check = false)
  end
  if canonical
    if !is_defining_polynomial_nice(K)
      K1, mK1 = simplify(K, cached = false, save_LLL_basis = false)
      K2, mK2 = simplify(K1, cached = cached, save_LLL_basis = save_LLL_basis, canonical = true)
      return K2, mK2*mK1
    end
    a, f1 = polredabs(K)
    f = Qx(f1)
    L = number_field(f, cached = cached, check = false)[1]
    m = hom(L, K, a, check = false)
    return L, m
  end
  n = degree(K)
  OK = maximal_order(K)
  if isdefined(OK, :lllO)
    @vprintln :Simplify 1 "LLL basis was already there"
    ZK = OK.lllO::typeof(OK)
  else
    b = _simplify(OK)
    if b != gen(K)
      @vprintln :Simplify 1 "The basis of the maximal order contains a better primitive element"
      f1 = Qx(minpoly(representation_matrix(OK(b))))
      L1 = number_field(f1, cached = cached, check = false)[1]
      #Before calling again the simplify on L1, we need to define the maximal order of L1
      mp = hom(L1, K, b, check = false)
      _assure_has_inverse_data(mp)
      B = basis(OK, K)
      BOL1 = Vector{AbsSimpleNumFieldElem}(undef, degree(L1))
      for i = 1:degree(L1)
        BOL1[i] = mp\(B[i])
      end
      OL1 = AbsSimpleNumFieldOrder(BOL1, false)
      OL1.is_maximal = 1
      set_attribute!(L1, :maximal_order => OL1)
      @vprintln :Simplify 3 "Trying to simplify $(L1.pol)"
      L2, mL2 = simplify(L1, cached = cached, save_LLL_basis = save_LLL_basis)
      h = mL2 * mp
      return L2, mL2*mp
    end
    prec = 100 + 25*div(n, 3) + Int(round(log(abs(discriminant(OK)))))
    @vtime :Simplify 3 ZK = lll(OK, prec = prec)
    OK.lllO = ZK
  end
  @vtime :Simplify 3 a = _simplify(ZK)
  if a == gen(K)
    f = K.pol
  else
    @vtime :Simplify 3 f = Qx(minpoly(representation_matrix(OK(a))))
  end
  L = number_field(f, cached = cached, check = false)[1]
  m = hom(L, K, a, check = false)
  if save_LLL_basis
    _assure_has_inverse_data(m)
    B = basis(ZK, K)
    BOL = Vector{AbsSimpleNumFieldElem}(undef, degree(L))
    for i = 1:degree(L)
      BOL[i] = m\(B[i])
    end
    OL = AbsSimpleNumFieldOrder(BOL, false)
    if isdefined(ZK, :disc)
      OL.disc = ZK.disc
      if is_defining_polynomial_nice(L)
        OL.index = root(divexact(numerator(discriminant(L.pol)), OL.disc), 2)
      end
    end
    OL.is_maximal = 1
    set_attribute!(L, :maximal_order => OL)
  end
  if cached
    embed(m)
    embed(inv(m))
  end
  return L, m
end

function _simplify(O::AbsNumFieldOrder)
  K = nf(O)

  B = basis(O, K, copy = false)
  nrep = min(3, degree(K))
  Bnew = elem_type(K)[]
  for i = 1:length(B)
    push!(Bnew, B[i])
    for j = 1:nrep
      push!(Bnew, B[i]+B[j])
      push!(Bnew, B[i]-B[j])
    end
  end
  #First, we search for elements that are primitive using block systems in the simple case.
  B1 = _sieve_primitive_elements(Bnew)

  #Now, we select the one of smallest T2 norm
  a = primitive_element(K)
  d = denominator(a, O)
  if !isone(d)
    a *= d
  end
  I = t2(a)
  for i = 1:length(B1)
    t2n = t2(B1[i])
    if t2n < I
      a = B1[i]
      I = t2n
    end
  end
  return a
end

function primitive_element(K::AbsSimpleNumField)
  return gen(K)
end

function _sieve_primitive_elements(B::Vector{AbsNonSimpleNumFieldElem})
  K = parent(B[1])
  Zx = polynomial_ring(FlintZZ, "x", cached = false)[1]
  pols = [Zx(to_univariate(Globals.Qx, x)) for x in K.pol]
  p, d = _find_prime(pols)
  F = Native.finite_field(p, d, "w", cached = false)[1]
  Fp = Native.GF(p, cached = false)
  Fpt = polynomial_ring(Fp, ngens(K))[1]
  Ft = polynomial_ring(F, "t", cached = false)[1]
  rt = Vector{Vector{fqPolyRepFieldElem}}(undef, ngens(K))
  for i = 1:length(pols)
    rt[i] = roots(F, pols[i])
  end
  rt_all = Vector{Vector{fqPolyRepFieldElem}}(undef, degree(K))
  ind = 1
  it = cartesian_product_iterator([1:degrees(K)[i] for i in 1:ngens(K)], inplace = true)
  for i in it
    rt_all[ind] = fqPolyRepFieldElem[rt[j][i[j]] for j = 1:length(rt)]
    ind += 1
  end
  indices = Int[]
  for i = 1:length(B)
    if length(vars(data(B[i]))) != ngens(K)
      continue
    end
    if isone(denominator(B[i]))
      continue
    end
    if _is_primitive_via_block(B[i], rt_all, Fpt)
      push!(indices, i)
    end
  end
  return B[indices]
end

function _is_primitive_via_block(el::AbsNonSimpleNumFieldElem, rt::Vector{Vector{fqPolyRepFieldElem}}, Rt::MPolyRing)
  K = parent(el)
  fR = map_coefficients(base_ring(Rt), data(el), parent = Rt)
  s = Set{fqPolyRepFieldElem}()
  for x in rt
    val = evaluate(fR, x)
    if val in s
      return false
    end
    push!(s, val)
    if length(s) > div(degree(K), 2)
      return true
    end
  end
  error("Something went wrong")
end

function _block(el::AbsNonSimpleNumFieldElem, rt::Vector{Vector{fqPolyRepFieldElem}}, R::fpField)
  fR = map_coefficients(R, data(el), cached = false)
  s = fqPolyRepFieldElem[evaluate(fR, x) for x in rt]
  b = Vector{Int}[]
  a = BitSet()
  i = 0
  n = length(rt)
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

function _sieve_primitive_elements(B::Vector{AbsSimpleNumFieldElem})
  K = parent(B[1])
  Zx = polynomial_ring(FlintZZ, "x", cached = false)[1]
  f = Zx(K.pol*denominator(K.pol))
  a = gen(K)*denominator(K.pol)

  p, d = _find_prime(ZZPolyRingElem[f])

  F = Nemo.Native.finite_field(p, d, "w", cached = false)[1]
  Ft = polynomial_ring(F, "t", cached = false)[1]
  ap = zero(Ft)
  fit!(ap, degree(K)+1)
  rt = roots(F, f)

  n = degree(K)
  indices = Int[]
  for i = 1:length(B)
    if isone(denominator(B[i]))
      continue
    end
    b = _block(B[i], rt, ap)
    if length(b) == n
      push!(indices, i)
    end
  end
  return B[indices]

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
function _block(a::AbsSimpleNumFieldElem, R::Vector{fqPolyRepFieldElem}, ap::fqPolyRepPolyRingElem)
  # TODO:
  # Maybe this _tmp business has to be moved out of this function too
  _R = Native.GF(Int(characteristic(base_ring(ap))), cached = false)
  _Ry, _ = polynomial_ring(_R, "y", cached = false)
  _tmp = _Ry()
  Nemo.nf_elem_to_gfp_poly!(_tmp, a, false) # ignore denominator
  set_length!(ap, length(_tmp))
  for i in 0:(length(_tmp) - 1)
    setcoeff!(ap, i, base_ring(ap)(_get_coeff_raw(_tmp, i)))
  end
#  ap = Ft(Zx(a*denominator(a)))
  s = fqPolyRepFieldElem[evaluate(ap, x) for x = R]
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
          if !(s in b)
            push!(b, s)
          end
        end
      end
    end
  end
  return b
end

function _find_prime(v::Vector{ZZPolyRingElem})
  p = 2^10
  total_deg = prod(degree(x) for x in v)
  n_attempts = min(total_deg, 10)
  candidates = Vector{Tuple{Int, Int}}(undef, n_attempts)
  i = 1
  polsR = Vector{fpPolyRingElem}(undef, length(v))
  while i < n_attempts+1
    p = next_prime(p)
    R = Native.GF(p, cached=false)
    Rt = polynomial_ring(R, "t", cached = false)[1]
    found_bad = false
    for j = 1:length(v)
      fR = map_coefficients(R, v[j], parent = Rt)
      if degree(fR) != degree(v[j]) || !is_squarefree(fR)
        found_bad = true
        break
      end
      polsR[j] = fR
    end
    if found_bad
      continue
    end
    d = 1
    for j = 1:length(polsR)
      fR = polsR[j]
      FS = factor_shape(fR)
      d1 = lcm(Int[x for (x, v) in FS])
      d = lcm(d1, d)
    end
    if d <= total_deg^2
      candidates[i] = (p, d)
      i += 1
    end
  end
  res = candidates[1]
  for j = 2:n_attempts
    if candidates[j][2] < res[2]
      res = candidates[j]
    end
  end
  return res[1], res[2]
end

function polredabs(K::AbsSimpleNumField)
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
  p, d = _find_prime(ZZPolyRingElem[f])

  F = Native.finite_field(p, d, "w", cached = false)[1]
  Ft = polynomial_ring(F, "t", cached = false)[1]
  ap = zero(Ft)
  fit!(ap, degree(K)+1)
  rt = roots(F, f)

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
  local E
  while true
    try
      setprecision(BigFloat, pr)
      E = enum_ctx_from_ideal(ideal(ZK, 1), zero_matrix(FlintZZ, 1, 1), prec = pr, TU = BigFloat, TC = BigFloat)

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
  end

  scale = 1.0
  enum_ctx_start(E, i, eps = 1.01) #start at the 1st vector having
                       # a 1 at position i, it's pointless to start earlier
                       #as none of the elements can be primitive.

  a = gen(K)
  all_a = AbsSimpleNumFieldElem[a]
  la = length(a)*BigFloat(E.t_den^2)
  Ec = BigFloat(E.c//E.d)
  eps = BigFloat(E.d)^(1//2)

  found_pe = false
  first = true
  while !found_pe
    while first || enum_ctx_next(E)
      first = false
      M = E.x*E.t
      q = elem_from_mat_row(K, M, 1, E.t_den)
      bb = _block(q, rt, ap)
      if length(bb) < n
        continue
      end
      found_pe = true
#  @show    llq = length(q)
#  @show sum(E.C[i,i]*(BigFloat(E.x[1,i]) + E.tail[i])^2 for i=1:E.limit)/BigInt(E.t_den^2)
      lq = Ec - (E.l[1] - E.C[1, 1]*(BigFloat(E.x[1,1]) + E.tail[1])^2)
#      @show lq/E.t_den^2

      if lq < la + eps
        if lq > la - eps
          push!(all_a, q)
#          @show "new one", q, minpoly(q), bb
        else
          a = q
          all_a = AbsSimpleNumFieldElem[a]
          if lq/la < 0.8
#            @show "re-init"
            enum_ctx_start(E, E.x, eps = 1.01)  #update upperbound
            first = true
            Ec = BigFloat(E.c//E.d)
          end
          la = lq
  #        @show Float64(la/E.t_den^2)
        end
      end
    end
    scale *= 2
    enum_ctx_start(E, i, eps = scale)
    first = true
    Ec = BigFloat(E.c//E.d)
  end

  setprecision(BigFloat, old)
  #try to find the T2 shortest element
  #the precision management here needs a revision once we figure out
  #how....
  #examples that require this are Gunters:
  #=
  die drei Polynome

[ 10834375376002294480896, x^18 - x^16 - 6*x^14 - 4*x^12 - 4*x^10 + 2*x^8 +
6*x^6 - 4*x^4 + 3*x^2 - 1 ],
[ 10834375376002294480896, x^18 - 3*x^16 + 4*x^14 - 6*x^12 - 2*x^10 + 4*x^8 +
4*x^6 + 6*x^4 + x^2 - 1 ],
[ 10834375376002294480896, x^18 + x^16 - x^14 - 8*x^12 - 3*x^8 + 27*x^6 -
25*x^4 + 8*x^2 - 1 ],


werden alle als 'canonical' ausgegeben, obwohl sie isomorphe
K"orper definieren ??
=#
  sort!(all_a, lt = (a,b) -> length(a) < length(b))
  i = length(all_a)
  la1 = length(all_a[1])
  while i >= 1 && la1 <= length(all_a[i]) - 1e-10
    i -= 1
  end
  all_a = all_a[1:i]

  all_f = Tuple{AbsSimpleNumFieldElem, QQPolyRingElem}[(x, minpoly(x)) for x=all_a]
  all_d = QQFieldElem[abs(discriminant(x[2])) for x= all_f]
  m = minimum(all_d)
  L1 = Tuple{AbsSimpleNumFieldElem, QQPolyRingElem}[]
  for i = 1:length(all_f)
    if all_d[i] == m
      push!(L1, all_f[i])
    end
  end
  L2 = Tuple{AbsSimpleNumFieldElem, QQPolyRingElem}[minQ(x) for x=L1]
  if length(L2) == 1
    return L2[1]
  end
  L3 = sort(L2, lt = il)

  return L3[1]
end

function Q1Q2(f::PolyRingElem)
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

function minQ(A::Tuple{AbsSimpleNumFieldElem, QQPolyRingElem})
  a = A[1]
  f = A[2]
  q1, q2 = Q1Q2(f)
  if leading_coefficient(q1)>0 && leading_coefficient(q2) > 0
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
