export simplify

@doc Markdown.doc"""
    simplify(K::AnticNumberField; canonical::Bool = false) -> AnticNumberField, NfToNfMor
 > Tries to find an isomorphic field $L$ given by a "nicer" defining polynomial.
 > By default, "nice" is defined to be of smaller index, testing is done only using
 > a LLL-basis of the maximal order.
 > If \texttt{canonical} is set to {{{true}}}, then a canonical defining
 > polynomial is found, where canonical is using the pari-definition of {{{polredabs}}}
 > in http://beta.lmfdb.org/knowledge/show/nf.polredabs.
 > Both version require a LLL reduced basis for the maximal order.
"""
function simplify(K::AnticNumberField; canonical::Bool = false)
  Qx, x = PolynomialRing(FlintQQ)
  if canonical
    a, f1 = polredabs(K)
    f = Qx(f1)
  else
    OK = maximal_order(K)
    ZK = lll(OK)
    a = gen(K)
    if isdefining_polynomial_nice(K)
      I = index(OK)
    else
      I = divexact(numerator(discriminant(K.pol)), discriminant(ZK))
    end
    B = basis(ZK, copy = false)
    
    for i = 1:length(B)
      if isone(denominator(B[i].elem_in_nf))
        continue
      end 
      el = OK(B[i].elem_in_nf)
      ind_a = _index(el)
      if !iszero(ind_a) && ind_a < I
        a = B[i].elem_in_nf
        I = ind_a
      end
    end
    f = minpoly(Qx, a)
  end
  L = NumberField(f, cached = false, check = false)[1]
  m = hom(L, K, a, check = false)
  return L, m
end

function _index(a::NfOrdElem)
  O = parent(a)
  d = degree(O)
  M = zero_matrix(FlintZZ, d, d)
  c = elem_in_basis(one(O), copy = false)
  for i = 1:d
    M[1, i] = c[i]
  end
  a1 = deepcopy(a)
  for i = 2:d
    c = elem_in_basis(a1, copy = false)
    for j = 1:d
      M[i, j] = c[j]
    end
    mul!(a1, a1, a)
  end
  return abs(det(M))
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
  c = FlintZZ()
  ap.length = a.elem_length
  for i=0:a.elem_length
    Nemo.num_coeff!(c, a, i)
    setcoeff!(ap, i, c)
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
    fR = change_base_ring(f, R)
    if !issquarefree(fR)
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


