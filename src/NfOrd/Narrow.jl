export narrow_class_group

@doc Markdown.doc"""
***
    power_reduce2(A::NfOrdIdl, e::fmpz) -> NfOrdIdl, FacElem{nf_elem}
> Computes $B$ and $\alpha$ in factored form, such that $\alpha B = A^e$
"""
function power_reduce2(A::NfOrdIdl, e::fmpz)
  A_orig = deepcopy(A)
  e_orig = e

  O = order(A)
  K= nf(O)
  if norm(A) > abs(discriminant(O))
    A, a = reduce_ideal2(A)
    @hassert :PID_Test 1 a*A_orig == A
    # A_old * inv(a) = A_new
    #so a^e A_old^e = A_new^e
    al = FacElem(Dict(a=>-e))
  else
    al = FacElem(Dict(K(1) => fmpz(1)))
  end

  #we have A_orig^e = (A*a)^e = A^e*a^e = A^e*al and A is now small

  if e < 0
    B = inv(A)
    A = numerator(B)
    al *= FacElem(Dict(K(denominator(B)) => fmpz(e)))
    e = -e
  end
  # A^e = A^(e/2)^2 A or A^(e/2)^2
  # al * A^old^(e/2) = A_new
  if e>1
    C, cl = power_reduce2(A, div(e, 2))
    @hassert :PID_Test 1 C*evaluate(cl) == A^Int(div(e, 2))

    C2 = C^2
    al = al*cl^2
    if norm(C2) > abs(discriminant(O))
      C2, a = reduce_ideal2(C2)
      al *= inv(a)
    end

    if isodd(e)
      A = C2*A
      if norm(A) > abs(discriminant(O))
        A, a = reduce_ideal2(A)
        al *= inv(a)
      end
    else
      A = C2
    end
    return A, al
  else
    @assert e==1
    return A, al
  end
end

function ==(A::NfOrdIdl, B::NfOrdFracIdl)
  C = simplify(B)
  if C.den != 1 ||
     C.num != A
    return false
  else
    return true
  end
end

==(A::NfOrdFracIdl, B::NfOrdIdl) = B==A

@doc Markdown.doc"""
***
    reduce_ideal2(A::FacElem{NfOrdIdl}) -> NfOrdIdl, FacElem{nf_elem}
> Computes $B$ and $\alpha$ in factored form, such that $\alpha B = A$.
"""
function reduce_ideal2(I::FacElem{NfOrdIdl, NfOrdIdlSet})
  O = order(first(keys(I.fac)))
  K = nf(O)
  fst = true
  a = FacElem(Dict(K(1) => fmpz(1)))
  A = ideal(O, 1)

  for (k,v) = I.fac
    @assert order(k) == O
    if iszero(v)
      continue
    end
    if fst
      A, a = power_reduce2(k, v)
      @hassert :PID_Test 1 (v>0 ? k^Int(v) : inv(k)^Int(-v)) == A*evaluate(a)
      fst = false
    else
      B, b = power_reduce2(k, v)
      @hassert :PID_Test (v>0 ? k^Int(v) : inv(k)^Int(-v)) == B*evaluate(b)
      A = A*B
      a = a*b
      if norm(A) > abs(discriminant(O))
        A, c = reduce_ideal2(A)
        a = a*FacElem(Dict(K(c) => fmpz(-1)))
      end
    end
  end
  @hassert :PID_Test 1 A*evaluate(a) == evaluate(I)
  return A, a
end

mutable struct MapNarrowClassGrp{T} <: Map{T, NfOrdIdlSet, HeckeMap, MapNarrowClassGrp}
  header::MapHeader

  function MapNarrowClassGrp{T}() where {T}
    return new{T}()
  end
end

function show(io::IO, mC::MapNarrowClassGrp)
  println(io, "NarrowClassGroup map of $(codomain(mC))")
end

#TODO: make it for AnticNumberField and for NfOrd. I that
#      case also return OrdElem

@doc Markdown.doc"""
***
    elements_with_all_signs(L::NfOrd) -> Array{nf_elem, 1}
> Finds elements $x_i$ in the number field s.th the elements
> totally positive at all but the $i$-th real embedding, but 
> negative at the $i$-th.
"""
function elements_with_all_signs(L::NfOrd)
  r1, r2 = signature(L)
  K = nf(L)
  
  S = DiagonalGroup([2 for i=1:r1])

  inf_places = real_places(K)

  function logS(x)
    return S([x[P] > 0 ? 0 : 1 for P in inf_places])
  end

  s = typeof(S[1])[]
  g = nf_elem[]
  u, mu = sub(S, s)
  b = 10
  cnt = 0
  while true
    a = rand(L, b)
    iszero(a) && continue
    t = logS(signs(K(a)))
    if !haspreimage(mu, t)[1]
      push!(s, t)
      push!(g, K(a))
      u, mu = sub(S, s)
      if order(u) == order(S)
        break
      end
    else
      cnt += 1
      if cnt > 100
        b *= 2
        cnt = 0
      end
    end
  end
  X = DiagonalGroup([2 for i=1:r1])
  hX = GrpAbFinGenMap(X, X, vcat([x.coeff for x=s]))
  r = nf_elem[]
  for i=1:r1
    y = haspreimage(hX, X[i])[2]
    push!(r, prod([g[i]^Int(y[i]) for i=1:r1]))
  end
  return r
end

@doc Markdown.doc"""
***
    narrow_class_group(L::NfOrd) -> GrpAbFinGen, Map
> Compute the narrow (or strict) class group of $L$, ie. the
> group of invertable ideals modulo the group of totally positive elements.
> In case the field has no real embedding, this is just the class group.
"""
function narrow_class_group(L::NfOrd)
  C, mC = class_group(L)

  r1, r2 = signature(L)
  if r1 == 0
    return C, mC
  end

  U, mU = unit_group_fac_elem(L)

  K = nf(L)

  inf_places = real_places(K)
  @assert length(inf_places) == r1

  # 1 -> K^*/K^+U -> Cl^+ -> Cl -> 1
  # K^*/K^+ = C_2^{r_1}

  gensC = [mC(C[i]) for i=1:ngens(C)]

  S = DiagonalGroup([2 for i=1:r1])

  function logS(x)
    return S([x[P] > 0 ? 0 : 1 for P in inf_places])
  end
  s, ms = quo(S, [logS(signs(mU(U[i]))) for i=1:ngens(U)])
  s, mms = snf(s)
  ms = ms*inv(mms)

  # we want the extension 1-> s -> X -> C -> 1
  # generators are gensC supplemented by gens(s)

  RC = rels(C)
  R = hcat(zero_matrix(FlintZZ, rows(RC), ngens(s)), RC)
  for i=1:ngens(C)
    A, al = power_reduce2(gensC[i], order(C[i]))
    be = principal_gen_fac_elem(A)
    x = ms(logS(signs(al*be)))
    for j=1:ngens(s)
      R[i,j] = x.coeff[1, j]
    end
  end
  R = vcat(R, hcat(rels(s), zero_matrix(FlintZZ, nrels(s), ngens(C))))

  X = AbelianGroup(R)

  el = elements_with_all_signs(L)
  sign_gen = [preimage(ms, s[i]) for i=1:ngens(s)]
  sg = [ prod([el[i]^Int(x[i]) for i=1:length(el)]) for x=sign_gen]

  function exp(a::GrpAbFinGenElem)
    return L(prod([sg[i]^Int(a.coeff[1,i]) for i=1:length(sg)])) * image(mC, C([a.coeff[1, i+length(sg)] for i=1:ngens(C)]))
  end

  function log(A::NfOrdIdl)
    a = preimage(mC, A)
    B = FacElem(Dict(A => fmpz(-1))) * FacElem(gensC, [a.coeff[1,i] for i=1:ngens(C)])
    A, c = reduce_ideal2(B)
    b = c*principal_gen_fac_elem(A)
    return X(hcat(ms(logS(signs(b))).coeff, a.coeff))
  end

  mp = MapNarrowClassGrp{typeof(X)}()
  mp.header = MapHeader(X, NfOrdIdlSet(L), exp, log)
  return X, mp
end

