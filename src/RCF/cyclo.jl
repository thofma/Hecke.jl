################################################################################
#
#  Type definition
#
################################################################################

mutable struct CyclotomicExt
  k::AbsSimpleNumField
  n::Int
  Kr::Hecke.RelSimpleNumField{AbsSimpleNumFieldElem}
  Ka::AbsSimpleNumField
  mp::Tuple{NumFieldHom{AbsSimpleNumField, RelSimpleNumField{AbsSimpleNumFieldElem}}, _AbsSimpleNumFieldHom}

  kummer_exts::Dict{Set{ZZRingElem}, Tuple{Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, KummerExt}}
                      #I save the kummer extensions used in the class field construction
                      #The keys are the factors of the minimum of the conductor
  function CyclotomicExt()
    return new()
  end
end

function Base.show(io::IO, c::CyclotomicExt)
  print(io, "Cyclotomic extension by zeta_$(c.n) of degree $(degree(c.Ka))")
end

absolute_simple_field(C::CyclotomicExt) = C.Ka
base_field(C::CyclotomicExt) = C.k

################################################################################
#
#  Interface and creation
#
################################################################################

function simplify!(C::CyclotomicExt)
  if degree(C.Kr) == 1
    return nothing
  end
  if is_maximal_order_known(C.Ka) && isdefined(maximal_order(C.Ka), :lllO)
    KS, mKS = simplify(C.Ka, cached = false, save_LLL_basis = false)
    if KS === C.Ka
      return nothing
    end
    abs2rel = mKS*C.mp[1]
    mKSi = inv(mKS)
    small2abs = C.mp[2]*mKSi
    C.Ka = KS
    C.mp = (abs2rel, small2abs)
    return nothing
  end
  Ka, mKa = simplified_absolute_field(C.Kr, cached = false)
  Ks, mKs = simplify(Ka, cached = false)
  abs2rel = mKs*mKa
  imKa = inv(abs2rel)
  small2abs = hom(base_field(C.Kr), Ks, imKa(C.Kr(gen(base_field(C.Kr)))))
  C.Ka = Ks
  C.mp = (abs2rel, small2abs)
  return nothing
end

@doc raw"""
    cyclotomic_extension(k::AbsSimpleNumField, n::Int) -> CyclotomicExt

Computes $k(\zeta_n)$, in particular, a structure containing $k(\zeta_n)$
both as an absolute extension, as a relative extension (of $k$) and the maps
between them.
"""
function cyclotomic_extension(k::AbsSimpleNumField, n::Int; cached::Bool = true, compute_maximal_order::Bool = true, compute_LLL_basis::Bool = true, simplified::Bool = true)
  if cached
    Ac = get_attribute!(() -> CyclotomicExt[], k, :cyclotomic_ext)::Vector{CyclotomicExt}
    for i = Ac
      if i.n == n
        return i
      end
    end
  end

  kt, t = polynomial_ring(k, "t", cached = false)
  c = CyclotomicExt()
  c.kummer_exts = Dict{Set{ZZRingElem}, Tuple{Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, KummerExt}}()
  c.k = k
  c.n = n

  if n <= 2
    #Easy, just return the field
    if n == 2
      Kr = number_field(t+1, cached = false, check = false)[1]
    else
      Kr = number_field(t-1, cached = false, check = false)[1]
    end
    if compute_maximal_order
      Ok = maximal_order(k)
      if compute_LLL_basis
        lll(Ok)
      end
    end
    abs2rel = hom(k, Kr, Kr(gen(k)), inverse = (gen(k), k(n==2 ? -1 : 1)))
    small2abs = id_hom(k)
    c.Kr = Kr
    c.Ka = k
    c.mp = (abs2rel, small2abs)
    if cached
      push!(Ac, c)
    end
    return c
  end

  ZX, X = polynomial_ring(ZZ, cached = false)
  f = cyclotomic(n, X)
  fk = change_base_ring(k, f, parent = kt)
  if n < 5
    #For n = 3, 4 the cyclotomic polynomial has degree 2,
    #so we can just ask for the roots.
    if !isone(gcd(degree(fk), degree(k))) && !is_totally_real(k)
      rt = _roots_hensel(fk, max_roots = 1, is_normal = true)
    else
      rt = AbsSimpleNumFieldElem[]
    end
    if length(rt) == 1
      #The polynomial splits completely!
      Kr, gKr = number_field(t - rt[1], cached = false, check = false)
      abs2rel = hom(k, Kr, Kr(gen(k)), inverse = (gen(k), rt[1]))
      small2abs = id_hom(k)
      if compute_maximal_order
        Ok = maximal_order(k)
        if compute_LLL_basis
          lll(Ok)
        end
      end
      c.Kr = Kr
      c.Ka = k
      c.mp = (abs2rel, small2abs)
    else
      Kr, Kr_gen = number_field(fk, "z_$n", cached = false, check = false)
      Ka, abs2rel, small2abs = collapse_top_layer(Kr, cached = false)
      if compute_maximal_order && !simplified
        Zk = maximal_order(k)
        b_k = basis(Zk, k)
        B_k = Vector{AbsSimpleNumFieldElem}(undef, degree(Ka))
        for i = 1:length(b_k)
          B_k[i] = small2abs(b_k[i])
        end
        g = abs2rel\(Kr_gen)
        for j = 1:length(b_k)
          B_k[j+length(b_k)] = B_k[j]*g
        end
        ZKa = Hecke.AbsSimpleNumFieldOrder(B_k)
        ZKa.disc = discriminant(f)^degree(k)*discriminant(Zk)^degree(fk)
        ZKa.index = root(divexact(numerator(discriminant(Ka)), ZKa.disc), 2)
        ZKa.gen_index = QQFieldElem(ZKa.index)
        for (p,v) = factor(gcd(discriminant(Zk), ZZRingElem(n))).fac
          ZKa = pmaximal_overorder(ZKa, p)
        end
        ZKa.is_maximal = 1
        set_attribute!(Ka, :maximal_order => ZKa)
        if !simplified && compute_LLL_basis
          lll(ZKa)
        end
      end
      c.Kr = Kr
      c.Ka = Ka
      c.mp = (abs2rel, small2abs)
      if simplified
        simplify!(c)
      end
    end
    if cached
      push!(Ac, c)
    end
    if (is_torsion_unit_group_known(k) || is_totally_real(k)) && c.Ka != k
      ok, gTk = _torsion_units_gen(k)
      expected = Int(_torsion_group_order_divisor(c.Ka))
      if expected == lcm(ok, n)
        #In this case, we know that the generator is the product.
        genTKa = c.mp[2](gTk)*(c.mp[1]\(gen(Kr)))
        set_attribute!(c.Ka, :torsion_units => (expected, genTKa))
      end
    end
    return c
  end

  if gcd(degree(fk), degree(k)) != 1
    lf = factor(fk)
    fk = first(keys(lf.fac))
  end

  Kr, Kr_gen = number_field(fk, "z_$n", cached = false, check = false)
  if degree(fk) != 1
    Ka, abs2rel, small2abs = collapse_top_layer(Kr, cached = false)

    if compute_maximal_order && !simplified
      # An equation order defined from a factor of a
      # cyclotomic polynomial is always maximal by Dedekind
      # hence the product basis should be maximal at all primes except
      # for all p dividing the gcd()
      Zk = maximal_order(k)
      b_k = basis(Zk, k)
      B_k = Vector{AbsSimpleNumFieldElem}(undef, degree(Ka))
      for i = 1:length(b_k)
        B_k[i] = small2abs(b_k[i])
      end
      g = abs2rel\(Kr_gen)
      s = length(b_k)+1
      for i = 1:degree(fk)-1
        for j = 1:degree(k)
          B_k[s] = B_k[s-degree(k)]*g
          s += 1
        end
      end
      ZKa = Hecke.AbsSimpleNumFieldOrder(B_k)
      if degree(Kr) == euler_phi(n)
        ZKa.disc = (discriminant(Zk)^euler_phi(n))*discriminant(f)^degree(k)
        ZKa.index = root(divexact(numerator(discriminant(Ka)), discriminant(ZKa)), 2)
        ZKa.gen_index = ZZRingElem(ZKa.index)
      else
        ZKa.disc = (discriminant(Zk)^degree(Kr))*numerator(norm(discriminant(fk)))
        ZKa.index = root(divexact(numerator(discriminant(Ka)), discriminant(ZKa)), 2)
        ZKa.gen_index = ZZRingElem(ZKa.index)
      end
      for (p, v) in factor(gcd(discriminant(Zk), ZZRingElem(n)))
        ZKa = pmaximal_overorder(ZKa, p)
      end
      ZKa.is_maximal = 1
      if !simplified && compute_LLL_basis
        lll(ZKa)
      end
      set_attribute!(Ka, :maximal_order => ZKa)
    end
  else
    Ka = k
    abs2rel = hom(Ka, Kr, Kr(gen(Ka)), inverse = (gen(Ka), -coeff(fk, 0)))
    small2abs = id_hom(k)
    if compute_maximal_order
      Ok = maximal_order(k)
      if compute_LLL_basis
        lll(Ok)
      end
    end
  end

  c.Kr = Kr
  c.Ka = Ka
  c.mp = (abs2rel, small2abs)
  if simplified
    simplify!(c)
  end

  if cached
    push!(Ac, c)
  end
  if (is_torsion_unit_group_known(k) || is_totally_real(k)) && c.Ka != k
    ok, gTk = _torsion_units_gen(k)
    expected = Int(_torsion_group_order_divisor(c.Ka))
    if expected == lcm(ok, n)
      #In this case, we know that the generator is the product.
      genTKa = c.mp[2](gTk)*(c.mp[1]\(gen(Kr)))
      set_attribute!(c.Ka, :torsion_units => (expected, genTKa))
    end
  end
  return c

end

@doc raw"""
    cyclotomic_extension(k::ClassField, n::Int) -> ClassField

Computes $k(\zeta_n)$, as a class field, as an extension of the same base field.
"""
function cyclotomic_extension(k::ClassField, n::Int; cached::Bool = true)
  return k*cyclotomic_extension(ClassField, base_ring(k), n)
end

function cyclotomic_extension(::Type{ClassField}, zk::AbsSimpleNumFieldOrder, n::Int; cached::Bool = true)
  c = cyclotomic_field(ClassField, n)
  k = nf(zk)
  r = ray_class_field(n*zk, real_places(k), n_quo = degree(c))
  h = norm_group_map(r, c, x->ideal(base_ring(c), norm(x)))
  return fixed_field(r, kernel(h)[1])
end

@doc raw"""
    cyclotomic_extension(ClassField, k::AbsSimpleNumField, n::Int) -> ClassField

Computes $k(\zeta_n)$, as a class field, as an extension of the same base field.
"""
function cyclotomic_extension(::Type{ClassField}, k::AbsSimpleNumField, n::Int; cached::Bool = true)
  return cyclotomic_extension(ClassField, maximal_order(k), n)
end

@doc raw"""
    fixed_field(A::ClassField, U::FinGenAbGroup)

For a subgroup $U$ of the norm group of $A$, return the class field fixed
by $U$, ie. norm group the quotient by $U$.
"""
function fixed_field(A::ClassField, s::FinGenAbGroup)
  mq = A.quotientmap
  q, mmq = quo(codomain(mq), s)
  return ray_class_field(A.rayclassgroupmap, mq*mmq)
end

function fixed_field(A::ClassField, s::Map{FinGenAbGroup, FinGenAbGroup})
  mq = A.quotientmap
  q, mmq = quo(codomain(mq), s)
  return ray_class_field(A.rayclassgroupmap, mq*mmq)
end


function compositum(k::AbsSimpleNumField, A::ClassField)
  c, mk, mA = compositum(k, base_field(A))
  return extend_base_field(A, mA)
end

function compositum(k::CyclotomicExt, A::ClassField)
  @assert k.k == base_field(A)
  mA = k.mp[2]
  return extend_base_field(A, mA)
end

function extend_base_field(A::ClassField, mA::Map; order=maximal_order(codomain(mA)))
  @assert base_field(A) == domain(mA)
  K = codomain(mA)
  ZK = order
  c, ci = conductor(A)
  C = induce_image(mA, c, target = ZK)
  if length(ci) > 0
    Ci = real_places(K) #TODO: don't need all....
  else
    Ci = InfPlc[]
  end
  R = ray_class_field(C, Ci, n_quo = exponent(A))
  h = norm_group_map(R, A, x->norm(mA, x, order = base_ring(A)))
  return fixed_field(R, kernel(h)[1])
end

function _isprobably_primitive(x::AbsNumFieldOrderElem)
  S = parent(x)
  OS = maximal_order(S)
  d = discriminant(OS)
  M, d1 = representation_matrix_q(x.elem_in_nf)
  p = next_prime(1000)
  for i = 1:3
    while is_divisible_by(d, p)[1] || is_divisible_by(d1, p)
      p = next_prime(p)
    end
    R = GF(p, cached = false)
    MR = map_entries(R, M)
    if degree(minpoly(MR)) == degree(S)
      return true
    end
  end
  return false
end

function _cyclotomic_extension_non_simple(k::AbsSimpleNumField, n::Int; cached::Bool = true)

  L, zeta = cyclotomic_field(n, cached = false)
  automorphism_list(L)
  OL = maximal_order(L)
  lOL = lll(OL)

  OK = maximal_order(k)
  lOK = lll(OK)

  S, mK, mL = number_field(k, L)
  BK = map(mK, basis(lOK, k))
  BL = map(mL, basis(lOL, L))
  BOS = product_basis(BK, BL)
  OS = AbsNumFieldOrder(BOS)
  OS.is_maximal = 1
  OS.disc = discriminant(OL)^(degree(k))*discriminant(OK)^(degree(L))
  set_attribute!(S, :maximal_order => OS)

  Zx = polynomial_ring(ZZ, "x")[1]
  prim_elems = elem_type(OS)[x for x in basis(OS) if _isprobably_primitive(x)]
  local poly::ZZPolyRingElem
  local poly2::ZZPolyRingElem
  if !isempty(prim_elems)
    #Now, I need to compare the elements and understand which is better.
    a = prim_elems[1]
    poly = minpoly(Zx, prim_elems[1])
    M = maximum([abs(coeff(poly, i)) for i = 0:degree(poly)-1])
    for i = 2:length(prim_elems)
      poly2 = minpoly(Zx, prim_elems[i])
      M2 = maximum([abs(coeff(poly2, i)) for i = 0:degree(poly2)-1])
      if M2 < M
        poly = poly2
        M = M2
        a = prim_elems[i]
      end
    end
  else
    a1 = S[1]+S[2]
    poly = minpoly(Zx, a1)
    while degree(poly) < degree(S)
      a1 += S[2]
      poly = minpoly(Zx, a1)
    end
    a = OS(a1)
  end
  Ka, gKa = number_field(poly, cached = false, check = false)

  kt, t = polynomial_ring(k, "t", cached = false)
  fL = L.pol(t)
  Kr, gKr = number_field(fL, check = false, cached = false)
  M = zero_matrix(QQ, degree(Ka), degree(Ka))
  z = one(S)
  elem_to_mat_row!(M, 1, z)
  elem_to_mat_row!(M, 2, elem_in_nf(a))
  mul!(z, z, elem_in_nf(a))
  for i=3:degree(Ka)
    mul!(z, z, elem_in_nf(a))
    elem_to_mat_row!(M, i, z)
  end
  N = zero_matrix(QQ, 2, degree(S))
  for i = 1:2
    elem_to_mat_row!(N, i, S[i])
  end
  s = solve(transpose(M), transpose(N); side = :right)
  b = basis(Ka)
  emb = Vector{typeof(b[1])}(undef, 2)
  for i = 1:2
    emb[i] = zero(Ka)
    for j = 1:degree(Ka)
      emb[i] += b[j] * s[j, i]
    end
  end
  abs2ns = hom(Ka, S, elem_in_nf(a), inverse = emb)

  BKa = Vector{AbsSimpleNumFieldElem}(undef, degree(Ka))
  for i = 1:length(BKa)
    BKa[i] = abs2ns\(BOS[i])
  end
  OKa = AbsSimpleNumFieldOrder(BKa)
  OKa.is_maximal = 1
  OKa.disc = OS.disc
  OKa.index = root(divexact(abs(numerator(discriminant(Ka))), abs(discriminant(OKa))), 2)
  lll(OKa)
  set_attribute!(Ka, :maximal_order => OKa)
  img_gen_k = abs2ns\(S[1])
  img_gen_Kr = abs2ns\(S[2])
  img_gen_Ka = evaluate(elem_in_nf(a).data, RelSimpleNumFieldElem{AbsSimpleNumFieldElem}[Kr(gen(k)), gKr])

  small2abs = hom(k, Ka, img_gen_k)
  abs2rel = hom(Ka, Kr, img_gen_Ka, inverse = (img_gen_k, img_gen_Kr))

  if is_torsion_unit_group_known(k) || is_totally_real(k)
    ok, gTk = _torsion_units_gen(k)
    expected = Int(_torsion_group_order_divisor(Ka))
    if expected == lcm(ok, n)
      #In this case, we know that the generator is the product.
      genTKa = small2abs(gTk)*img_gen_Kr
      set_attribute!(Ka, :torsion_units => (expected, genTKa))
    end
  end

  C = CyclotomicExt()
  C.kummer_exts = Dict{Set{ZZRingElem}, Tuple{Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, KummerExt}}()
  C.k = k
  C.n = n
  C.Ka = Ka
  C.Kr = Kr
  C.mp = (abs2rel, small2abs)
  if cached
    Ac = get_attribute!(() -> CyclotomicExt[], k, :cyclotomic_ext)::Vector{CyclotomicExt}
    push!(Ac, C)
  end
  return C

end




################################################################################
#
#  Automorphisms for cyclotomic extensions
#
################################################################################
@doc raw"""
    automorphism_list(C::CyclotomicExt; gens::Vector{NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}) -> Vector{NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}

Computes the automorphisms of the absolute field defined by the cyclotomic extension, i.e. of `absolute_simple_field(C).
It assumes that the base field is normal. `gens` must be a set of generators for the automorphism group of the base field of $C$.
"""
function automorphism_list(C::CyclotomicExt; gens::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}} = small_generating_set(automorphism_list(base_field(C))), copy::Bool = true)

  if degree(absolute_simple_field(C)) == degree(base_field(C)) || is_automorphisms_known(C.Ka)
    return automorphism_list(C.Ka, copy = copy)
  end
  genK = C.mp[1](gen(C.Ka))
  gnew = morphism_type(AbsSimpleNumField, AbsSimpleNumField)[]
  #First extend the old generators
  for g in gens
    ng = Hecke.extend_to_cyclotomic(C, g)
    na = hom(C.Ka, C.Ka, C.mp[1]\(ng(genK)), check = true)
    push!(gnew, na)
  end
  #Now add the automorphisms of the relative extension
  R = residue_ring(ZZ, C.n, cached = false)[1]
  U, mU = unit_group(R)
  if is_cyclic(U)
    k = degree(C.Kr)
    expo = divexact(euler_phi(ZZRingElem(C.n)), k)
    l = hom(C.Kr, C.Kr, gen(C.Kr)^Int(lift(mU(U[1])^expo)), check = true)
    l1 = hom(C.Ka, C.Ka, C.mp[1]\(l(C.mp[1](gen(C.Ka)))), check = true)
    push!(gnew, l1)
  else
    f = C.Kr.pol
    s, ms = sub(U, [x for x in U if iszero(f(gen(C.Kr)^Int(lift(mU(x)))))], false)
    S, mS = snf(s)
    for t = 1:ngens(S)
      l = hom(C.Kr, C.Kr, gen(C.Kr)^Int(lift(mU(ms(mS(S[t]))))), check = true)
      push!(gnew, hom(C.Ka, C.Ka, C.mp[1]\(l(genK)), check = true))
    end
  end
  auts = closure(gnew, degree(C.Ka))
  set_automorphisms(C.Ka, auts)
  if copy
    return Base.copy(auts)
  else
    return auts
  end

end

################################################################################
#
#  Cyclotomic fields as class fields
#
################################################################################

function show_cyclo(io::IO, C::ClassField)
  f = get_attribute(C, :cyclo)# ::Int #can be ZZRingElem/ is ZZRingElem
  print(io, "Cyclotomic field mod $f as a class field")
end

@doc raw"""
    cyclotomic_field(::Type{ClassField}, n::Int) -> ClassField

The $n$-th cyclotomic field as a `ray_class_field`
"""
function cyclotomic_field(::Type{ClassField}, n::Integer)
  return cyclotomic_field(ClassField, ZZRingElem(n))
end

function cyclotomic_field(::Type{ClassField}, n::ZZRingElem)
  Zx, x = polynomial_ring(ZZ, cached = false)
  QQ = rationals_as_number_field()[1]
  C = ray_class_field(n*maximal_order(QQ), infinite_places(QQ))
  set_attribute!(C, :cyclo => n, :show => show_cyclo)
  return C
end
