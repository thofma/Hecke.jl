export CyclotomicExt, cyclotomic_extension

################################################################################
#
#  Type definition
#
################################################################################
mutable struct CyclotomicExt
  k::AnticNumberField
  n::Int
  Kr::Hecke.NfRel{nf_elem}
  Ka::AnticNumberField
  mp::Tuple{NfToNfRel, NfToNfMor}

  kummer_exts::Dict{Set{fmpz}, Tuple{Vector{NfOrdIdl}, KummerExt}}
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

@doc Markdown.doc"""
    cyclotomic_extension(k::AnticNumberField, n::Int) -> CyclotomicExt

Computes $k(\zeta_n)$, in particular, a structure containing $k(\zeta_n)$
both as an absolute extension, as a relative extension (of $k$) and the maps
between them.
"""
function cyclotomic_extension(k::AnticNumberField, n::Int; cached::Bool = true, compute_maximal_order::Bool = true, compute_LLL_basis::Bool = true, simplified::Bool = true)
  if cached
    Ac = get_attribute!(() -> CyclotomicExt[], k, :cyclotomic_ext)::Vector{CyclotomicExt}
    for i = Ac
      if i.n == n
        return i
      end
    end
  end
  @assert n > 1

  kt, t = PolynomialRing(k, "t", cached = false)
  c = CyclotomicExt()
  c.kummer_exts = Dict{Set{fmpz}, Tuple{Vector{NfOrdIdl}, KummerExt}}()
  c.k = k
  c.n = n

  if n <= 2
    #Easy, just return the field
    Kr = number_field(t+1, cached = false, check = false)[1]
    if compute_maximal_order
      Ok = maximal_order(k)
      if compute_LLL_basis
        lll(Ok)
      end
    end
    abs2rel = hom(k, Kr, Kr(gen(k)), inverse = (gen(k), k(-1)))
    small2abs = id_hom(k)
    c.Kr = Kr
    c.Ka = k
    c.mp = (abs2rel, small2abs)
    if cached
      push!(Ac, c)
    end
    return c
  end

  ZX, X = PolynomialRing(FlintZZ, cached = false)
  f = cyclotomic(n, X)
  fk = change_base_ring(k, f, parent = kt)
  if n < 5
    #For n = 3, 4 the cyclotomic polynomial has degree 2,
    #so we can just ask for the roots.
    if !isone(gcd(degree(fk), degree(k))) && !is_totally_real(k)
      rt = _roots_hensel(fk, max_roots = 1, is_normal = true)
    else
      rt = nf_elem[]
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
        B_k = Vector{nf_elem}(undef, degree(Ka))
        for i = 1:length(b_k)
          B_k[i] = small2abs(b_k[i])
        end
        g = abs2rel\(Kr_gen)
        for j = 1:length(b_k)
          B_k[j+length(b_k)] = B_k[j]*g
        end
        ZKa = Hecke.NfOrd(B_k)
        ZKa.disc = discriminant(f)^degree(k)*discriminant(Zk)^degree(fk)
        ZKa.index = root(divexact(numerator(discriminant(Ka)), ZKa.disc), 2)
        ZKa.gen_index = fmpq(ZKa.index)
        for (p,v) = factor(gcd(discriminant(Zk), fmpz(n))).fac
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
      B_k = Vector{nf_elem}(undef, degree(Ka))
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
      ZKa = Hecke.NfOrd(B_k)
      if degree(Kr) == euler_phi(n)
        ZKa.disc = (discriminant(Zk)^euler_phi(n))*discriminant(f)^degree(k)
        ZKa.index = root(divexact(numerator(discriminant(Ka)), discriminant(ZKa)), 2)
        ZKa.gen_index = fmpz(ZKa.index)
      else
        ZKa.disc = (discriminant(Zk)^degree(Kr))*numerator(norm(discriminant(fk)))
        ZKa.index = root(divexact(numerator(discriminant(Ka)), discriminant(ZKa)), 2)
        ZKa.gen_index = fmpz(ZKa.index)
      end
      for (p, v) in factor(gcd(discriminant(Zk), fmpz(n)))
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

function _isprobably_primitive(x::NfAbsOrdElem)
  S = parent(x)
  OS = maximal_order(S)
  d = discriminant(OS)
  M, d1 = representation_matrix_q(x.elem_in_nf)
  p = next_prime(1000)
  for i = 1:3
    while divisible(d, p)[1] || divisible(d1, p)
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

function _cyclotomic_extension_non_simple(k::AnticNumberField, n::Int; cached::Bool = true)

  L, zeta = cyclotomic_field(n, cached = false)
  automorphisms(L)
  OL = maximal_order(L)
  lOL = lll(OL)

  OK = maximal_order(k)
  lOK = lll(OK)

  S, mK, mL = number_field(k, L)
  BK = map(mK, basis(lOK, k))
  BL = map(mL, basis(lOL, L))
  BOS = product_basis(BK, BL)
  OS = NfAbsOrd(BOS)
  OS.is_maximal = 1
  OS.disc = discriminant(OL)^(degree(k))*discriminant(OK)^(degree(L))
  set_attribute!(S, :maximal_order => OS)

  Zx = PolynomialRing(FlintZZ, "x")[1]
  prim_elems = elem_type(OS)[x for x in basis(OS) if _isprobably_primitive(x)]
  local poly::fmpz_poly
  local poly2::fmpz_poly
  if !isempty(prim_elems)
    #Now, I need to compare the elements and understand which is better.
    a = prim_elems[1]
    poly = minpoly(prim_elems[1], Zx)
    M = maximum([abs(coeff(poly, i)) for i = 0:degree(poly)-1])
    for i = 2:length(prim_elems)
      poly2 = minpoly(prim_elems[i], Zx)
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

  kt, t = PolynomialRing(k, "t", cached = false)
  fL = L.pol(t)
  Kr, gKr = number_field(fL, check = false, cached = false)
  M = zero_matrix(FlintQQ, degree(Ka), degree(Ka))
  z = one(S)
  elem_to_mat_row!(M, 1, z)
  elem_to_mat_row!(M, 2, elem_in_nf(a))
  mul!(z, z, elem_in_nf(a))
  for i=3:degree(Ka)
    mul!(z, z, elem_in_nf(a))
    elem_to_mat_row!(M, i, z)
  end
  N = zero_matrix(FlintQQ, 2, degree(S))
  for i = 1:2
    elem_to_mat_row!(N, i, S[i])
  end
  s = solve(transpose(M), transpose(N))
  b = basis(Ka)
  emb = Vector{typeof(b[1])}(undef, 2)
  for i = 1:2
    emb[i] = zero(Ka)
    for j = 1:degree(Ka)
      emb[i] += b[j] * s[j, i]
    end
  end
  abs2ns = hom(Ka, S, elem_in_nf(a), inverse = emb)

  BKa = Vector{nf_elem}(undef, degree(Ka))
  for i = 1:length(BKa)
    BKa[i] = abs2ns\(BOS[i])
  end
  OKa = NfOrd(BKa)
  OKa.is_maximal = 1
  OKa.disc = OS.disc
  OKa.index = root(divexact(abs(numerator(discriminant(Ka))), abs(discriminant(OKa))), 2)
  lll(OKa)
  set_attribute!(Ka, :maximal_order => OKa)
  img_gen_k = abs2ns\(S[1])
  img_gen_Kr = abs2ns\(S[2])
  img_gen_Ka = evaluate(elem_in_nf(a).data, NfRelElem{nf_elem}[Kr(gen(k)), gKr])

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
  C.kummer_exts = Dict{Set{fmpz}, Tuple{Vector{NfOrdIdl}, KummerExt}}()
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
@doc Markdown.doc"""
    automorphisms(C::CyclotomicExt; gens::Vector{NfToNfMor}) -> Vector{NfToNfMor}

Computes the automorphisms of the absolute field defined by the cyclotomic extension, i.e. of `absolute_simple_field(C).
It assumes that the base field is normal. `gens` must be a set of generators for the automorphism group of the base field of $C$.
"""
function automorphisms(C::CyclotomicExt; gens::Vector{NfToNfMor} = small_generating_set(automorphisms(base_field(C))), copy::Bool = true)

  if degree(absolute_simple_field(C)) == degree(base_field(C)) || is_automorphisms_known(C.Ka)
    return automorphisms(C.Ka, copy = copy)
  end
  genK = C.mp[1](gen(C.Ka))
  gnew = Hecke.NfToNfMor[]
  #First extend the old generators
  for g in gens
    ng = Hecke.extend_to_cyclotomic(C, g)
    na = hom(C.Ka, C.Ka, C.mp[1]\(ng(genK)), check = true)
    push!(gnew, na)
  end
  #Now add the automorphisms of the relative extension
  R = ResidueRing(FlintZZ, C.n, cached = false)
  U, mU = unit_group(R)
  if is_cyclic(U)
    k = degree(C.Kr)
    expo = divexact(euler_phi(fmpz(C.n)), k)
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
  f = get_attribute(C, :cyclo)
  print(io, "Cyclotomic field mod $f as a class field")
end

@doc Markdown.doc"""
    cyclotomic_field(::Type{ClassField}, n::Int) -> ClassField

The $n$-th cyclotomic field as a `ray_class_field`
"""
function cyclotomic_field(::Type{ClassField}, n::Integer)
  return cyclotomic_field(ClassField, fmpz(n))
end

function cyclotomic_field(::Type{ClassField}, n::fmpz)
  Zx, x = PolynomialRing(FlintZZ, cached = false)
  QQ = rationals_as_number_field()[1]
  C = ray_class_field(n*maximal_order(QQ), infinite_places(QQ))
  set_attribute!(C, :cyclo => n, :show => show_cyclo)
  return C
end
