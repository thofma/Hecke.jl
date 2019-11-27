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

################################################################################
#
#  Interface and creation
#
################################################################################

@doc Markdown.doc"""
    cyclotomic_extension(k::AnticNumberField, n::Int) -> CyclotomicExt
Computes $k(\zeta_n)$, in particular, a structure containing $k(\zeta_n)$
both as an absolute extension, as a relative extension (of $k$) and the maps
between them.
"""
function cyclotomic_extension(k::AnticNumberField, n::Int; cached::Bool = true,  compute_maximal_order::Bool = true, compute_LLL_basis::Bool = true)
  Ac = CyclotomicExt[]
  if cached
    try 
      Ac = Hecke._get_cyclotomic_ext_nf(k)::Vector{CyclotomicExt}
      for i = Ac
        if i.n == n
          return i
        end
      end
    catch e
      if !(e isa AbstractAlgebra.AccessorNotSetError)
        rethrow(e)
      end
    end
  end
  
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
    abs2rel = NfToNfRel(k, Kr, gen(k), k(-1), Kr(gen(k)))
    small2abs = id_hom(k)
    c.Kr = Kr
    c.Ka = k
    c.mp = (abs2rel, small2abs)
    if cached
      push!(Ac, c)
      Hecke._set_cyclotomic_ext_nf(k, Ac)
    end
    return c
  end
  
  ZX, X = PolynomialRing(FlintZZ, cached = false)
  f = cyclotomic(n, X)
  fk = change_ring(f, kt)
  if n < 5
    #For n = 3, 4 the cyclotomic polynomial has degree 2,
    #so we can just ask for the roots.
    if !isone(gcd(degree(fk), degree(k))) && !isone(gcd(discriminant(maximal_order(k)), n)) && !istotally_real(k)  
      rt = _roots_hensel(fk, max_roots = 1, isnormal = true)
    else
      rt = nf_elem[]
    end
    if length(rt) == 1
      #The polynomial splits completely!
      Kr, gKr = number_field(t - rt[1], cached = false, check = false)
      abs2rel = NfToNfRel(k, Kr, gen(k), rt[1], Kr(gen(k)))
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
      Ka, abs2rel, small2abs = Hecke.absolute_field(Kr, false)
      if compute_maximal_order
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
        ZKa.ismaximal = 1
        if compute_LLL_basis
          ZKa = lll(ZKa)
        end
        Hecke._set_maximal_order_of_nf(Ka, ZKa)
      end
      c.Kr = Kr
      c.Ka = Ka
      c.mp = (abs2rel, small2abs)
    end
    if cached
      push!(Ac, c)
      Hecke._set_cyclotomic_ext_nf(k, Ac)
    end
    return c
  end
   
  if gcd(degree(fk), degree(k)) != 1 && !isone(gcd(discriminant(maximal_order(k)), n))
    lf = factor(fk)
    fk = first(keys(lf.fac))
  end

  Kr, Kr_gen = number_field(fk, "z_$n", cached = false, check = false)
  if degree(fk) != 1
    Ka, abs2rel, small2abs = Hecke.absolute_field(Kr, false)
    
    if compute_maximal_order
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
      for (p, v) in factor(gcd(discriminant(Zk), fmpz(n)))
        ZKa = pmaximal_overorder_at(ZKa, [p])
      end
      if compute_LLL_basis
        ZKa = lll(ZKa)
      end
      ZKa.ismaximal = 1
      Hecke._set_maximal_order_of_nf(Ka, ZKa)
    end
  else
    Ka = k
    abs2rel = NfToNfRel(Ka, Kr, gen(Ka), -coeff(fk, 0), Kr(gen(Ka)))
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
  if cached
    push!(Ac, c)
    Hecke._set_cyclotomic_ext_nf(k, Ac)
  end
  return c
  
end

absolute_field(C::CyclotomicExt) = C.Ka
base_field(C::CyclotomicExt) = C.k

################################################################################
#
#  Automorphisms for cyclotomic extensions
#
################################################################################
@doc Markdown.doc"""
    automorphisms(C::CyclotomicExt; gens::Vector{NfToNfMor}) -> Vector{NfToNfMor}
Computes the automorphisms of the absolute field defined by the cyclotomic extension, i.e. of absolute_field(C).
It assumes that the base field is normal. gens must be a set of generators for the automorphism group of the base field of C
"""
function automorphisms(C::CyclotomicExt; gens::Vector{NfToNfMor} = small_generating_set(automorphisms(base_field(C))), copy::Bool = true)

  if degree(absolute_field(C)) == degree(base_field(C))
    return automorphisms(C.Ka, copy = copy)
  end
  genK = C.mp[1](gen(C.Ka))
  gnew = Hecke.NfToNfMor[]
  #First extend the old generators
  for g in gens
    ng = Hecke.extend_to_cyclotomic(C, g)
    na = hom(C.Ka, C.Ka, C.mp[1]\(ng(genK)), check = false)
    push!(gnew, na)
  end 
  #Now add the automorphisms of the relative extension
  R = ResidueRing(FlintZZ, C.n, cached = false)
  U, mU = unit_group(R)
  if iscyclic(U)
    k = degree(C.Kr)
    expo = divexact(eulerphi(fmpz(C.n)), k)
    l = hom(C.Kr, C.Kr, gen(C.Kr)^Int(lift(mU(U[1])^expo)), check = false)
    l1 = hom(C.Ka, C.Ka, C.mp[1]\(l(C.mp[1](gen(C.Ka)))), check = false)
    push!(gnew, l1)
  else
    f = C.Kr.pol
    s, ms = sub(U, [x for x in U if iszero(f(gen(C.Kr)^Int(lift(mU(x)))))], false)
    S, mS = snf(s)
    for t = 1:ngens(S)
      l = hom(C.Kr, C.Kr, gen(C.Kr)^Int(lift(mU(ms(mS(S[t]))))), check = false)
      push!(gnew, hom(C.Ka, C.Ka, C.mp[1]\(l(genK)), check = false))
    end
  end
  auts = closure(gnew, degree(C.Ka))
  Hecke._set_automorphisms_nf(C.Ka, auts)
  if copy
    return Base.copy(auts)
  else
    return auts
  end

end
