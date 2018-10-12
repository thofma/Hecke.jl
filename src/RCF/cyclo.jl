export CyclotomicExt, cyclotomic_extension

mutable struct CyclotomicExt
  k::AnticNumberField
  n::Int
  Kr::Hecke.NfRel
  Ka::AnticNumberField
  mp::Any
  function CyclotomicExt()
    return new()
  end
end

function Base.show(io::IO, c::CyclotomicExt)
  print(io, "Cyclotomic extension by zeta_$(c.n) of degree $(degree(c.Ka))")
end

@doc Markdown.doc"""
    cyclotomic_extension(k::AnticNumberField, n::Int) -> CyclotomicExt
> Computes $k(\zeta_n)$, in particular, a structure containing $k(\zeta_n)$
> both as an absolute extension, as a relative extension (of $k$) and the maps
> between them.
"""
function cyclotomic_extension(k::AnticNumberField, n::Int)
  Ac = CyclotomicExt[]
  try 
    Ac = Hecke._get_cyclotomic_ext_nf(k)
    for i = Ac
      if i.n == n
        return i::CyclotomicExt
      end
    end
  catch e
    if !(e isa AbstractAlgebra.AccessorNotSetError)
      rethrow(e)
    end
  end

  ZX, X = PolynomialRing(FlintZZ)
  Qx = parent(k.pol)
  kt, t = PolynomialRing(k, "t", cached = false)
  f = cyclotomic(n, X)
  fq = Qx(f)
  fk = evaluate(fq, t)
  lf = factor(fk)
  fk = first(keys(lf.fac))

  Kr, Kr_gen = number_field(fk, "z_$n", cached = false, check = false)
  if degree(fk) != 1
    Ka, rel2abs, small2abs = Hecke.absolute_field(Kr, false)
    
    # An equation order defined from a factor of a 
    # cyclotomic polynomial is always maximal by Dedekind
    # hence the product basis should be maximal at all primes except
    # for all p dividing the gcd()
    b_k = basis(maximal_order(k), k)
    B_k = [small2abs(x) for x = b_k]
    g = rel2abs(Kr_gen)
    for i = 1:degree(fk)-1
      for j = 1:degree(k)
        push!(B_k, B_k[j]*g^i)
      end
    end
    ZKa = Hecke.NfOrd(B_k)
    for (p,v) = factor(gcd(discriminant(maximal_order(k)), fmpz(n))).fac
      ZKa = pmaximal_overorder(ZKa, p)
    end
    ZKa.ismaximal = 1
    Hecke._set_maximal_order_of_nf(Ka, ZKa)
  else
    Ka = k
    rel2abs = NfRelToNf(Kr, Ka, gen(Ka), -coeff(fk, 0), Kr(gen(Ka)))
    small2abs = NfToNfMor(k, k, gen(k))
    ZKa = maximal_order(k)
  end
  #ZKa = lll(ZKa)

  
  c = CyclotomicExt()
  c.k = k
  c.n = n
  c.Kr = Kr
  c.Ka = Ka
  c.mp = (rel2abs, small2abs)

  push!(Ac, c)
  Hecke._set_cyclotomic_ext_nf(k, Ac)
  return c
  
end

