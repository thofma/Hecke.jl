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

function cyclotomic_extension(k::AnticNumberField, n::Int)
  Ac = CyclotomicExt[]
  try 
    Ac = Hecke._get_cyclotomic_ext_nf(k)
    for i = Ac
      if i.n == n
        return i
      end
    end
  catch e
    if e != Nemo.AccessorNotSetError()
      rethrow(e)
    end
  end

  ZX, X = PolynomialRing(FlintZZ)
  Qx = parent(k.pol)
  kt, t = PolynomialRing(k, "t")
  f = cyclotomic(n, X)
  fq = Qx(f)
  fk = evaluate(fq, t)
  lf = factor(fk)
  fk = first(keys(lf.fac))

  Kr, Kr_gen = number_field(fk, "z_$n")
  Ka, rel2abs, small2abs = Hecke.absolute_field(Kr)

  c = CyclotomicExt()
  c.k = k
  c.n = n
  c.Kr = Kr
  c.Ka = Ka
  c.mp = (rel2abs, small2abs)
 
  b_k = basis(maximal_order(k), k)
  B_k = [small2abs(x) for x = b_k]
  g = rel2abs(Kr_gen)
  for i=1:degree(fk)-1
    for j=1:degree(k)
      push!(B_k, B_k[j]*g^i)
    end
  end

  # we argued that an equation order defined from a factor of a 
  # cyclotomic polynomial should always be maximal by Dedekind
  # hence the product basis should be maximal...
  # we can later implement proper relative maximal orders
  # wrong! for Q(sqrt(10))(zeta_5) this is not 5 maximal.
  # so we need to become p-maximal for all p dividing the gcd()

  ZKa = Hecke.NfOrd(B_k)
  for (p,v) = factor(gcd(discriminant(maximal_order(k)), fmpz(n))).fac
    ZKa = pmaximal_overorder(ZKa, p)
  end
  ZKa = lll(ZKa)
  ZKa.ismaximal = 1
  Hecke._set_maximal_order_of_nf(Ka, ZKa)
  push!(Ac, c)
  Hecke._set_cyclotomic_ext_nf(k, Ac)
  return c
end

