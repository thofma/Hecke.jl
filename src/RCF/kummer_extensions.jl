abstract type AbelianExt end

mutable struct KummerExt <: AbelianExt
  zeta::nf_elem
  n::Int
  gen::Vector{FacElem{nf_elem, AnticNumberField}}

  AutG::GrpAbFinGen
  frob_cache::Dict{NfOrdIdl, GrpAbFinGenElem}
  gen_mod_nth_power::Vector{FacElem{nf_elem, AnticNumberField}}
  eval_mod_nth::Vector{nf_elem}
  
  function KummerExt()
    return new()
  end
end

function Base.show(io::IO, K::KummerExt)
  if isdefined(K.AutG, :snf)
    print(io, "KummerExt with structure $(K.AutG.snf)")
  else
    print(io, "KummerExt with structure $([K.AutG.rels[i, i] for i=1:ngens(K.AutG)])")
  end
end

function kummer_extension(n::Int, gen::Vector{FacElem{nf_elem, AnticNumberField}})
  K = KummerExt()
  k = base_ring(gen[1])
  L = maximal_order(k)
  zeta, o = torsion_units_gen_order(L)
  @assert o % n == 0

  K.zeta = k(zeta)^div(o, n)
  K.n = n
  K.gen = gen
  K.AutG = GrpAbFinGen(fmpz[n for i=gen])
  K.frob_cache = Dict{NfOrdIdl, GrpAbFinGenElem}()
  return K
end

function kummer_extension(exps::Array{Int, 1}, gens::Vector{FacElem{nf_elem, AnticNumberField}})
  K = KummerExt()
  k = base_ring(gens[1])
  L = maximal_order(k)
  zeta, o = torsion_units_gen_order(L)
  n = lcm(exps)
  @assert o % n == 0

  K.zeta = k(zeta)^div(o, n)
  K.n = n
  K.gen = gens
  K.AutG = DiagonalGroup(exps)
  K.frob_cache = Dict{NfOrdIdl, GrpAbFinGenElem}()
  return K
end

function kummer_extension(n::Int, gen::Array{nf_elem, 1})
  g = [FacElem(x) for x=gen]
  return kummer_extension(n, g)
end

###############################################################################
#
#  Base Field
#
###############################################################################

function base_field(K::KummerExt)
  return base_ring(K.gen[1])
end

###############################################################################
#
#  Degree
#
###############################################################################

function degree(K::KummerExt)
  return Int(order(K.AutG))
end

###############################################################################
#
#  From Kummer Extension to Number Field
#
###############################################################################

function number_field(K::KummerExt)
  k = base_field(K)
  kt, t = PolynomialRing(k, "t", cached = false)
  pols = Array{typeof(t), 1}(undef, length(K.gen))
  for i = 1:length(pols)
    p = kt()
    setcoeff!(p, Int(order(K.AutG[i])), k(1))
    setcoeff!(p, 0, -evaluate(K.gen[i]))
    pols[i] = p
  end
  return number_field(pols, check = false, cached = false)
end

###############################################################################
#
#  Computation of Frobenius automorphisms
#
###############################################################################

mutable struct NfToFqMor_easy <: Map{AnticNumberField, FqNmodFiniteField, HeckeMap, NfToFqMor_easy}
  header::MapHeader
  Fq::FqNmodFiniteField
  s::fq_nmod
  t::gfp_poly
  function NfToFqMor_easy(a::Map, k::AnticNumberField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = PolynomialRing(GF(UInt(characteristic(r.Fq)), cached=false), cached=false)[1]()
    return r
  end
end

function image(mF::NfToFqMor_easy, a::FacElem{nf_elem, AnticNumberField}, quo::Int = 0)
  Fq = mF.Fq
  q = one(Fq)
  t = mF.t
  s = mF.s
  for (k,v) = a.fac
    vv = Int(v)
    if quo != 0
      vv = v %quo 
      if vv < 0
        vv += quo
      end
    end
    @assert vv < order(Fq)  #please complain if this is triggered
    if !iszero(vv)
      if denominator(k) % characteristic(Fq) == 0
        throw(BadPrime(characteristic(Fq)))
      end
      _nf_to_fq!(s, k, Fq, t)
      if iszero(s)
        throw(BadPrime(1))
      end
      if vv < 0
        ccall((:fq_nmod_inv, :libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Ref{FqNmodFiniteField}), s, s, Fq)
        vv = -vv
      end
      ccall((:fq_nmod_pow_ui, :libflint), Nothing, (Ref{fq_nmod}, Ref{fq_nmod}, Int, Ref{FqNmodFiniteField}), s, s, vv, Fq)
      mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToFqMor_easy, a::nf_elem)
  Fq = mF.Fq
  q = Fq()
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  _nf_to_fq!(q, a, Fq, mF.t)
  return q
end

# the Frobenius at p in K:
#K is an extension of k, p a prime in k,
#returns a vector in (Z/nZ)^r representing the Frob
function can_frobenius(p::NfOrdIdl, K::KummerExt)
  @assert norm(p) % K.n == 1
  if haskey(K.frob_cache, p)
    return K.frob_cache[p]
  end
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    #index divisors and residue class fields don't agree
    # ex: x^2-10, rcf of 29*Zk, 7. 239 is tricky...
    throw(BadPrime(p))
  end

  if nbits(minimum(p)) > 64
    error("Oops")
  end

  F, mF = ResidueFieldSmall(Zk, p)::Tuple{FqNmodFiniteField,NfOrdToFqNmodMor}
  #_mF = extend_easy(mF, number_field(Zk))
  mF = NfToFqMor_easy(mF, number_field(Zk))
  z_p = image(mF, K.zeta)^(K.n-1)

  # K = k(sqrt[n_i](gen[i]) for i=1:length(gen)), an automorphism will be
  # K[i] -> zeta^divexact(n, n_i) * ? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p

  aut = Array{fmpz, 1}(undef, length(K.gen))
  for j = 1:length(K.gen)
    ord_genj = Int(order(K.AutG[j]))
    ex = div(norm(p)-1, ord_genj)
    if isdefined(K, :gen_mod_nth_power)
      mu = image(mF, K.gen_mod_nth_power[j])^ex
    else
      mu = image(mF, K.gen[j], K.n)^ex  # can throw bad prime!
    end
    i = 0
    z_pj = z_p^divexact(K.n, ord_genj)
    while !isone(mu)
      i += 1
      @assert i <= K.n
      mul!(mu, mu, z_pj)
    end
    aut[j] = fmpz(i)
  end
  z = K.AutG(aut)
  K.frob_cache[p] = z
  return z
end

function can_frobenius1(p::NfOrdIdl, K::KummerExt)
  @assert norm(p) % K.n == 1
  if haskey(K.frob_cache, p)
    return K.frob_cache[p]
  end
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    #index divisors and residue class fields don't agree
    # ex: x^2-10, rcf of 29*Zk, 7. 239 is tricky...
    throw(BadPrime(p))
  end

  if nbits(minimum(p)) > 64
    error("Oops")
  end

  F, mF = ResidueFieldSmall(Zk, p)
  mF = NfToFqMor_easy(mF, number_field(Zk))
  #mF = extend_easy(mF, number_field(Zk))
  z_p = mF(K.zeta)^(K.n-1)

  # K = k(sqrt[n_i](gen[i]) for i=1:length(gen)), an automorphism will be
  # K[i] -> zeta^divexact(n, n_i) * ? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p
  ex = div(norm(p)-1, K.n)
  gens = Vector{fq_nmod}(undef, length(K.gen))
  for i = 1:length(K.gen)
    if isdefined(K, :eval_mod_nth)
      gens[i] = image(mF, K.eval_mod_nth[i])^ex
      if iszero(gens[i])
        throw(BadPrime(p))
      end
    elseif isdefined(K, :gen_mod_nth_power)
      gens[i] = image(mF, K.gen_mod_nth_power[i])^ex
    else
      gens[i] = image(mF, K.gen[i], K.n)^ex  # can throw bad prime!
    end
  end
  
  aut = Array{fmpz, 1}(undef, length(K.gen))
  for j = 1:length(K.gen)
    mu = gens[j]
    i = 0
    while !isone(mu)
      i += 1
      @assert i <= K.n
      mul!(mu, mu, z_p)
    end
    aut[j] = fmpz(i)
  end
  z = K.AutG(aut)
  K.frob_cache[p] = z
  return z
end


#In this function, we are computing the image of $sqrt[n](g) under the Frobenius automorphism of p
function can_frobenius(p::NfOrdIdl, K::KummerExt, g::FacElem{nf_elem})
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    #index divisors and residue class fields don't agree
    # ex: x^2-10, rcf of 29*Zk, 7. 239 is tricky...
    throw(BadPrime(p))
  end

  if nbits(minimum(p)) > 64
    error("Oops")
  end

  F, mF = ResidueFieldSmall(Zk, p)
  mF = extend_easy(mF, nf(Zk))

  #K = sqrt[n](gen), an automorphism will be
  # K[i] -> zeta^? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p

  z_p = inv(mF(K.zeta))
  @assert norm(p) % K.n == 1
  ex = div(norm(p)-1, K.n)

  mu = image(mF, g, K.n)^ex  # can throw bad prime!
  i = 0
  while true
    if isone(mu)
      break
    end
    i += 1
    @assert i <= K.n
    mul!(mu, mu, z_p)
  end
  return i
end
