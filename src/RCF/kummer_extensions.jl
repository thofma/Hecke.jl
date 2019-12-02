abstract type AbelianExt end

mutable struct KummerExt <: AbelianExt
  zeta::nf_elem
  n::Int
  gen::Vector{FacElem{nf_elem, AnticNumberField}}

  AutG::GrpAbFinGen
  frob_cache::Dict{NfOrdIdl, GrpAbFinGenElem}
  frob_gens::Tuple{Vector{NfOrdIdl}, Vector{GrpAbFinGenElem}}
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
  kt = PolynomialRing(k, "t", cached = false)[1]
  pols = Array{elem_type(kt), 1}(undef, length(K.gen))
  for i = 1:length(pols)
    p = Vector{nf_elem}(undef, Int(order(K.AutG[i]))+1)
    p[1] = -evaluate(K.gen[i])
    for i = 2:Int(order(K.AutG[i]))
      p[i] = zero(k)
    end 
    p[end] = one(k)
    pols[i] = kt(p)
  end
  return number_field(pols, check = false, cached = false)
end

################################################################################
#
#  Extension of residue field map to localization
#
################################################################################

mutable struct NfToFqMor_easy <: Map{AnticNumberField, FqFiniteField, HeckeMap, NfToFqMor_easy}
  header::MapHeader
  Fq::FqFiniteField
  s::fq
  t::gfp_fmpz_poly
  function NfToFqMor_easy(a::Map, k::AnticNumberField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = PolynomialRing(GF(characteristic(r.Fq), cached = false), cached = false)[1]()
    return r
  end
end

function image(mF::NfToFqMor_easy, a::FacElem{nf_elem, AnticNumberField}, quo::Int = 0)
  Fq = mF.Fq
  q = one(Fq)
  t = mF.t
  s = mF.s
  for (k, v) = a.fac
    vv = v
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
        ccall((:fq_inv, :libflint), Nothing, (Ref{fq}, Ref{fq}, Ref{FqFiniteField}), s, s, Fq)
        vv = -vv
      end
      ccall((:fq_pow_ui, :libflint), Nothing, (Ref{fq}, Ref{fq}, Int, Ref{FqFiniteField}), s, s, vv, Fq)
      mul!(q, q, s)
    end
  end
  return q
end

function image(mF::NfToFqMor_easy, a::nf_elem, n_quo::Int = 0)
  Fq = mF.Fq
  q = Fq()
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  _nf_to_fq!(q, a, Fq, mF.t)
  return q
end


mutable struct NfToFqNmodMor_easy <: Map{AnticNumberField, FqNmodFiniteField, HeckeMap, NfToFqNmodMor_easy}
  header::MapHeader
  Fq::FqNmodFiniteField
  s::fq_nmod
  t::gfp_poly
  function NfToFqNmodMor_easy(a::Map, k::AnticNumberField)
    r = new()
    r.Fq = codomain(a)
    r.header = MapHeader(k, r.Fq)
    r.s = r.Fq()
    r.t = PolynomialRing(GF(UInt(characteristic(r.Fq)), cached=false), cached=false)[1]()
    return r
  end
end

function image(mF::NfToFqNmodMor_easy, a::FacElem{nf_elem, AnticNumberField}, quo::Int = 0)
  Fq = mF.Fq
  q = one(Fq)
  t = mF.t
  s = mF.s
  for (k, v) = a.fac
    vv = v
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

function image(mF::NfToFqNmodMor_easy, a::nf_elem, n_quo::Int = 0)
  Fq = mF.Fq
  q = Fq()
  if denominator(a) % characteristic(Fq) == 0
    throw(BadPrime(characteristic(Fq)))
  end
  _nf_to_fq!(q, a, Fq, mF.t)
  return q
end

###############################################################################
#
#  Computation of Frobenius automorphisms
#
###############################################################################

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
  if !fits(Int, minimum(p, copy = false))
    return can_frobenius_fmpz(p, K)
  end

  F, mF = ResidueFieldSmall(Zk, p)::Tuple{FqNmodFiniteField,NfOrdToFqNmodMor}
  #_mF = extend_easy(mF, number_field(Zk))
  mF = NfToFqNmodMor_easy(mF, number_field(Zk))
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

function can_frobenius_fmpz(p::NfOrdIdl, K::KummerExt)
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


  F, mF = ResidueField(Zk, p)
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

#In this function, we are computing the image of $sqrt[n](g) under the Frobenius automorphism of p
function can_frobenius(p::NfOrdIdl, K::KummerExt, g::FacElem{nf_elem})
  Zk = order(p)
  if index(Zk) % minimum(p) == 0 
    #index divisors and residue class fields don't agree
    # ex: x^2-10, rcf of 29*Zk, 7. 239 is tricky...
    throw(BadPrime(p))
  end

  if !fits(Int, minimum(p, copy = false))
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
