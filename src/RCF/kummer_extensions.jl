abstract type AbelianExt end

mutable struct KummerExt <: AbelianExt
  zeta::nf_elem
  n::Int
  gen::Array{FacElem{nf_elem}, 1}

  AutG::GrpAbFinGen
  frob_cache::Dict{NfOrdIdl, GrpAbFinGenElem}

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

function kummer_extension(n::Int, gen::Array{FacElem{nf_elem, AnticNumberField}, 1})
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

function kummer_extension(exps::Array{Int, 1}, gens::Array{FacElem{nf_elem, AnticNumberField}, 1})
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
  kt, t = PolynomialRing(k, "t")
  return number_field([t^(Int(order(K.AutG[i])))- evaluate(K.gen[i]) for i=1:length(K.gen)])
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

  if nbits(minimum(p)) > 64
    error("Oops")
  end

  F, mF = ResidueFieldSmall(Zk, p)
  mF = extend_easy(mF, number_field(Zk))
  z_p = inv(mF(Zk(K.zeta)))

  # K = k(sqrt[n_i](gen[i]) for i=1:length(gen)), an automorphism will be
  # K[i] -> zeta^divexact(n, n_i) * ? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p

  aut = Array{fmpz, 1}(undef, length(K.gen))
  for j=1:length(K.gen)
    ord_genj = Int(order(K.AutG[j]))
    ex = div(norm(p)-1, ord_genj)
    mu = mF(K.gen[j])^ex  # can throw bad prime!
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

  if nbits(minimum(p)) > 64
    error("Oops")
  end

  F, mF = ResidueFieldSmall(Zk, p)
  mF = extend_easy(mF, number_field(Zk))

  #K = sqrt[n](gen), an automorphism will be
  # K[i] -> zeta^? K[i]
  # Frob(sqrt[n](a), p) = sqrt[n](a)^N(p) (mod p) = zeta^r sqrt[n](a)
  # sqrt[n](a)^N(p) = a^(N(p)-1 / n) = zeta^r mod p

  z_p = inv(mF(Zk(K.zeta)))
  @assert norm(p) % K.n == 1
  ex = div(norm(p)-1, K.n)

  mu = mF(g)^ex  # can throw bad prime!
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
