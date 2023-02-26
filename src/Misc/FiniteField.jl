# additional constructors

function FlintFiniteField(p::Integer; cached::Bool = true)
  @assert is_prime(p)
  k = GF(p, cached=cached)
  return k, k(1)
end

function FlintFiniteField(p::ZZRingElem; cached::Bool = true)
  @assert is_prime(p)
  k = GF(p, cached=cached)
  return k, k(1)
end

GF(p::Integer, k::Int, s::Union{AbstractString,Symbol}=:o; cached::Bool = true) = FlintFiniteField(p, k, s, cached = cached)[1]
GF(p::ZZRingElem, k::Int, s::Union{AbstractString,Symbol}=:o; cached::Bool = true) = FlintFiniteField(p, k, s, cached = cached)[1]

##
## rand for Flint-Finite fields
##
## fqPolyRepFieldElem has no base ring
function rand(R::fqPolyRepField)
  #gen is not a generator for the group!
  r = R(0)
  for i=0:degree(R)
    r *= gen(R)
    r += rand(1:characteristic(R))
  end

  return r
end

function rand(R::FqPolyRepField)
  #gen is not a generator for the group!
  r = R(0)
  for i=0:degree(R)
    r *= gen(R)
    r += rand(1:characteristic(R))
  end

  return r
end

################################################################################
#
#  Iterators for finite fields
#
################################################################################

# fqPolyRepField

function Base.iterate(F::fqPolyRepField)
  return zero(F), zeros(UInt, degree(F))
end

function Base.iterate(F::fqPolyRepField, st::Vector{UInt})
  done = true
  for j in 1:length(st)
    if st[j] != F.n - 1
      done = false
    end
  end

  if done
    return nothing
  end

  st[1] = st[1] + 1
  for j in 1:(length(st) - 1)
    if st[j] == F.n
      st[j] = 0
      st[j + 1] = st[j + 1] + 1
    end
  end

  d = F()
  ccall((:fq_nmod_init2, libflint), Nothing,
        (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), d, F)
  for j in 1:length(st)
         ccall((:nmod_poly_set_coeff_ui, libflint), Nothing,
              (Ref{fqPolyRepFieldElem}, Int, UInt), d, j - 1, st[j])
  end

  return d, st
end

Base.length(F::fqPolyRepField) = BigInt(F.n)^degree(F)

Base.IteratorSize(::Type{fqPolyRepField}) = Base.HasLength()

Base.eltype(::fqPolyRepField) = fqPolyRepFieldElem

# FqPolyRepField

function Base.iterate(F::FqPolyRepField)
  return zero(F), zeros(FlintZZ, degree(F))
end

function Base.iterate(F::FqPolyRepField, st::Vector{ZZRingElem})
  done = true
  for j in 1:length(st)
    if st[j] != characteristic(F) - 1
      done = false
    end
  end

  if done
    return nothing
  end

  st[1] = st[1] + 1
  for j in 1:(length(st) - 1)
    if st[j] == characteristic(F)
      st[j] = 0
      st[j + 1] = st[j + 1] + 1
    end
  end

  d = F()
  ccall((:fq_init2, libflint), Nothing,
        (Ref{FqPolyRepFieldElem}, Ref{FqPolyRepField}), d, F)
  g = Hecke.Globals.Zx()
  for j in 1:length(st)
    #ccall((:fmpz_poly_set_coeff_fmpz, libflint), (Ref{ZZPolyRingElem}, Int, Ref{ZZRingElem}), g, j - 1, st[j])
    ccall((:fmpz_poly_set_coeff_fmpz, libflint), Nothing,
               (Ref{FqPolyRepFieldElem}, Int, Ref{ZZRingElem}), d, j - 1, st[j])
  end

  return d, st
end

Base.eltype(::FqPolyRepField) = FqPolyRepFieldElem

Base.length(F::FqPolyRepField) = BigInt(characteristic(F)^degree(F))

Base.IteratorSize(::Type{FqPolyRepField}) = Base.HasLength()

sub!(z::T, x::T, y::T) where {T} = x - y

function _reduce(a::fqPolyRepFieldElem)
  A = parent(a)
  if a.length < 2*degree(A)
    ccall((:fq_nmod_reduce, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), a, A)
  else
    ccall((:nmod_poly_rem, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Ref{Nothing}, Ref{Nothing}), a, a, pointer_from_objref(A)+6*sizeof(Int) + 2*sizeof(Ptr{Nothing}), pointer_from_objref(A)+sizeof(ZZRingElem))
  end
end

function _reduce(a::FqPolyRepFieldElem)
  A = parent(a)
  #if a.length < 2*degree(A)
    ccall((:fq_reduce, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FqPolyRepField}), a, A)
  #else
  #  ccall((:fmpz_mod_poly_rem, libflint), Nothing, (Ref{FqPolyRepFieldElem}, Ref{FqPolyRepFieldElem}, Ref{Nothing}, Ref{Nothing}), a, a, pointer_from_objref(A)+6*sizeof(Int) + 2*sizeof(Ptr{Nothing}), pointer_from_objref(A)+sizeof(ZZRingElem))
  #end
end

function (R::FqPolyRepField)(x::ZZModPolyRingElem)
  z = R()
  ccall((:fq_set_fmpz_mod_poly, libflint), Nothing, (Ref{Nemo.FqPolyRepFieldElem}, Ref{Nemo.ZZModPolyRingElem}, Ref{Nemo.FqPolyRepField}), z, x, R)
  #ccall((:fq_reduce, libflint), Nothing, (Ref{Nemo.FqPolyRepFieldElem}, Ref{Nemo.FqPolyRepField}), z, R)
  return z
end

function (R::FqPolyRepField)(x::FpPolyRingElem)
  z = R()
  ccall((:fq_set_fmpz_mod_poly, libflint), Nothing, (Ref{Nemo.FqPolyRepFieldElem}, Ref{Nemo.FpPolyRingElem}, Ref{Nemo.FqPolyRepField}), z, x, R)
  ccall((:fq_reduce, libflint), Nothing, (Ref{Nemo.FqPolyRepFieldElem}, Ref{Nemo.FqPolyRepField}), z, R)
  return z
end

#TODO: move elsewhere - and use. There are more calls to nmod_set/reduce
function (A::fqPolyRepField)(x::zzModPolyRingElem)
  u = A()
  ccall((:fq_nmod_set, libflint), Nothing,
                     (Ref{fqPolyRepFieldElem}, Ref{zzModPolyRingElem}, Ref{fqPolyRepField}),
                                     u, x, A)
  _reduce(u)
  return u
end

function (A::fqPolyRepField)(x::fpPolyRingElem)
  u = A()
  ccall((:fq_nmod_set, libflint), Nothing,
                     (Ref{fqPolyRepFieldElem}, Ref{fpPolyRingElem}, Ref{fqPolyRepField}),
                                     u, x, A)
  _reduce(u)
  return u
end

function _nf_to_fq!(a::fqPolyRepFieldElem, b::nf_elem, K::fqPolyRepField, a_tmp::zzModPolyRingElem)
  nf_elem_to_nmod_poly!(a_tmp, b)
  ccall((:fq_nmod_set, libflint), Nothing,
                     (Ref{fqPolyRepFieldElem}, Ref{zzModPolyRingElem}, Ref{fqPolyRepField}),
                                     a, a_tmp, K)
  _reduce(a)
end

function _nf_to_fq!(a::fqPolyRepFieldElem, b::nf_elem, K::fqPolyRepField, a_tmp::fpPolyRingElem)
  nf_elem_to_gfp_poly!(a_tmp, b)
  ccall((:fq_nmod_set, libflint), Nothing,
                     (Ref{fqPolyRepFieldElem}, Ref{fpPolyRingElem}, Ref{fqPolyRepField}),
                                     a, a_tmp, K)
  _reduce(a)
end

function _nf_to_fq!(a::FqPolyRepFieldElem, b::nf_elem, K::FqPolyRepField, a_tmp::FpPolyRingElem)
  nf_elem_to_gfp_fmpz_poly!(a_tmp, b)
  ccall((:fq_set, libflint), Nothing,
                     (Ref{FqPolyRepFieldElem}, Ref{FpPolyRingElem}, Ref{FqPolyRepField}),
                                     a, a_tmp, K)
  _reduce(a)
end

function _nf_to_fq!(a::FqFieldElem, b::nf_elem, K::FqField)#, a_tmp::FpPolyRingElem)
  # nf_elem -> fmpq_poly
  z = fmpq_poly()
  ccall((:nf_elem_get_fmpq_poly, libantic), Nothing,
        (Ref{QQPolyRingElem}, Ref{nf_elem}, Ref{AnticNumberField}), z, b, parent(b))
  z.parent = Globals.Qx
  # fmpq_poly -> fmpz_poly, fmpz
  zz = fmpz_poly()
  ccall((:fmpq_poly_get_numerator, libflint), Nothing, (Ref{ZZPolyRingElem}, Ref{QQPolyRingElem}), zz, z)
  zz.parent = Globals.Zx
  zzz = fmpz()
  ccall((:fmpq_poly_get_denominator, libflint), Nothing, (Ref{ZZRingElem}, Ref{QQPolyRingElem}), zzz, z)
  ccall((:fq_default_set_fmpz_poly, libflint), Nothing, (Ref{FqFieldElem}, Ref{ZZPolyRingElem}, Ref{FqField}), a, zz, K)
  # invert the denominator
  c = characteristic(K)
  ccall((:fmpz_invmod, libflint), Cint,
        (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), zzz, zzz, c)
  ccall((:fq_default_mul_fmpz, libflint), Nothing, (Ref{FqFieldElem}, Ref{FqFieldElem}, Ref{fmpz}, Ref{FqField}), a, a, zzz, K)
    #ccall((:fq_set, libflint), Nothing,
  #                   (Ref{FqPolyRepFieldElem}, Ref{FpPolyRingElem}, Ref{FqPolyRepField}),
  #                                   a, a_tmp, K)
  #_reduce(a)
  return a
end

function (A::fqPolyRepField)(x::fpFieldElem)
  @assert characteristic(A) == characteristic(parent(x))
  return A(lift(x))
end

function (A::FqPolyRepField)(x::Generic.ResF{ZZRingElem})
  @assert characteristic(A) == characteristic(parent(x))
  return A(lift(x))
end

Nemo.promote_rule(::Type{fqPolyRepFieldElem}, ::Type{fpFieldElem}) = fqPolyRepFieldElem

Nemo.promote_rule(::Type{FqPolyRepFieldElem}, ::Type{FpFieldElem}) = FqPolyRepFieldElem

################################################################################
#
#  Primitive roots in finite fields
#
################################################################################

# This is not used anywhere
function has_primitive_root_1(K::Nemo.fqPolyRepField, m::Int)
  @assert m > 0
  if m == 1
    return K(1)
  end
  if size(K) % m != 1
    return false, K(1)
  end
  if m == 2
    return K(-1)
  end
  fm = factor(m)
  while true
    g = rand(K)
    if iszero(g)
      continue
    end
    if any(x -> isone(g^div(m, x)), keys(fm))
      continue
    end
    return true, g^div(size(K)-1, m)
  end
end


## Minpoly/ Charpoly

function minpoly(a::fqPolyRepFieldElem)
  return minpoly(polynomial_ring(GF(Int(characteristic(parent(a))), cached = false), cached = false)[1], a)
end

function minpoly(Rx::fpPolyRing, a::fqPolyRepFieldElem)
  c = [a]
  fa = frobenius(a)
  while !(fa in c)
    push!(c, fa)
    fa = frobenius(fa)
  end
  St = polynomial_ring(parent(a), cached = false)[1]
  f = prod([gen(St) - x for x = c], init = one(St))
  g = Rx()
  for i = 0:degree(f)
    setcoeff!(g, i, coeff(coeff(f, i), 0))
  end
  return g
end

function charpoly(a::fqPolyRepFieldElem)
  return charpoly(polynomial_ring(GF(Int(characteristic(parent(a))), cached = false), cached = false)[1], a)
end

function charpoly(Rx::fpPolyRing, a::fqPolyRepFieldElem)
  g = minpoly(Rx, a)
  return g^div(degree(parent(a)), degree(g))
end


function minpoly(a::FqPolyRepFieldElem)
  return minpoly(polynomial_ring(GF(characteristic(parent(a)), cached = false), cached = false)[1], a)
end

function minpoly(Rx::FpPolyRing, a::FqPolyRepFieldElem)
  c = [a]
  fa = frobenius(a)
  while !(fa in c)
    push!(c, fa)
    fa = frobenius(fa)
  end
  St = polynomial_ring(parent(a), cached = false)[1]
  f = prod([gen(St) - x for x = c])
  g = Rx()
  for i = 0:degree(f)
    setcoeff!(g, i, coeff(coeff(f, i), 0))
  end
  return g
end

################################################################################
#
#  Generators multiplicative group
#
################################################################################

function primitive_element(F::T; n_quo::Int = -1) where T <: Union{FqPolyRepField, fqPolyRepField, fpField, Nemo.FpField, FqField}
  n = order(F)-1
  k = ZZRingElem(1)
  if n_quo != -1
    if !divisible(n, n_quo)
      return F(1)
    end
    n, k = ppio(n, ZZRingElem(n_quo))
  end
  primefactors_n = collect(keys(factor(n).fac))

  x = rand(F)^k
  while iszero(x)
    x = rand(F)^k
  end
  while true
    found = true
    for l in primefactors_n
      if isone(x^div(n, l))
        found = false
        break
      end
    end
    if found
      break
    end
    x = rand(F)^k
    while iszero(x)
      x = rand(F)^k
    end
  end
  return x
end


function unit_group(F::T; n_quo::Int = -1) where T <: FinField

  g = primitive_element(F, n_quo = n_quo)
  k = order(F) - 1
  inv = ZZRingElem(1)
  npart = ZZRingElem(k)
  if n_quo != -1
    k = ZZRingElem(n_quo)
    npart, nnpart = ppio(order(F) - 1, k)
    inv = invmod(nnpart, npart)
  end

  G = abelian_group(Int[k])
  ex = div(order(F) - 1, npart)
  function disc_log(x)
    @assert typeof(x) == elem_type(F)
    iszero(x) && error("Not invertible!")
    y = x^ex
    isone(y) && return G[0]
    if k < 20
      c = 1
      el = deepcopy(g)
      while el != y
        c += 1
        if c > npart
          error("Something went wrong!")
        end
        el *= g
      end
      return G([mod(c*inv, k)])
    else
      return G([mod(inv*disc_log_bs_gs(g, y, npart), k)])
    end
  end
  mG = FiniteFieldMultGrpMap{T, elem_type(F)}(G, F, g, disc_log)
  return G, mG
end

################################################################################
#
#  Missing ad hoc operations
#
################################################################################

function (R::FqPolyRepField)(x::Nemo.FpFieldElem)
  return R(lift(x))
end

function *(a::Nemo.FqPolyRepFieldElem, b::Nemo.FpFieldElem)
  return a * parent(a)(b)
end

function *(a::Nemo.FpFieldElem, b::Nemo.FqPolyRepFieldElem)
  return parent(b)(a) * b
end
function Hecke.preimage(phi::Nemo.FinFieldMorphism, x::FinFieldElem)
  return preimage_map(phi)(x)
end

function (R::Nemo.zzModRing)(a::Nemo.fpFieldElem)
  @assert modulus(R) == characteristic(parent(a))
  return R(data(a))
end

function (k::Nemo.fqPolyRepField)(a::QQFieldElem)
  return k(numerator(a))//k(denominator(a))
end

function (k::Nemo.FpField)(a::QQFieldElem)
  return k(numerator(a))//k(denominator(a))
end

function (k::Nemo.FqPolyRepField)(a::QQFieldElem)
  return k(numerator(a))//k(denominator(a))
end


(F::Nemo.fqPolyRepField)(a::Nemo.zzModRingElem) = F(a.data)

#to avoid using embed - which is (more me) still broken..
# it accumulates fields until the machine dies
function find_morphism(k::Nemo.zzModRing, K::fqPolyRepField)
  return x->K(x.data)
end

function find_morphism(k::fqPolyRepField, K::fqPolyRepField)
   if degree(k) > 1
    phi = Nemo.find_morphism(k, K) #avoids embed - which stores the info
  else
    phi = MapFromFunc(x->K((coeff(x, 0))), y->k((coeff(y, 0))), k, K)
  end
  return phi
end

#TODO/ think: 
# - should those be zzModMatrix of fpMatrix
# - base_ring/ coeff_field needs to be unique?
function representation_matrix(a::fpFieldElem)
  return matrix(parent(a), 1, 1, [a])
end

function representation_matrix(a::fqPolyRepFieldElem)
  F = parent(a)
  k = quo(ZZ, Int(characteristic(F)))[1]
  k = GF(Int(characteristic(F)))
  m = zero_matrix(k, degree(F), degree(F))
  ccall((:fq_nmod_embed_mul_matrix, libflint), Nothing, (Ref{fpMatrix}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}), m, a, F)
  ccall((:nmod_mat_transpose, libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), m, m)
  return m
end

function frobenius_matrix(F::fqPolyRepField, n::Int=1)
  a = frobenius(gen(F), n)
  k = quo(ZZ, Int(characteristic(F)))[1]
  k = GF(Int(characteristic(F)))
  m = zero_matrix(k, degree(F), degree(F))
  ccall((:fq_nmod_embed_composition_matrix_sub, libflint), Nothing, (Ref{fpMatrix}, Ref{fqPolyRepFieldElem}, Ref{fqPolyRepField}, Int), m, a, F, degree(F))
  ccall((:nmod_mat_transpose, libflint), Nothing, (Ref{fpMatrix}, Ref{fpMatrix}), m, m)
  return m
end

mutable struct VeryBad
  entries::Ptr{Nothing}
  r::Int
  c::Int
  rows::Ptr{Nothing}
  n::UInt
  ninv::UInt
  norm::UInt

  function VeryBad(n, ninv, norm)
    r = new()
    r.n = n
    r.ninv = ninv
    r.norm = norm
    r.r = 1
    r.rr = [reinterpret(Ptr{Nothing}, 0)]
    r.rows = Base.unsafe_convert(Ptr{Nothing}, r.rr)
    return r
  end

  rr::Vector{Ptr{Nothing}}
end

function VeryBad!(V::VeryBad, a::fqPolyRepFieldElem)
  V.c = a.length
  V.entries = a.coeffs
  V.rr[1] = a.coeffs
#  V.rows = Base.unsafe_convert(Ptr{Nothing}, [a.coeffs])
end

function clear!(V::VeryBad)
  V.entries = reinterpret(Ptr{Nothing}, 0)
#  V.rows = reinterpret(Ptr{Nothing}, 0)
end

struct FrobeniusCtx
  m::fpMatrix
  fa::VeryBad
  fb::VeryBad
  K::fqPolyRepField
  i::Int

  function FrobeniusCtx(K::fqPolyRepField, i::Int = 1)
    m = frobenius_matrix(K, i)
    return new(m, VeryBad(m.n, m.ninv, m.norm), VeryBad(m.n, m.ninv, m.norm), K, i)
  end
end

function show(io::IO, F::FrobeniusCtx)
  println(io, "$(F.i)-th Frobenius data for $(F.K)")
end

function apply!(b::fqPolyRepFieldElem, a::fqPolyRepFieldElem, F::FrobeniusCtx)
  n = degree(parent(a))
  ccall((:nmod_poly_fit_length, libflint), Nothing, (Ref{fqPolyRepFieldElem}, Int), b, n)
  VeryBad!(F.fa, a)
  VeryBad!(F.fb, b)
  ccall((:nmod_mat_mul, libflint), Nothing, (Ref{VeryBad}, Ref{VeryBad}, Ref{zzModMatrix}), F.fb, F.fa, F.m)
  b.length = n
  clear!(F.fa)
  clear!(F.fb)
  ccall((:_nmod_poly_normalise, libflint), Nothing, (Ref{fqPolyRepFieldElem}, ), b)
  return b
end

function frobenius!(a::fqPolyRepFieldElem, b::fqPolyRepFieldElem, i::Int = 1)
    ccall((:fq_nmod_frobenius, libflint), Nothing,
         (Ref{fqPolyRepFieldElem}, Ref{fqPolyRepFieldElem}, Int, Ref{fqPolyRepField}),
                                               a, b, i, a.parent)
end

################################################################################
#
#  Defining polynomial for finite fields
#
################################################################################

defining_polynomial(F::FqPolyRepField) = minpoly(gen(F))

function defining_polynomial(Q::fqPolyRepField, P::Ring = GF(Int(characteristic(Q)), cached = false))
  Pt, t = polynomial_ring(P, cached = false)
  f = Pt()
  for i=0:Q.len-1
    j = unsafe_load(reinterpret(Ptr{Int}, Q.j), i+1)
    a = ZZRingElem()
    ccall((:fmpz_set, libflint), Nothing, (Ref{ZZRingElem}, Int64), a, Q.a+i*sizeof(Ptr))
    setcoeff!(f, j, P(a))
  end
  return f
end
