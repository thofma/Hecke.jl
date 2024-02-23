
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

function _nf_to_fq!(a::fqPolyRepFieldElem, b::AbsSimpleNumFieldElem, K::fqPolyRepField, a_tmp::zzModPolyRingElem)
  Nemo.nf_elem_to_nmod_poly!(a_tmp, b)
  ccall((:fq_nmod_set, libflint), Nothing,
                     (Ref{fqPolyRepFieldElem}, Ref{zzModPolyRingElem}, Ref{fqPolyRepField}),
                                     a, a_tmp, K)
  _reduce(a)
end

function _nf_to_fq!(a::fqPolyRepFieldElem, b::AbsSimpleNumFieldElem, K::fqPolyRepField, a_tmp::fpPolyRingElem)
  Nemo.nf_elem_to_gfp_poly!(a_tmp, b)
  ccall((:fq_nmod_set, libflint), Nothing,
                     (Ref{fqPolyRepFieldElem}, Ref{fpPolyRingElem}, Ref{fqPolyRepField}),
                                     a, a_tmp, K)
  _reduce(a)
end

function _nf_to_fq!(a::FqPolyRepFieldElem, b::AbsSimpleNumFieldElem, K::FqPolyRepField, a_tmp::FpPolyRingElem)
  Nemo.nf_elem_to_gfp_fmpz_poly!(a_tmp, b)
  ccall((:fq_set, libflint), Nothing,
                     (Ref{FqPolyRepFieldElem}, Ref{FpPolyRingElem}, Ref{FqPolyRepField}),
                                     a, a_tmp, K)
  _reduce(a)
end

function _nf_to_fq!(a::FqFieldElem, b::AbsSimpleNumFieldElem, K::FqField)#, a_tmp::FpPolyRingElem)
  # AbsSimpleNumFieldElem -> QQPolyRingElem
  z = QQPolyRingElem()
  ccall((:nf_elem_get_fmpq_poly, libantic), Nothing,
        (Ref{QQPolyRingElem}, Ref{AbsSimpleNumFieldElem}, Ref{AbsSimpleNumField}), z, b, parent(b))
  z.parent = Globals.Qx
  # QQPolyRingElem -> ZZPolyRingElem, ZZRingElem
  zz = ZZPolyRingElem()
  ccall((:fmpq_poly_get_numerator, libflint), Nothing, (Ref{ZZPolyRingElem}, Ref{QQPolyRingElem}), zz, z)
  zz.parent = Globals.Zx
  zzz = ZZRingElem()
  ccall((:fmpq_poly_get_denominator, libflint), Nothing, (Ref{ZZRingElem}, Ref{QQPolyRingElem}), zzz, z)
  ccall((:fq_default_set_fmpz_poly, libflint), Nothing, (Ref{FqFieldElem}, Ref{ZZPolyRingElem}, Ref{FqField}), a, zz, K)
  # invert the denominator
  c = characteristic(K)
  ccall((:fmpz_invmod, libflint), Cint,
        (Ref{ZZRingElem}, Ref{ZZRingElem}, Ref{ZZRingElem}), zzz, zzz, c)
  ccall((:fq_default_mul_fmpz, libflint), Nothing, (Ref{FqFieldElem}, Ref{FqFieldElem}, Ref{ZZRingElem}, Ref{FqField}), a, a, zzz, K)
    #ccall((:fq_set, libflint), Nothing,
  #                   (Ref{FqPolyRepFieldElem}, Ref{FpPolyRingElem}, Ref{FqPolyRepField}),
  #                                   a, a_tmp, K)
  #_reduce(a)
  return a
end


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


################################################################################
#
#  Generators multiplicative group
#
################################################################################

function primitive_element(F::T; n_quo::Int = -1) where T <: Union{FqPolyRepField, fqPolyRepField, fpField, Nemo.FpField, FqField}
  n = order(F)-1
  k = ZZRingElem(1)
  if n_quo != -1
    if !is_divisible_by(n, n_quo)
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


#to avoid using embed - which is (more me) still broken..
# it accumulates fields until the machine dies
function find_morphism(k::Nemo.zzModRing, K::fqPolyRepField)
  return x->K(x.data)
end

function find_morphism(k::fqPolyRepField, K::fqPolyRepField)
   if degree(k) > 1
    phi = Nemo.find_morphism(k, K) #avoids embed - which stores the info
  else
    phi = MapFromFunc(k, K, x->K((coeff(x, 0))), y->k((coeff(y, 0))))
  end
  return phi
end

function find_morphism(k::FqField, K::FqField)
  if degree(k) > 1
    phi = Nemo.find_morphism(k, K) #avoids embed - which stores the info
  else
    phi = MapFromFunc(k, K, x -> K(lift(ZZ, x)), y -> k(lift(ZZ, y)))
  end
  return phi
end

function find_morphism(k::FqField, K::fqPolyRepField)
  # This is no fun
  if absolute_degree(k) == 1
    #@assert degree(K) == 1
    pre = function(x)
      @assert all(is_zero(coeff(x, i)) for i in 1:(degree(K) - 1))
      return k(coeff(x, 0))
    end
    return MapFromFunc(k, K, x -> K(lift(ZZ, x)), pre)
  end

  # build K as FqField, then find isomorphism, then go back

  f = modulus(K)
  a = gen(K)
  F = prime_field(k)
  Ft, t = polynomial_ring(F, "t", cached = false)
  fF = map_coefficients(x -> F(lift(x)), f, parent = Ft)
  KK, polytoKK = Nemo._residue_field(fF)

  KtoKK = x -> polytoKK(map_coefficients(x -> F(lift(x)), parent(f)(x), parent = Ft))

  KKtoK = x -> K(map_coefficients(x -> coefficient_ring(parent(f))(lift(ZZ, x)), polytoKK\x, parent = parent(f)))

  phi_k_to_KK = Nemo.embed_any(k, KK)

  phi = MapFromFunc(k, K, x -> KKtoK(phi_k_to_KK(x)), x -> phi_k_to_KK\(KtoKK(x)))
end


mutable struct VeryBad
  entries::Ptr{UInt}
  r::Int
  c::Int
  rows::Ptr{Ptr{UInt}}
  n::UInt
  ninv::UInt
  norm::UInt

  function VeryBad(n, ninv, norm)
    r = new()
    r.n = n
    r.ninv = ninv
    r.norm = norm
    r.r = 1
    r.rr = [reinterpret(Ptr{UInt}, 0)]
    r.rows = pointer(r.rr)
    return r
  end

  rr::Vector{Ptr{UInt}}
end

function VeryBad!(V::VeryBad, a::fqPolyRepFieldElem)
  V.c = a.length
  V.entries = reinterpret(Ptr{UInt}, a.coeffs)
  V.rr[1] = a.coeffs
#  V.rows = Base.unsafe_convert(Ptr{Nothing}, [a.coeffs])
end

function clear!(V::VeryBad)
  V.entries = reinterpret(Ptr{Ptr{UInt}}, 0)
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

function splitting_field(f::PolyRingElem{<:FinFieldElem}; do_roots::Bool = false)
  lf = factor(f)
  k = base_ring(f)
  d = reduce(lcm, [degree(x) for x = keys(lf.fac)], init = 1)
  if isa(k,  Nemo.fpField) || isa(k, Nemo.fqPolyRepField)
    K = GF(Int(characteristic(k)), absolute_degree(k)*d)
  else
    K = GF(characteristic(k), absolute_degree(k)*d)
  end
  if !isa(k, Nemo.fpField) && !isa(k, Nemo.FpField)
    embed(k, K)
  end
  if do_roots
    return K, roots(K, f)
  end
  return K
end
