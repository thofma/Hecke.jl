export extend, NfToNfMor, automorphisms, automorphism_group

struct NfMorSet{T}
  field::T
end

function show(io::IO, S::NfMorSet{T}) where {T}
  print(io, "Set of automorphisms of ", S.field)
end

parent(f::NfToNfMor) = NfMorSet(domain(f))

function parent(f::NumFieldMor)
  @assert domain(f) == codomain(f)
  return NfMorSet(domain(f))
end

function image(f::NumFieldMor, a::FacElem{S, T}) where {S <: NumFieldElem, T <: NumField}
  D = Dict{elem_type(codomain(f)), fmpz}(f(b) => e for (b, e) in a)
  return FacElem(D)
end

################################################################################
#
#  Some basic properties of NfToNfMor
#
################################################################################

is_injective(m::NumFieldMor) = true

is_surjective(m::NumFieldMor) = absolute_degree(domain(m) == absolute_degree(codomain(m)))

is_bijective(m::NumFieldMor) = is_surjective(m)

################################################################################
#
#  Generic groups to set of homomorphisms
#
################################################################################

mutable struct GrpGenToNfMorSet{S, T} <: Map{GrpGen, NfMorSet{T}, HeckeMap, GrpGenToNfMorSet{S, T}}
  G::GrpGen
  aut::Vector{S}
  header::MapHeader{GrpGen, NfMorSet{T}}

  function GrpGenToNfMorSet(aut::Vector{S}, G::GrpGen, s::NfMorSet{T}) where {S, T}
    z = new{S, T}()
    z.header = MapHeader(G, s)
    z.aut = aut
    z.G = G
    return z
  end
end

function GrpGenToNfMorSet(G::GrpGen, K::NumField)
  return GrpGenToNfMorSet(automorphisms(K), G, NfMorSet(K))
end

function GrpGenToNfMorSet(G::GrpGen, aut::Vector{S}, K::NumField) where S <: NumFieldMor
  return GrpGenToNfMorSet(aut, G, NfMorSet(K))
end

function image(f::GrpGenToNfMorSet, g::GrpGenElem)
  @assert parent(g) == f.G
  K = codomain(f).field
  return f.aut[g[]]
end

function (f::GrpGenToNfMorSet)(g::GrpGenElem)
  return image(f, g)
end

function preimage(f::GrpGenToNfMorSet{S, T}, a::S) where {S, T}
  K = codomain(f).field
  aut = f.aut
  for i in 1:length(aut)
    if a == aut[i]
      return domain(f)[i]
    end
  end
  error("something wrong")
end


function evaluate(f::fmpq_poly, a::nf_elem)
  #Base.show_backtrace(stdout, Base.stacktrace())
  R = parent(a)
  if iszero(f)
    return zero(R)
  end
  if a == gen(R) && parent(f) == parent(parent(a).pol)
    return R(f)
  end
  l = length(f) - 1
  s = R(coeff(f, l))
  for i in l-1:-1:0
    #s = s*a + R(coeff(f, i))
    mul!(s, s, a)
    add!(s, s, coeff(f, i))
  end
  return s
end

Base.copy(f::NfToNfMor) = f

################################################################################
#
#  is normal
#
################################################################################

@doc Markdown.doc"""
     is_normal(K::AnticNumberField) -> Bool

Returns true if $K$ is a normal extension of $\mathbb Q$, false otherwise.
"""
function is_normal(K::AnticNumberField)
  #Before computing the automorphisms, I split a few primes and check if the
  #splitting behaviour is fine
  c = get_attribute(K, :is_normal)
  if c isa Bool
    return c::Bool
  end
  fl = is_normal_easy(K)
  if !fl
    return false
  end
  if length(automorphisms(K, copy = false)) != degree(K)
    set_attribute!(K, :is_normal => false)
    return false
  else
    set_attribute!(K, :is_normal => true)
    return true
  end
end

function is_normal_easy(K::AnticNumberField)
  E = any_order(K)
  p = 1000
  ind = 0
  while ind < 15
    p = next_prime(p)
    F = GF(p, cached = false)
    Fx = PolynomialRing(F, cached = false)[1]
    fF = Fx(K.pol)
    if degree(fF) != degree(K) || iszero(discriminant(fF))
      continue
    end
    ind += 1
    dt = prime_decomposition_type(E, p)
    if !divisible(degree(K), length(dt))
      set_attribute!(K, :is_normal => false)
      return false
    end
    f = dt[1][1]
    for i = 2:length(dt)
      if f != dt[i][1]
        set_attribute!(K, :is_normal => false)
        return false
      end
    end
  end
  return true
end

is_normal(K::NumField) = length(automorphisms(K)) == degree(K)

################################################################################
#
#  IsCMfield
#
################################################################################
@doc Markdown.doc"""
    is_cm_field(K::AnticNumberField) -> Bool, NfToNfMor

Given a number field $K$, this function returns true and the complex conjugation
if the field is CM, false and the identity otherwise.
"""
function is_cm_field(K::NumField)
  c = get_attribute(K, :cm_field)
  if c !== nothing
    return true, c::morphism_type(K)
  end
  if isodd(degree(K)) || !is_totally_complex(K)
    return false, id_hom(K)
  end
  if is_automorphisms_known(K)
    auts = automorphisms(K, copy = false)
    return _find_complex_conj(auts)
  end
  if !is_cm_field_easy(K)
    return false, id_hom(K)
  end
  auts = _automorphisms_center(K)
  return _find_complex_conj(auts)
end

function _automorphisms_center(K::NumField)
  return automorphisms(K)
end

function is_cm_field_known(K::NumField)
  c = get_attribute(K, :cm_field)
  return c !== nothing
end

function _find_complex_conj(auts::Vector{NfToNfMor})
  K = domain(auts[1])
  for x in auts
    if !is_involution(x)
      continue
    end
    if is_complex_conjugation(x)
      set_attribute!(K, :cm_field => x)
      return true, x
    end
  end
  return false, id_hom(K)
end

function is_cm_field_easy(K::AnticNumberField)
  E = any_order(K)
  if is_maximal_order_known(K)
    E = maximal_order(K)
  end
  n = degree(E)
  g = zero_matrix(FlintZZ, n, n)
  B = basis(E, nf(E))
  prec = 32
  imgs = Vector{Vector{arb}}(undef, n)
  for i = 1:n
    imgs[i] = minkowski_map(B[i], prec)
  end
  i = 1
  t = arb()
  while i <= n
    j = i
    while j <= n
      el = imgs[i][1]*imgs[j][1]
      for k = 2:n
        mul!(t, imgs[i][k], imgs[j][k])
        add!(el, el, t)
      end
      if radius(el) > 1//16
        prec *= 2
        for k = i:n
          imgs[k] = minkowski_map(B[k], prec)
        end
        continue
      end
      fl, r = unique_integer(el)
      if !fl
        return false
      end
      j += 1
    end
    i += 1
  end
  return true

end

################################################################################
#
#  Induced image
#
################################################################################

function _evaluate_mod(f::fmpq_poly, a::nf_elem, d::fmpz)
  #Base.show_backtrace(stdout, Base.stacktrace())
  R = parent(a)
  if iszero(f)
    return zero(R)
  end
  l = length(f) - 1
  s = R(coeff(f, l))
  for i in l-1:-1:0
    #s = s*a + R(coeff(f, i))
    mul!(s, s, a)
    # TODO (easy): Once fmpq_poly_add_fmpq is improved in flint, remove the R(..)
    add!(s, s, R(coeff(f, i)))
    s = mod(s, d)
  end
  return s
end

(f::NfToNfMor)(x::NfOrdIdl) = induce_image(f, x)

function induce_image(f::NfToNfMor, x::NfOrdIdl)
  K = domain(f)
  if K != codomain(f)
    OK = maximal_order(codomain(f))
    @assert is_maximal(order(x))
    assure_2_normal(x)
    I = ideal(OK, x.gen_one, OK(f(x.gen_two.elem_in_nf)))
    I.gens_normal = x.gens_normal
    return I
  end

  if isone(x)
    return x
  end

  OK = order(x)
  K = nf(OK)
 if has_2_elem(x) && is_maximal_known(OK) && is_maximal(OK)
    int_in_ideal = x.gen_one
    if has_minimum(x)
      int_in_ideal = minimum(x, copy = false)
    elseif has_norm(x)
      int_in_ideal = norm(x, copy = false)
    end
    if is_coprime(index(OK, copy = false), int_in_ideal) && fits(Int, int_in_ideal^2)
    #The conjugate of the prime will still be a prime over the minimum
    #I just need to apply the automorphism modularly
      return induce_image_easy(f, x)
    end
  end
  I = ideal(OK)
  if isdefined(x, :gen_two)
    new_gen_two = f(K(x.gen_two))
    if has_minimum(x)
      new_gen_two = mod(new_gen_two, minimum(x, copy = false)^2)
    end
    if is_maximal_known(OK) && is_maximal(OK)
      I.gen_two = OK(new_gen_two, false)
    else
      I.gen_two = OK(new_gen_two)
    end
  end
  if isdefined(x, :princ_gen)
     if is_maximal_known(OK) && is_maximal(OK)
      I.princ_gen = OK(f(K(x.princ_gen)), false)
    else
      I.princ_gen = OK(f(K(x.princ_gen)))
    end
  end
  for i in [:gen_one, :is_prime, :gens_normal, :gens_weakly_normal, :is_principal,
          :iszero, :minimum, :norm, :splitting_type]
    if isdefined(x, i)
      setfield!(I, i, getfield(x, i))
    end
  end
  if !has_2_elem(I)
    #I need to translate the basis matrix
    bb = Vector{NfOrdElem}(undef, degree(K))
    B = basis(x, copy = false)
    for i = 1:length(bb)
      bb[i] = OK(f(K(B[i])))
    end
    I.basis = bb
    M = zero_matrix(FlintZZ, degree(K), degree(K))
    for i = 1:degree(K)
      el = coordinates(I.basis[i])
      for j = 1:degree(K)
        M[i, j] = el[j]
      end
    end
    I.basis_matrix = M
  end
  return I
end

function induce_image_easy(f::NfToNfMor, P::NfOrdIdl)
  OK = order(P)
  K = nf(OK)
  R = ResidueRing(FlintZZ, Int(minimum(P, copy = false))^2, cached = false)
  Rx = PolynomialRing(R, "t", cached = false)[1]
  fmod = Rx(K.pol)
  prim_img = Rx(image_primitive_element(f))
  gen_two = Rx(P.gen_two.elem_in_nf)
  img = compose_mod(gen_two, prim_img, fmod)
  new_gen = OK(lift(K, img), false)
  res = ideal(OK, minimum(P), new_gen)
  if isdefined(P, :princ_gen)
    res.princ_gen = OK(f(K(P.princ_gen)), false)
  end
  for i in [:is_prime, :gens_normal, :gens_weakly_normal, :is_principal,
          :minimum, :norm, :splitting_type]
    if isdefined(P, i)
      setfield!(res, i, getfield(P, i))
    end
  end
  return res
end

################################################################################
#
#  Maps to algebras
#
################################################################################

# Embedding of a number field into an algebra over Q.
mutable struct NfAbsToAbsAlgAssMor{S} <: Map{AnticNumberField, S, HeckeMap, NfAbsToAbsAlgAssMor}
  header::MapHeader{AnticNumberField, S}
  mat::fmpq_mat
  t::fmpq_mat

  function NfAbsToAbsAlgAssMor{S}(K::AnticNumberField, A::S, M::fmpq_mat) where { S <: AbsAlgAss{fmpq} }
    z = new{S}()
    z.mat = M
    z.t = zero_matrix(FlintQQ, 1, degree(K))

    function _image(x::nf_elem)
      for i = 1:degree(K)
        z.t[1, i] = coeff(x, i - 1)
      end
      s = z.t*z.mat
      return A([ s[1, i] for i = 1:dim(A) ])
    end

    z.header = MapHeader{AnticNumberField, S}(K, A, _image)
    return z
  end
end

function NfAbsToAbsAlgAssMor(K::AnticNumberField, A::S, M::fmpq_mat) where { S <: AbsAlgAss{fmpq} }
  return NfAbsToAbsAlgAssMor{S}(K, A, M)
end

function haspreimage(m::NfAbsToAbsAlgAssMor, a::AbsAlgAssElem)
  A = parent(a)
  t = matrix(FlintQQ, 1, dim(A), coefficients(a))
  b, p = can_solve_with_solution(m.mat, t, side = :left)
  if b
    return true, domain(m)([ p[1, i] for i = 1:nrows(m.mat) ])
  else
    return false, zero(domain(m))
  end
end

################################################################################
#
#  Order of an automorphism in the automorphisms group
#
################################################################################
@doc Markdown.doc"""
    is_involution(f::NfToNfMor) -> Bool

Returns true if $f$ is an involution, i.e. if $f^2$ is the identity, false otherwise.
"""
function is_involution(f::NfToNfMor)
  K = domain(f)
  @assert K == codomain(f)
  if image_primitive_element(f) == gen(K)
    return false
  end
  p = 2
  R = ResidueRing(FlintZZ, p, cached = false)
  Rt = PolynomialRing(R, "t", cached = false)[1]
  fmod = Rt(K.pol)
  while iszero(discriminant(fmod))
    p = next_prime(p)
    R = ResidueRing(FlintZZ, p, cached = false)
    Rt = PolynomialRing(R, "t", cached = false)[1]
    fmod = Rt(K.pol)
  end
  i = 2
  ap = Rt(image_primitive_element(f))
  fp = compose_mod(ap, ap, fmod)
  return fp == gen(Rt)
end

#@doc Markdown.doc"""
#    _order(f::NfToNfMor) -> Int
#
#If $f$ is an automorphism of a field $K$, it returns the order of $f$ in the automorphism group of $K$.
#"""
function _order(f::NfToNfMor)
  K = domain(f)
  @req K === codomain(f) "The morphism must be an automorphism"
  if image_primitive_element(f) == gen(K)
    return 1
  end
  p = 2
  R = ResidueRing(FlintZZ, p, cached = false)
  Rt = PolynomialRing(R, "t", cached = false)[1]
  fmod = Rt(K.pol)
  while iszero(discriminant(fmod))
    p = next_prime(p)
    R = ResidueRing(FlintZZ, p, cached = false)
    Rt = PolynomialRing(R, "t", cached = false)[1]
    fmod = Rt(K.pol)
  end
  i = 2
  ap = Rt(image_primitive_element(f))
  fp = compose_mod(ap, ap, fmod)
  while fp != gen(Rt)
    i += 1
    fp = compose_mod(ap, fp, fmod)
  end
  return i
end


function small_generating_set(G::Vector{NfToNfMor})

  if length(G) == 1
    return G
  end

  firsttry = 10
  secondtry = 20
  thirdtry = 30

	K = domain(G[1])
	p = 2
  R = GF(p, cached = false)
	Rx = PolynomialRing(R, "x", cached = false)[1]
	while iszero(discriminant(Rx(K.pol)))
		p = next_prime(p)
	  R = GF(p, cached = false)
		Rx = PolynomialRing(R, "x", cached = false)[1]
	end

  given_gens = gfp_poly[Rx(image_primitive_element(x)) for x in G]
	orderG = length(closure(given_gens, (x, y) -> Hecke.compose_mod(x, y, Rx(K.pol)), gen(Rx)))
  # First try one element

  for i in 1:firsttry
    trygen = _non_trivial_randelem(G, id_hom(K))
    if length(closure(gfp_poly[Rx(image_primitive_element(trygen))], (x, y) -> Hecke.compose_mod(x, y, Rx(K.pol)), gen(Rx))) == orderG
      return NfToNfMor[trygen]
    end
  end

  for i in 1:secondtry
    gens = NfToNfMor[_non_trivial_randelem(G, id_hom(K)) for i in 1:2]
    gens_mod = gfp_poly[Rx(image_primitive_element(x)) for x in gens]
    if length(closure(gens_mod, (x, y) -> Hecke.compose_mod(x, y, Rx(K.pol)), gen(Rx))) == orderG
      return unique(gens)
    end
  end

  for i in 1:thirdtry
    gens = NfToNfMor[_non_trivial_randelem(G, id_hom(K)) for i in 1:3]
    gens_mod = gfp_poly[Rx(image_primitive_element(x)) for x in gens]
    if length(closure(gens_mod, (x, y) -> Hecke.compose_mod(x, y, Rx(K.pol)), gen(Rx))) == orderG
      return unique(gens)
    end
  end

  # Now use that unconditionally log_2(|G|) elements generate G

  b = ceil(Int, log(2, orderG))
  @assert orderG <= 2^b

  j = 0
  while true
    if j > 2^20
      error("Something wrong with generator search")
    end
    j = j + 1
    gens = NfToNfMor[_non_trivial_randelem(G, id_hom(K)) for i in 1:b]
    gens_mod = gfp_poly[Rx(image_primitive_element(x)) for x in gens]
    if length(closure(gens_mod, (x, y) -> Hecke.compose_mod(x, y, Rx(K.pol)), gen(Rx))) == orderG
      return unique(gens)
    end
  end
end

function _order(G::Vector{NfToNfMor})
  K = domain(G[1])
	p = 2
  R = GF(p, cached = false)
	Rx = PolynomialRing(R, "x", cached = false)[1]
	while iszero(discriminant(Rx(K.pol)))
		p = next_prime(p)
	  R = GF(p, cached = false)
		Rx = PolynomialRing(R, "x", cached = false)[1]
	end
  given_gens = gfp_poly[Rx(image_primitive_element(x)) for x in G]
	return length(closure(given_gens, (x, y) -> Hecke.compose_mod(x, y, Rx(K.pol)), gen(Rx)))
end

################################################################################
#
#  Frobenius automorphism
#
################################################################################

function frobenius_automorphism(P::NfOrdIdl)
  @assert is_prime(P)
  OK = order(P)
  K = nf(OK)
  @assert is_maximal_known_and_maximal(OK)
  @assert ramification_index(P) == 1
  @assert is_normal(K)
  K = nf(OK)
  auts = decomposition_group(P)
  F, mF = ResidueField(OK, P)
  p = minimum(P, copy = false)
  genF = elem_in_nf(mF\gen(F))
  powgen = gen(F)^p
  for i = 1:length(auts)
    img = auts[i](genF)
    if mF(OK(img, false)) == powgen
      return auts[i]
    end
  end
  error("Something went wrong")
end
