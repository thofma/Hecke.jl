# Compute basis for the subfield of K that is generated by the elements of as.
function _subfield_basis(K::S, as::Vector{T}) where {
    S <: Union{AbsSimpleNumField, Hecke.RelSimpleNumField},
    T <: Union{AbsSimpleNumFieldElem, Hecke.RelSimpleNumFieldElem}
   }
  if isempty(as)
    return elem_type(K)[gen(K)]
  end

  # Notation: k base field, K the ambient field, F the field generated by as

  k = base_field(K)

  d = degree(K)
  Kvs = vector_space(k, d)
  # We transition the coefficients of a in reverse order, so that the
  # first vector in the row reduced echelon form yields the highest
  # degree among all elements of Fas.
  (Fvs,phivs) = sub(Kvs, [Kvs([coeff(a,n) for n in d-1:-1:0])
                          for a in as])
  dF = length(Fvs.gens) # dim(Fvs)
  bs = as
  while !isempty(bs)
    nbs = elem_type(K)[]
    for b in bs
      abs = elem_type(K)[a*b for a in as]
      abvs,_ = sub(Kvs, [Kvs([coeff(ab,n) for n in d-1:-1:0])
                         for ab in abs])
      (Fvs,phivs) = sub(Kvs, typeof(Fvs)[Fvs, abvs])
      if dF != length(Fvs.gens) # dim(Fvs)
        dF = length(Fvs.gens) # dim(Fvs)
        append!(nbs, abs)
      end
    end
    bs = nbs
  end

  kx = parent(K.pol)
  b = elem_type(K)[let Kv = phivs(v)
            K(kx([Kv[n] for n in d:-1:1]))
          end
          for v in gens(Fvs)]::Vector{elem_type(K)}
          return b
  return [x*denominator(x) for x= b]        
end

function _improve_subfield_basis(K, bas)
  # First compute the maximal order of <bas> by intersecting and saturating
  # Then B_Ok = N * B_LLL_OK
  # Then B' defined as lllN * B_LLL_OK will hopefully be small
  OK = maximal_order(K)
  OKbmatinv = basis_mat_inv(FakeFmpqMat, OK, copy = false)
  basinOK = bas * QQMatrix(OKbmatinv.num) * QQFieldElem(1, OKbmatinv.den)
  deno = ZZRingElem(1)
  for i in 1:nrows(basinOK)
    for j in 1:ncols(basinOK)
      deno = lcm(deno, denominator(basinOK[i, j]))
    end
  end
   S = saturate(map_entries(ZZ, basinOK * deno))
  SS = S * basis_matrix(FakeFmpqMat, OK, copy = false)
  lllOK = lll(OK)
  N = (SS * basis_mat_inv(FakeFmpqMat, lllOK)).num
  lllN = lll(N)
  maybesmaller = lllN * basis_matrix(FakeFmpqMat, lllOK)
  return maybesmaller
end

function _improve_subfield_basis_no_lll(K, bas)
  OK = maximal_order(K)
  OKbmatinv = basis_mat_inv(OK, copy = false)
  basinOK = bas * QQMatrix(OKbmatinv.num) * QQFieldElem(1, OKbmatinv.den)
  deno = ZZRingElem(1)
  for i in 1:nrows(basinOK)
    for j in 1:ncols(basinOK)
      deno = lcm(deno, denominator(basinOK[i, j]))
    end
  end
  S = saturate(map_entries(ZZ, basinOK * deno))
  SS = S * basis_matrix(FakeFmpqMat, OK, copy = false)
  return SS
end

# Compute a primitive element given a basis of a subfield
function _subfield_primitive_element_from_basis(K::S, as::Vector{T}) where {
    S <: Union{AbsSimpleNumField, Hecke.RelSimpleNumField},
    T <: Union{AbsSimpleNumFieldElem, Hecke.RelSimpleNumFieldElem}
   }
  if isempty(as)
    return gen(K)
  end

  d = length(as)

  # First check basis elements
  i = findfirst(a -> degree(minpoly(a)) == d, as)
  if i <= d
    return as[i]
  end

  k = base_field(K)

  # Notation: cs the coefficients in a linear combination of the as, ca the dot
  # product of these vectors.
  cs = ZZRingElem[zero(ZZ) for n in 1:d]
  cs[1] = one(ZZ)
  while true
    ca = sum(c*a for (c,a) in zip(cs,as))
    if degree(minpoly(ca)) == d
      return ca
    end

    # increment the components of cs
    cs[1] += 1
    let i = 2
      while i <= d && cs[i-1] > cs[i]+1
        cs[i-1] = zero(ZZ)
        cs[i] += 1
        i += 1
      end
    end
  end
end

#As above, but for AbsSimpleNumField type
#In this case, we can use block system to find if an element is primitive.
#does not need to be a basis, generators are sufficient
function _subfield_primitive_element_from_basis(K::AbsSimpleNumField, as::Vector{AbsSimpleNumFieldElem})
  if isempty(as) || degree(K) == 1
    return gen(K)
  end

  as = [x for x = as if !iszero(x)]

  dsubfield = length(as)

  @vprintln :Subfields 1 "Sieving for primitive elements"
  # First check basis elements
  Zx = polynomial_ring(ZZ, "x", cached = false)[1]
  f = Zx(K.pol*denominator(K.pol))
  p, d = _find_prime(ZZPolyRingElem[f])
  #does not need to ne successful!!!
  #First, we search for elements that are primitive using block systems
  #TODO: use p-adic roots ala Oscar/experimental/Galois.../src/Subfield.jl
  # prob: get bounds without SLP and GaloisCtx
  F = Nemo.Native.finite_field(p, d, "w", cached = false)[1]
  Ft = polynomial_ring(F, "t", cached = false)[1]
  ap = zero(Ft)
  fit!(ap, degree(K)+1)
  rt = roots(F, f)
  indices = Int[]
  b = [collect(1:degree(f))] #block system for QQ
  all_b = []
  for i = 1:length(as)
    _b = _block(as[i], rt, ap)
    push!(all_b, _b)
    b = [intersect(x, y) for x = b for y = _b]
    b = [x for x = b if length(x) > 0]
  end
  @vprintln :Subfields 1 "Have block systems, degree of subfield is $(length(b))\n"

  indices = findall(x->length(x) == length(b), all_b)

  @vprintln :Subfields 1 "Found $(length(indices)) primitive elements in the basis"
  #Now, we select the one of smallest T2 norm
  if !isempty(indices)
    a = as[indices[1]]
    I = t2(a)
    for i = 2:length(indices)
      t2n = t2(as[indices[i]])
      if t2n < I
        a = as[indices[i]]
        I = t2n
      end
    end
    @vprintln :Subfields 1 "Primitive element found"
    return a
  end

  @vprintln :Subfields 1 "Finding combination of elements"

  pe = as[1]
  cur_b = all_b[1]
  for i=2:length(as)
    if issubset(all_b[i][1], cur_b[1])
      continue
    end
    cur_b = [intersect(x, y) for x = cur_b for y = all_b[i]]
    cur_b = [x for x = cur_b if length(x) > 0]
    j = 1
    while _block(pe + j*as[i], rt, ap) != c
      j += 1
      if j > 10
        error("dnw")
      end
    end
    pe += j*as[i]
    if cur_b == b
      @vprintln :Subfields 1 "Primitive element found"
      return pe
    end
  end
  error("should be hard...")
end

################################################################################
#
#  Subfield
#
################################################################################

sub(K::NumField, args...; kw...) = subfield(K, args...; kw...)

@doc raw"""
    subfield(L::NumField, elements::Vector{<: NumFieldelem};
                          is_basis::Bool = false) -> NumField, Map

Return the simple number field $K$ generated by the given elements over the
base field $k$ of $L$ together with the embedding $k \to L$.

If `is_basis` is `true`, it is assumed that `elements` holds a $k$-basis of
$K$.

```jldoctest
julia> Qx, x = QQ[:x]; L, a = number_field(x^4 + 6*x^2 + 4, :a);

julia> K, KtoL = subfield(L, [a^2]);

julia> K
Number field with defining polynomial x^2 + 6*x + 4
  over rational field
```
"""
function subfield(K::NumField, elt::Vector{<:NumFieldElem}; is_basis::Bool = false, isbasis::Bool = false)
  @req all(x -> parent(x) === K, elt) "Elements must be contained in the field"

  if length(elt) == 1
    return _subfield_from_primitive_element(K, elt[1])
  end

  s = _subfield_primitive_element_from_basis(K, elt) #see comment: does not
   #have to be a basis...
  s *= denominator(s)

  return _subfield_from_primitive_element(K, s)
end

function _subfield_from_primitive_element(K::AbsSimpleNumField, s::AbsSimpleNumFieldElem)
  @vtime :Subfields 1 f = minpoly(Globals.Qx, s)
  f = denominator(f) * f
  L, _ = number_field(f, cached = false)
  return L, hom(L, K, s, check = false)
end

function _subfield_from_primitive_element(K, s)
  @vtime :Subfields 1 f = minpoly(s)
  L, _ = number_field(f, cached = false)
  return L, hom(L, K, s, check = false)
end

################################################################################
#
#  Fixed field
#
################################################################################

@doc raw"""
    fixed_field(K::SimpleNumField,
                sigma::Map;
                simplify::Bool = true) -> number_field, NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}

Given a number field $K$ and an automorphism $\sigma$ of $K$, this function
returns the fixed field of $\sigma$ as a pair $(L, i)$ consisting of a number
field $L$ and an embedding of $L$ into $K$.

By default, the function tries to find a small defining polynomial of $L$. This
can be disabled by setting `simplify = false`.
"""
function fixed_field(K::SimpleNumField, sigma::T; simplify::Bool = true) where {T <: NumFieldHom}
  return fixed_field(K, T[sigma], simplify = simplify)
end

#@doc raw"""
#    fixed_field(K::SimpleNumField, A::Vector{NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}) -> number_field, NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}
#
#Given a number field $K$ and a set $A$ of automorphisms of $K$, this function
#returns the fixed field of $A$ as a pair $(L, i)$ consisting of a number field
#$L$ and an embedding of $L$ into $K$.
#
#By default, the function tries to find a small defining polynomial of $L$. This
#can be disabled by setting `simplify = false`.
#"""
function fixed_field(K::AbsSimpleNumField, A::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}; simplify::Bool = true)

  autos = small_generating_set(A)
  if length(autos) == 0
    return K, id_hom(K)
  end

  if is_maximal_order_known(K)
    OK = maximal_order(K)
    if isdefined(OK, :lllO)
      k, mk = fixed_field1(K, A)
      return k, mk
    end
  end

  a = gen(K)
  n = degree(K)
  ar_mat = Vector{QQMatrix}()
  v = Vector{AbsSimpleNumFieldElem}(undef, n)
  for i in 1:length(autos)
    domain(autos[i]) !== codomain(autos[i]) && error("Maps must be automorphisms")
    domain(autos[i]) !== K && error("Maps must be automorphisms of K")
    o = one(K)
    # Compute the image of the basis 1,a,...,a^(n - 1) under autos[i] and write
    # the coordinates in a matrix. This is the matrix of autos[i] with respect
    # to 1,a,...a^(n - 1).
    as = autos[i](a)
    if a == as
      continue
    end
    v[1] = o
    for j in 2:n
      o = o * as
      v[j] = o
    end
    bm = basis_matrix(v, FakeFmpqMat)
    # We have to be a bit careful (clever) since in the absolute case the
    # basis matrix is a FakeFmpqMat

    m = QQMatrix(bm.num)
    for j in 1:n
      m[j, j] = m[j, j] - bm.den # This is autos[i] - identity
    end


    push!(ar_mat, m)
  end

  if length(ar_mat) == 0
    return K, id_hom(K)
  else
    bigmatrix = reduce(hcat, ar_mat)
    Ker = kernel(bigmatrix, side = :left)
    bas = Vector{elem_type(K)}(undef, nrows(Ker))
    if simplify
      KasFMat = _improve_subfield_basis(K, Ker)
      for i in 1:nrows(Ker)
        bas[i] = elem_from_mat_row(K, KasFMat.num, i, KasFMat.den)
      end
    else
    #KasFMat = _improve_subfield_basis_no_lll(K, Ker)
      KasFMat = FakeFmpqMat(Ker)
      Ksat = saturate(KasFMat.num)
      Ksat = lll(Ksat)
      onee = one(ZZRingElem)
      for i in 1:nrows(Ker)
        #bas[i] = elem_from_mat_row(K, KasFMat.num, i, KasFMat.den)
        bas[i] = elem_from_mat_row(K, Ksat, i, onee)
      end
    end
  end
  return subfield(K, bas, isbasis = true)
end


function fixed_field(K::RelSimpleNumField, A::Vector{T}; simplify::Bool = true) where {T <: NumFieldHom}
  autos = A

    # Everything is fixed by nothing :)
  if length(autos) == 0
    return K, id_hom(K)
  end

  F = base_field(K)
  a = gen(K)
  n = degree(K)
  ar_mat = Vector{dense_matrix_type(elem_type(F))}()
  v = Vector{elem_type(K)}(undef, n)
  for i in 1:length(autos)
    domain(autos[i]) !== codomain(autos[i]) && error("Maps must be automorphisms")
    domain(autos[i]) !== K && error("Maps must be automorphisms of K")
    o = one(K)
    # Compute the image of the basis 1,a,...,a^(n - 1) under autos[i] and write
    # the coordinates in a matrix. This is the matrix of autos[i] with respect
    # to 1,a,...a^(n - 1).
    as = autos[i](a)
    if a == as
      continue
    end
    v[1] = o
    for j in 2:n
      o = o * as
      v[j] = o
    end

    bm = basis_matrix(v)
    # In the generic case just subtract the identity
    m = bm - identity_matrix(F, degree(K))
    push!(ar_mat, m)
  end

  if length(ar_mat) == 0
    return K, id_hom(K)
  else
    bigmatrix = reduce(hcat, ar_mat)
    Ker = kernel(bigmatrix, side = :left)
    bas = Vector{elem_type(K)}(undef, nrows(Ker))
    for i in 1:nrows(Ker)
      bas[i] = elem_from_mat_row(K, Ker, i)
    end
  end
  return subfield(K, bas, isbasis = true)
end


function fixed_field1(K::AbsSimpleNumField, auts::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})

	auts_new = small_generating_set(auts)
  orderG = _order(auts)
  degree_subfield = divexact(degree(K), orderG)
  #TODO: Experiments to see if this is helpful
  #=
  if length(auts_new) == 1 && is_prime_power(degree_subfield)
    #In this case, one of the coefficients of the minpoly of gen(K)
    #over the subfield is a generator for the subfield.
    #if the given generator was not too large, also this element will be ok
		gens = auts
		if orderG != length(auts)
		  gens = closure(auts, orderG)
    end
    conjs = AbsSimpleNumFieldElem[image_primitive_element(x) for x in gens]
		prim_el = sum(conjs)
		def_pol = minpoly(prim_el)
    if degree(def_pol) != degree_subfield
			conjs1 = copy(conjs)
      while degree(def_pol) != degree_subfield
				for i = 1:length(conjs)
          conjs1[i] *= conjs[i]
				end
				prim_el = sum(conjs1)
       	def_pol = minpoly(prim_el)
			end
		end
    subK = number_field(def_pol, cached = false)[1]
    mp = hom(subK, K, prim_el, check = false)
    return subK, mp
	end
=#
  OK = maximal_order(K)
  # If degree(K) is large and the basis is not LLL reduced
  # the linear algebra will be very slow.
  # So lets compute an LLL basis once degree(K) is large.
  # 50 is a heuristic cutoff.
  if isdefined(OK, :lllO) || degree(K) >= 50
    OK = lll(OK)
  end
  M = zero_matrix(ZZ, degree(K), degree(K)*length(auts_new))
  v = Vector{AbsSimpleNumFieldElem}(undef, degree(K))
  MOK = basis_matrix(FakeFmpqMat, OK, copy = false)
  MOKinv = basis_mat_inv(FakeFmpqMat, OK, copy = false)
  for i = 1:length(auts_new)
		v[1] = one(K)
    v[2] = image_primitive_element(auts_new[i])
    for j = 3:degree(K)
      v[j] = v[j-1]*v[2]
		end
    B = basis_matrix(v, FakeFmpqMat)
    mul!(B, B, MOKinv)
    mul!(B, MOK, B)
    @assert isone(B.den)
    for i = 1:degree(K)
      B.num[i, i] -= 1
    end
		_copy_matrix_into_matrix(M, 1, (i-1)*degree(K)+1, B.num)
	end
	@vtime :Subfields 1 Ker = kernel(M, side = :left)
  @assert nrows(Ker) == degree_subfield
  @vtime :Subfields 1 Ker = lll(Ker)
	#The kernel is the maximal order of the subfield.
  bas = Vector{AbsSimpleNumFieldElem}(undef, degree_subfield)
	for i = 1:degree_subfield
    bas[i] = elem_from_mat_row(OK, Ker, i).elem_in_nf
	end
  return subfield(K, bas, isbasis = true)
end


################################################################################
#
#  Fixed field as relative extension
#
################################################################################

function fixed_field(K::AbsSimpleNumField, auts::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}}, ::Type{RelSimpleNumField{AbsSimpleNumFieldElem}}; simplify_subfield::Bool = true)
  F, mF = fixed_field(K, auts)
  if simplify_subfield
    F, mF1 = simplify(F, cached = false)
    mF = mF1*mF
  end
  all_auts = closure(auts, div(degree(K), degree(F)))
  Kx, x = polynomial_ring(K, "x", cached = false)
  p = prod(x-image_primitive_element(y) for y in all_auts)
  def_eq = map_coefficients(x -> has_preimage_with_preimage(mF, x)[2], p, cached = false)
  L, gL = number_field(def_eq, cached = false, check = false)
  iso = hom(K, L, gL, image_primitive_element(mF), gen(K))
  #I also set the automorphisms...
  autsL = Vector{NfRelToNfRelMor{AbsSimpleNumFieldElem, AbsSimpleNumFieldElem}}(undef, length(all_auts))
  for i = 1:length(autsL)
    autsL[i] = hom(L, L, iso(image_primitive_element(all_auts[i])))
  end
  set_automorphisms!(L, autsL)
  return L, iso
end
