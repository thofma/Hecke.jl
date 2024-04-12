import Base.vcat, Base.hcat

add_verbosity_scope(:PseudoHnf)
add_assertion_scope(:PseudoHnf)
add_verbosity_scope(:PseudoHnfKB)

function _det_bound(M::Generic.Mat{AbsSimpleNumFieldOrderElem})
  n = nrows(M)
  O = base_ring(M)
  d = degree(O)
  c1, c2 = Hecke.norm_change_const(O)

  return ZZRingElem(BigInt(ceil(sqrt(c2)*c1^(n/2)*BigInt(n)^n*BigInt(d)^n*BigInt(_max_max(M))^n)))
end

function _max_max(M::Generic.Mat{AbsSimpleNumFieldOrderElem})
  d = FlintZZ(1)
  for i in 1:nrows(M)
    for j in 1:ncols(M)
      if !iszero(M[i, j])
        v = coordinates(M[i, j])
        for k in degree(base_ring(M))
          d = max(d, abs(v[k]))
        end
      end
    end
  end
  return d
end

#function det(M::Generic.Mat{AbsSimpleNumFieldOrderElem})
#  O = base_ring(M)::AbsSimpleNumFieldOrder
#  B = _det_bound(M)
#  p = next_prime(2^60) # magic numbers
#  P = ZZRingElem(1)
#  i = 1
#  res = zero(O)
#  t = 0.0
#  while P < 2*B
#    # reject some bad primes
#    if true
#      #println("$p");
#      Omodp, pi_p = quo(O, ideal(O, p))
#      Mmodp = matrix_space(Omodp, nrows(M), ncols(M))(M)
#      t += @elapsed detmodp = pi_p\Hecke.det(Mmodp)
#      if i == 1
#        res = detmodp
#      elseif i >= 2
#        g, e, f = gcdx(P, ZZRingElem(p))
#        @assert isone(g)
#        res = f*p*res + e*P*detmodp
#        res = mod_sym(res, P*p)
#        #@assert _basis_coord_nonneg(res)
#      end
#      P = P*p
#      p = next_prime(p)
#      i += 1
#    end
#  end
#  #println("Modular determinant time: $t");
#  return res
#end

function _get_coeff_raw(x::zzModPolyRingElem, i::Int)
  u = ccall((:nmod_poly_get_coeff_ui, libflint), UInt, (Ref{zzModPolyRingElem}, Int), x, i)
  return u
end

function _get_coeff_raw(x::fpPolyRingElem, i::Int)
  u = ccall((:nmod_poly_get_coeff_ui, libflint), UInt, (Ref{fpPolyRingElem}, Int), x, i)
  return u
end

function det(M::Generic.Mat{AbsSimpleNumFieldOrderElem})
  O = base_ring(M)::AbsSimpleNumFieldOrder
  K = nf(O)
  B = _det_bound(M)
  p = next_prime(p_start) #global
  P = ZZRingElem(1)
  i = 1
  res = O()
  t_det = 0.0
  t_reducing = 0.0
  t_splitting = 0.0
  used_primes = Vector{UInt}()
  tmp_polys = Vector{AbsSimpleNumFieldElem}()

  while P < 2*B
    # reject some bad primes
    if is_index_divisor(O, p)
      continue
    end

    ttt = @elapsed me = modular_init(K, p)

    push!(used_primes, UInt(p))

    t_splitting += ttt

    detmodp = zzModPolyRingElem(UInt(p))

    t_reducing += @elapsed Mp = modular_proj(M, me)

    t_det += @elapsed detmodQ = [det(x) for x = Mp]

      # now the CRT step
    detmodp = modular_lift(detmodQ, me)

    push!(tmp_polys, detmodp)

    P = P*p
    p = next_prime(p)
    i += 1
  end

  # now the CRT on each coefficient

  fc = crt_env(ZZRingElem[x for x = used_primes])
  fv = Array{ZZRingElem}(undef, length(used_primes))
  for i=1:length(used_primes)
    fv[i] = ZZRingElem(0)
  end
  zz = ZZRingElem()

  @assert length(used_primes) == length(tmp_polys)

  tmp_fmpz_poly = polynomial_ring(FlintZZ)[1]()

  for i in 0:degree(O)
    for j=1:length(used_primes)
      Nemo.num_coeff!(fv[j], tmp_polys[j], i)
    end
    crt!(zz, fv, fc)
    setcoeff!(tmp_fmpz_poly, i, zz)
  end

  tut = QQPolyRingElem(tmp_fmpz_poly)
  tut.parent = parent(nf(O).pol)
  res = mod_sym(O(nf(O)(tut)), P)

  #println("Modular determinant time: $t_det");
  #println("Time for reducing: $t_reducing");
  #println("Time for splitting: $t_splitting");
  #println("Used $(length(used_primes)) primes")

  return res
end

# s, t are auxiliary variables, r1, r2 are the residues, m1, m2 are the moduli
# aliasing is not allowed (?)
function crt!(z::zzModPolyRingElem, r1::zzModPolyRingElem, r2::Union{zzModPolyRingElem, fqPolyRepFieldElem}, m1::zzModPolyRingElem, m2::zzModPolyRingElem, s::zzModPolyRingElem, t::zzModPolyRingElem)
  ccall((:nmod_poly_xgcd, libflint), Nothing, (Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}), z, s, t, m1, m2)
  @assert Bool(ccall((:nmod_poly_is_one, libflint), Cint, (Ref{zzModPolyRingElem}, ), z))
  # z = s*m1*r2 + t*m2*r1
  mul!(z, s, m1)
  ccall((:nmod_poly_mul, libflint), Nothing, (Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}, Ref{fqPolyRepFieldElem}), z, z, r2)
  mul!(t, t, m2)
  mul!(t, t, r1)
  add!(z, z, t)
  mul!(s, m1, m2)
  rem!(z, z, s)
end

function set!(z::zzModPolyRingElem, x::zzModPolyRingElem)
  ccall((:nmod_poly_set, libflint), Nothing, (Ref{zzModPolyRingElem}, Ref{zzModPolyRingElem}), z, x)
end

function set!(z::fpPolyRingElem, x::fpPolyRingElem)
  ccall((:nmod_poly_set, libflint), Nothing, (Ref{fpPolyRingElem}, Ref{fpPolyRingElem}), z, x)
end

function __helper!(z, mF, entries)
  s = size(entries)
  for i in 1:s[2]
    for j in 1:s[1]
      z[j, i] = mF(entries[j, i])
    end
  end
  return z
end

function mod_sym(x::AbsSimpleNumFieldOrderElem, m::ZZRingElem)
  z = coordinates(x)
  for i in 1:length(z)
    z[i] = mod(z[i], m)
    if 2*z[i] > m
      z[i] = z[i] - m
    end
  end
  return parent(x)(z)
end
mod_sym(x::AbsSimpleNumFieldOrderElem, m::Integer) = mod_sym(x, ZZRingElem(m))

function _basis_coord_nonneg(x::AbsSimpleNumFieldOrderElem)
  b = coordinates(x)
  for i in 1:length(b)
    if b[i] < 0
      return false
    end
  end
  return true
end

function rand(M::Generic.MatSpace{AbsSimpleNumFieldOrderElem}, B::Union{Int, ZZRingElem})
  z = M()
  for i in 1:nrows(z)
    for j in 1:ncols(z)
      z[i, j] = Hecke.rand(Hecke.base_ring(M), B)
    end
  end
  return z
end

==(P::PMat, Q::PMat) = P.matrix == Q.matrix && P.coeffs == Q.coeffs

function Base.deepcopy_internal(P::PMat{T, S}, dict::IdDict) where {T, S}
  z = PMat{T, S}()
  for x in fieldnames(typeof(P))
    if x != :base_ring && isdefined(P, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(P, x), dict))
    end
  end
  if isdefined(P, :base_ring)
    z.base_ring = P.base_ring
  end
  return z
end

function show(io::IO, P::PMat)
  compact = get(io, :compact, false)
  if compact
    for i in 1:nrows(P.matrix)
      i == 1 || print(io, "\n")
      print(io, "(")
      print(IOContext(io, :compact => true), P.coeffs[i])
      print(io, ") * ")
      print(io, sub(P.matrix, i:i, 1:ncols(P.matrix)))
    end
  else
    print(io, "Pseudo-matrix over ", base_ring(P))
    for i in 1:nrows(P.matrix)
      print(io, "\n")
      show(IOContext(io, :compact => true), P.coeffs[i])
      print(io, " with row $(sub(P.matrix, i:i, 1:ncols(P.matrix)))")
    end
  end
end

@doc raw"""
    coefficient_ideals(M::PMat)

Returns the vector of coefficient ideals.
"""
coefficient_ideals(M::PMat) = M.coeffs

@doc raw"""
    matrix(M::PMat)

Returns the matrix part of the `PMat`.
"""
matrix(M::PMat) = M.matrix

@doc raw"""
    base_ring(M::PMat)

The `PMat` $M$ defines an $R$-module for some maximal order $R$.
This function returns the $R$ that was used to defined $M$.
"""
base_ring(M::PMat{T, S}) where {T, S} = nrows(M) >= 1 ? order(M.coeffs[1]) : M.base_ring::order_type(parent_type(T))

function pseudo_matrix(m::AbstractAlgebra.MatElem{T}, c::Vector{S}) where {T, S}
  # sanity checks
  @assert nrows(m) == length(c)
  return PMat{T, S}(m ,c)
end

function pseudo_matrix(O::NumFieldOrder, m::AbstractAlgebra.MatElem{T}, c::Vector{S}) where {T, S}
  # sanity checks
  @assert nrows(m) == length(c)
  z = PMat{T, S}(m ,c)
  z.base_ring = O
  return z
end

@doc raw"""
    pseudo_matrix(m::Generic.Mat{AbsSimpleNumFieldElem}, c::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}

Returns the (row) pseudo matrix representing the $Z_k$-module
 $$\sum c_i m_i$$
 where $c_i$ are the ideals in $c$ and $m_i$ the rows of $M$.
"""
function pseudo_matrix(m::AbstractAlgebra.MatElem{AbsSimpleNumFieldElem}, c::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  @assert nrows(m) == length(c)
  cc = map(z -> AbsSimpleNumFieldOrderFractionalIdeal(z, ZZRingElem(1)), c)
  return PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}(m, cc)
end

@doc raw"""
    pseudo_matrix(m::Generic.Mat{AbsSimpleNumFieldOrderElem}, c::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}) -> PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}

Returns the (row) pseudo matrix representing the $Z_k$-module
 $$\sum c_i m_i$$
 where $c_i$ are the ideals in $c$ and $m_i$ the rows of $M$.
"""
function pseudo_matrix(m::Generic.Mat{AbsSimpleNumFieldOrderElem}, c::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
  @assert nrows(m) == length(c)
  mm = change_base_ring(nf(base_ring(m)), m)
  cc = map(z -> AbsSimpleNumFieldOrderFractionalIdeal(z, ZZRingElem(1)), c)
  return PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}(mm, cc)
end

@doc raw"""
    pseudo_matrix(m::Generic.Mat{AbsSimpleNumFieldOrderElem}) -> PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}

Returns the free (row) pseudo matrix representing the $Z_k$-module
 $$\sum Z_k m_i$$
 where $m_i$ are the rows of $M$.
"""
function pseudo_matrix(m::Generic.Mat{AbsSimpleNumFieldElem})
   K = base_ring(m)
   O = maximal_order(K)
   return pseudo_matrix(O, m, fractional_ideal_type(O)[ideal(O, K(1)) for i = 1:nrows(m)])
end

function pseudo_matrix(m::MatElem{S}) where S <: NumFieldElem
  L = base_ring(m)
  OL = maximal_order(L)
  K = base_field(L)
  return pseudo_matrix(OL, m, fractional_ideal_type(OL)[ fractional_ideal(OL, ideal(OL, 1)) for i = 1:nrows(m) ])
end

function pseudo_matrix(m::MatElem{S}, c::Vector{T}) where {S <: NumFieldElem, T <: RelNumFieldOrderIdeal}
  @assert nrows(m) == length(c)
  cc = [ fractional_ideal(order(c[i]), basis_pmatrix(c[i]); M_in_hnf=true) for i = 1:length(c) ]
  return PMat{S, typeof(cc[1])}(m, cc)
end

pseudo_matrix(m::MatElem{AbsSimpleNumFieldOrderElem}) = pseudo_matrix(change_base_ring(nf(base_ring(m)), m))

function pseudo_matrix(c::Vector{S}) where S
   K = nf(order(c[1]))
   m = identity_matrix(K, length(c))
   return pseudo_matrix(m, c)
end

pseudo_matrix(c::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}) = pseudo_matrix(map(z -> AbsSimpleNumFieldOrderFractionalIdeal(z, ZZRingElem(1)), c))

function number_of_rows(m::PMat)
  return number_of_rows(m.matrix)
end

function number_of_columns(m::PMat)
  return number_of_columns(m.matrix)
end


function det(m::PMat)
  z = m.coeffs[1]
  for i in 2:nrows(m)
    z = z*m.coeffs[i]
  end
  return det(m.matrix)*z
end

function *(P::PMat{T, S}, x::U) where { T, S, U <: Union{ Int, RingElem } }
  if nrows(P) == 0 || ncols(P) == 0
    return P
  end

  K = parent(P.matrix[1, 1])
  x = K(x)

  PP = deepcopy(P)
  for i = 1:nrows(PP)
    PP.coeffs[i] = PP.coeffs[i]*x
    PP.coeffs[i] = simplify(PP.coeffs[i])
  end
  return PP
end

*(x::U, P::PMat{T, S}) where { T, S, U <: Union{ Int, RingElem } } = P*x

# this is slow
function _coprime_integral_ideal_class(x::Union{AbsSimpleNumFieldOrderFractionalIdeal, AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  O = order(y)
  x_inv = inv(x)
  check = true
  z = ideal(O, O(1))
  a = nf(O)()
  i = 0
  while check
    i += 1
    a = rand(x_inv, 10)
    if iszero(a)
      continue
    end
    b = x*a
    z = divexact(numerator(b), denominator(b))
    norm(z + y) == 1 ? (check = false) : (check = true)
  end
  return z, a
end

function _coprime_integral_ideal_class(x::FacElem{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, AbsNumFieldOrderIdealSet{AbsSimpleNumField, AbsSimpleNumFieldElem}}, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  D = typeof(x.fac)()
  D2 = Dict{AbsSimpleNumFieldElem, ZZRingElem}()
  O = order(y)
  for (I, e) in x
    II, a = _coprime_integral_ideal_class(I, y)
    D[II] = e
    D2[a] = e
  end
  return FacElem(D), FacElem(D2)
end


# this is slow
function _coprime_norm_integral_ideal_class(x, y) #x::AbsSimpleNumFieldOrderFractionalIdeal, y::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  # x must be nonzero
  O = order(y)
  if is_coprime(norm(numerator(x, copy = false), copy = false), norm(y, copy = false))
    return numerator(x, copy = false), nf(O)(denominator(x))
  end
  x_inv = inv(x)
  check = true
  z = ideal(O, O(1))
  a = nf(O)()
  i = -1
  while check && i < 100
    i += 1
    a = rand(x_inv, 10)
    if iszero(a)
      continue
    end
    b = x*a
    simplify(b)
    @assert isone(denominator(b, copy = false))
    z = numerator(b, copy = false)
    check = !(gcd(norm(z, copy = false), norm(y, copy = false)) == 1)
  end
  if !check
    return z, a
  end
  a = nf(O)(denominator(x, copy = false))
  lp = factor(ideal(O, gcd(minimum(numerator(x, copy = false), copy = false), minimum(y, copy = false))))
  J, b = coprime_deterministic(numerator(x, copy = false), y, lp)
  res2 = b*a
  @hassert :PseudoHnf 1 res2*x == J
  @hassert :PseudoHnf 1 is_coprime(norm(J, copy = false), norm(y, copy = false))
  return J, res2
end

RandomExtensions.maketype(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, ::Int) = AbsSimpleNumFieldOrderElem

function rand(rng::AbstractRNG, sp::SamplerTrivial{<:Make2{AbsSimpleNumFieldOrderElem,AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem},Int}})
  I, B = sp[][1:end]
  r = rand(rng, -B:B, degree(order(I)))
  b = basis(I)
  z::Random.gentype(sp) = r[1]*b[1] # type assert to help inference in Julia 1.0
  for i in 2:degree(order(I))
    z = z + r[i]*b[i]
  end
  return z
end

rand(I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, B::Int) = rand(GLOBAL_RNG, I, B)
rand(rng::AbstractRNG, I::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, B::Int) = rand(rng, make(I, B))


RandomExtensions.maketype(I::AbsSimpleNumFieldOrderFractionalIdeal, ::Int) = AbsSimpleNumFieldElem

function rand(rng::AbstractRNG, sp::SamplerTrivial{<:Make2{AbsSimpleNumFieldElem,AbsSimpleNumFieldOrderFractionalIdeal,Int}})
  I, B = sp[][1:2]
  z = rand(rng, make(numerator(I), B))
  return divexact(elem_in_nf(z), denominator(I))::AbsSimpleNumFieldElem
  # type assert to help inference in Julia 1.0
end

rand(I::AbsSimpleNumFieldOrderFractionalIdeal, B::Int) = rand(GLOBAL_RNG, I, B)
rand(rng::AbstractRNG, I::AbsSimpleNumFieldOrderFractionalIdeal, B::Int) = rand(rng, make(I, B))

@doc raw"""
    pseudo_hnf(P::PMat)

Transforms $P$ into pseudo-Hermite form as defined by Cohen. Essentially the
matrix part of $P$ will be upper triangular with some technical normalisation
for the off-diagonal elements. This operation preserves the module.

A optional second argument can be specified as a symbols, indicating the desired
shape of the echelon form. Possible are
`:upperright` (the default) and `:lowerleft`
"""
function pseudo_hnf(P::PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}, shape::Symbol = :upperright, full_rank::Bool = false)
  if full_rank
    Q = pseudo_hnf_full_rank(P, shape)
    if is_square(matrix(Q))
      @hassert :PseudoHnf 1 det(Q) == det(P)
    end
    return Q
  else
    # TODO: If P is not of full rank and nrows(P) > ncols(P)
    # find_pseudo_hnf_modulus (called by pseudo_hnf_full_rank)
    # starts an infinite loop.
    Q = try
      QQ = pseudo_hnf_full_rank(P, shape)
      if is_square(matrix(P))
        @hassert :PseudoHnf 1 det(QQ) == det(P)
      end
      QQ
    catch e
      pseudo_hnf_kb(P, shape)
    end
    return Q
  end
end

@doc raw"""
    pseudo_hnf_with_transform(P::PMat)

Transforms $P$ into pseudo-Hermite form as defined by Cohen. Essentially the
matrix part of $P$ will be upper triangular with some technical normalisation
for the off-diagonal elements. This operation preserves the module.
The used transformation is returned as a second return value.

A optional second argument can be specified as a symbol, indicating the desired
shape of the echelon form. Possible are
`:upperright` (the default) and `:lowerleft`
"""
pseudo_hnf_with_transform(P::PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}, shape::Symbol = :upperright, full_rank::Bool = false) = pseudo_hnf_kb_with_transform(P, shape)

pseudo_hnf(P::PMat{T, S}, shape::Symbol = :upperright, full_rank::Bool = false) where {T <: NumFieldElem, S} = pseudo_hnf_kb(P, shape)

pseudo_hnf_with_transform(P::PMat{T, S}, shape::Symbol = :upperright, full_rank::Bool = false) where {T <: NumFieldElem, S} = pseudo_hnf_kb_with_transform(P, shape)

function pseudo_hnf_full_rank(P::PMat, shape::Symbol = :upperright)
  PP = deepcopy(P)
  K = parent(PP.matrix[1, 1])
  integralizer = _make_integral!(PP)
  m = find_pseudo_hnf_modulus(PP)
  PPhnf = pseudo_hnf_mod(PP, m, shape)
  invint = inv(K(integralizer))
  for i in 1:nrows(PP)
    PPhnf.coeffs[i] = PPhnf.coeffs[i]*invint
    simplify(PPhnf.coeffs[i])
  end
  return PPhnf
end

function pseudo_hnf_full_rank_with_modulus!(P::PMat, m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, shape::Symbol = :upperright)
  K = parent(P.matrix[1, 1])
  integralizer = _make_integral!(P)
  m = integralizer*m
  PPhnf = pseudo_hnf_mod(P, m, shape)
  for i in 1:nrows(PPhnf)
    PPhnf.coeffs[i] = PPhnf.coeffs[i]*inv(K(integralizer))
    simplify(PPhnf.coeffs[i])
  end
  return PPhnf
end

function pseudo_hnf_full_rank_with_modulus(P::PMat, m::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, shape::Symbol = :upperright)
  PP = deepcopy(P)
  return pseudo_hnf_full_rank_with_modulus!(PP, m, shape)
end

pseudo_hnf_full_rank_with_modulus(P::PMat, m::RelNumFieldOrderIdeal, shape::Symbol = :upperright) = pseudo_hnf_kb(P, shape)

function find_pseudo_hnf_modulus(P::PMat{T, S}) where {T, S}
  K = parent(P.matrix[1, 1])
  O = order(P.coeffs[1])
  if nrows(P) == ncols(P)
    m = det(P)
    simplify(m)
    return numerator(m)
  end
  p = next_prime(2^61)
  permGroup = SymmetricGroup(nrows(P))
  rowPerms = elem_type(permGroup)[]
  cnt = 0
  to_remove = Int[]
  while length(rowPerms) < 2 && cnt < min(5, ncols(P))
    cnt += 1
    lp = prime_ideals_over(O, p)
    for t in lp
      F, mF = residue_field(O, t)
      mFF = extend(mF, K)
      Pt = zero_matrix(F, nrows(P), ncols(P))
      nextIdeal = false
      for i = 1:nrows(P)
        if i in to_remove
          continue
        end
        for j = 1:ncols(P)
          try Pt[i, j] = mFF(P.matrix[i, j])
          catch
            nextIdeal = true
            break
          end
        end
        if nextIdeal
          break
        end
      end
      if nextIdeal
        continue
      end
      rowPerm = one(permGroup)
      rank = lu!(rowPerm, Pt)
      if rank == ncols(P) && !(rowPerm in rowPerms)
        j = 1
        while rowPerm[j] > ncols(P)
          j += 1
        end
        push!(to_remove, j)
        push!(rowPerms, rowPerm)
      end
    end
    p = next_prime(p)
  end
  dets = Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}()
  for s = 1:length(rowPerms)
    rowPerm = rowPerms[s]
    Minor = zero_matrix(K, ncols(P), ncols(P))
    C = Vector{S}(undef, ncols(P))
    for i = 1:nrows(P)
      if rowPerm[i] > ncols(P)
        continue
      end
      for j = 1:ncols(P)
        Minor[rowPerm[i], j] = P.matrix[i, j]
      end
      C[rowPerm[i]] = P.coeffs[i]
    end
    PMinor = pseudo_matrix(Minor, C)
    m1 = det(PMinor)
    simplify(m1)
    push!(dets, numerator(m1))
  end
  return sum(dets)
end

#TODO: das kann man besser machen
function _make_integral!(P::PMat{T, S}) where {T, S}
  K = parent(P.matrix[1, 1])
  O = order(P.coeffs[1])
  integralizer = one(FlintZZ)

  for i = 1:nrows(P)
    divide_row!(P.matrix, i, K(denominator(P.coeffs[i])))
    P.coeffs[i] = P.coeffs[i]*K(denominator(P.coeffs[i]))
    simplify(P.coeffs[i])
  end

  z = one(FlintZZ)
  for i in 1:nrows(P)
    for j in 1:ncols(P)
      z = lcm(z, denominator(P.matrix[i, j], O))
    end
  end

  PP = deepcopy(P.matrix)

  for i in 1:nrows(P)
    mul_row!(P.matrix, i, K(z))
  end

  return z
end

function pseudo_hnf_mod(P::PMat, m, shape::Symbol = :upperright, strategy = :split)
  O = order(m)

  t_comp_red = 0.0
  t_mod_comp = 0.0
  t_sum = 0.0
  t_div = 0.0
  t_idem = 0.0

  t_comp_red += @elapsed z = _matrix_for_reduced_span(P, m)
  @vprintln :PseudoHnf 1 "Computation of reduction: $t_comp_red"
  #return map_entries(lift, z)
  t_mod_comp += @elapsed zz = strong_echelon_form(z, shape, :no_split)
  @vprintln :PseudoHnf 1 "Modular computation: $t_mod_comp"

  res_mat = zero_matrix(nf(O), nrows(P), ncols(P))
  for i in 1:nrows(P)
    for j in 1:ncols(P)
      res_mat[i, j] = lift(zz[i, j]).elem_in_nf
    end
  end

  res = PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}(res_mat, copy(P.coeffs))

  shift = 0
  if shape == :lowerleft
    shift = nrows(P) - ncols(P)
  end

  for i in 1:ncols(P)
    if iszero(zz[i + shift, i])
      res.matrix[i + shift, i] = one(nf(O))
      res.coeffs[i + shift] = AbsSimpleNumFieldOrderFractionalIdeal(m, ZZRingElem(1))
    else
      o = ideal(O, lift(zz[i + shift, i]))
      t_sum += @elapsed g = o + m
      if isone(g)
        oo = o
        mm = m
      else
        t_div += @elapsed oo = divexact(o, g)
        @hassert :PseudoHnf g * oo == o
        t_div += @elapsed mm = divexact(m, g)
        @hassert :PseudoHnf mm * g == m
      end
      t_idem += @elapsed e, f = idempotents(oo, mm)
      res.coeffs[i + shift] = AbsSimpleNumFieldOrderFractionalIdeal(g, ZZRingElem(1))
      t = divexact(elem_in_nf(e), elem_in_nf(zz[i + shift, i].elem))
      mul_row!(res.matrix, i + shift, t)
      res.matrix[i + shift, i] = one(nf(O))
    end
  end

  if shape == :upperright
    t = nf(O)()
    for i = (ncols(res) - 1):-1:1
      for j = (i + 1):ncols(res)
        if iszero(res.matrix[i, j])
          continue
        end
        d = res.coeffs[j]//res.coeffs[i]
        q = mod(res.matrix[i, j], d)
        q = q - res.matrix[i, j]
        for c = j:ncols(res)
          mul!(t, q, res.matrix[j, c])
          addeq!(res.matrix[i, c], t)
        end
      end
    end
  elseif shape == :lowerleft
    t = nf(O)()
    for i = (shift + 2):nrows(res)
      for j = (i - shift - 1):-1:1
        if iszero(res.matrix[i, j])
          continue
        end
        d = res.coeffs[j + shift]//res.coeffs[i]
        q = mod(res.matrix[i, j], d)
        q = q - res.matrix[i, j]
        for c = 1:j
          mul!(t, q, res.matrix[j + shift, c])
          addeq!(res.matrix[i, c], t)
        end
      end
    end
  end

  #println("computation of ideal sum : $t_sum")
  #println("computation of ideal div : $t_div")
  #println("computation of idems     : $t_idem")

  return res
end

#this is Algorithm 4 of FH2014
# we assume that span(P) \subseteq O^r
function _matrix_for_reduced_span(P::PMat, m::AbsNumFieldOrderIdeal)
  O = order(m)
  Om, OtoOm = quo(O, m)
  z = zero_matrix(Om, nrows(P), ncols(P))
  if isone(m)
    return z
  end

  for i in 1:nrows(z)
    @vprintln :PseudoHnf 4 "New row"
    @vtime :PseudoHnf 4 I, a = _coprime_norm_integral_ideal_class(P.coeffs[i], m)
    @hassert :PseudoHnf 1 a * P.coeffs[i] == I
    @hassert :PseudoHnf is_integral(a * P.coeffs[i])
    @hassert :PseudoHnf is_coprime(norm(I), norm(m))
    n = norm(I, copy = false)
    qq = Om(invmod(n, minimum(m, copy = false)))
    @hassert :PseudoHnf isone(Om(n) * Om(qq))
    for j in 1:ncols(z)
      q = OtoOm(O(n*divexact(P.matrix[i, j], a)))
      z[i, j] = mul!(z[i, j], q, qq)
    end
  end
  return z
end

function _matrix_for_reduced_span(P::PMat, m::RelNumFieldOrderIdeal)
  O = order(m)
  Om, OtoOm = quo(O, m)
  z = zero_matrix(Om, nrows(P), ncols(P))
  if isone(m)
    return z
  end

  for i in 1:nrows(z)
    I, a = _coprime_norm_integral_ideal_class(P.coeffs[i], m)
    n = absolute_norm(I)
    Omn = OtoOm(O(n))
    qq = inv(Omn)
    for j in 1:ncols(z)
      @assert euclid(Omn) == 1
      q = OtoOm(O(n*divexact(P.matrix[i, j], a)))
      z[i, j] = mul!(z[i, j], q, qq)
    end
  end
  return z
end
(::AbsSimpleNumFieldOrderQuoRing)(a::AbsSimpleNumFieldOrderQuoRingElem) = a

_check(a) = a.has_coord ? dot(a.coordinates, basis(parent(a))) == a : true

function _check(m::Generic.Mat{AbsSimpleNumFieldOrderElem})
  for i in 1:nrows(m)
    for j in 1:ncols(m)
      if !_check(m[i, j].elem)
        println("$i $j not consistent: $(m[i, j]) : $(m[i, j].coordinates)")
        error("dasdsad")
      end
    end
  end
end

function _check(m::Generic.Mat{AbsSimpleNumFieldOrderQuoRingElem})
  for i in 1:nrows(m)
    for j in 1:ncols(m)
      if !_check(m[i, j].elem)
        println("$i $j not consistent: $(m[i, j].elem) : $(m[i, j].elem.coordinates)")
        error("dasdsad")
      end
    end
  end
end

function divide_row!(M::Generic.Mat{T}, i::Int, r::T) where T
  for j in 1:ncols(M)
    M[i, j] = divexact(M[i, j], r)
  end
  return nothing
end

function mul_row!(M::Generic.Mat{T}, i::Int, r::T) where T
  for j in 1:ncols(M)
    M[i, j] = mul!(M[i, j], M[i, j], r)
  end
  return nothing
end

function mul_col!(M::Generic.Mat{T}, i::Int, r::T) where T
  for j in 1:nrows(M)
    M[j, i] = mul!(M[j, i], M[j, i], r)
  end
  return nothing
end

function _contained_in_span_of_pseudohnf(v::Generic.Mat{T}, P::PMat{T, S}, shape::Symbol = :upperright) where {T, S}
  # accepts :upperright or :lowerleft for the shape of P
  (shape != :upperright && shape != :lowerleft) && error("Not yet implemented.")
  start = 1
  stop = nrows(P)
  step = 1
  if shape == :lowerleft
    start, stop = stop, start
    step = -1
  end
  w = deepcopy(v)
  for i = start:step:stop
    # find pivot
    if shape === :upperright
      piv = findfirst(k -> !iszero(P.matrix[i, k]), 1:ncols(P))::Int
    else
      piv = findlast(k -> !iszero(P.matrix[i, k]), 1:ncols(P))::Int
    end
    if !(w[1, piv]//P.matrix[i, piv] in P.coeffs[i])
      return false
    end
    e = w[1, piv]//P.matrix[i, piv]
    if shape == :upperright
      for j = piv:ncols(P)
        w[1, j] = w[1, j] - e*P.matrix[i, j]
      end
    elseif shape == :lowerleft
      for j = 1:piv
        w[1, j] = w[1, j] - e*P.matrix[i, j]
      end
    end
  end
  if !iszero(w)
    return false
  end
  return true
end

function _contained_in_span_of_pseudohnf(v::Generic.Mat{T}, a::S, P::PMat{T, S}, shape::Symbol = :upperright) where {T, S}
  # accepts :upperright or :lowerleft for the shape of P
  (shape != :upperright && shape != :lowerleft) && error("Not yet implemented.")
  start = 1
  stop = nrows(P)
  step = 1
  if shape == :lowerleft
    start, stop = stop, start
    step = -1
  end
  w = deepcopy(v)
  for i = start:step:stop
    # find pivot
    if shape === :upperright
      piv = findfirst(k -> !iszero(P.matrix[i, k]), 1:ncols(P))::Int
    else
      piv = findlast(k -> !iszero(P.matrix[i, k]), 1:ncols(P))::Int
    end

    if !(w[1, piv]//P.matrix[i, piv] in P.coeffs[i]*inv(a))
      return false
    end
    e = w[1, piv]//P.matrix[i, piv]
    if shape == :upperright
      for j = piv:ncols(P)
        w[1, j] = w[1, j] - e*P.matrix[i, j]
      end
    elseif shape == :lowerleft
      for j = 1:piv
        w[1, j] = w[1, j] - e*P.matrix[i, j]
      end
    end
  end
  if !iszero(w)
    return false
  end
  return true
end

function _spans_subset_of_pseudohnf(M::PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}, P::PMat{AbsSimpleNumFieldElem, AbsSimpleNumFieldOrderFractionalIdeal}, shape::Symbol = :upperright)
  # accepts :upperright or :lowerleft for the shape of P
  (shape != :upperright && shape != :lowerleft) && error("Not yet implemented.")
  for i in 1:nrows(M)
    A = M.coeffs[i]
    v = sub(M.matrix, i:i, 1:ncols(P))
    for b in basis(A.num)
      bb = divexact(elem_in_nf(b), A.den)
      if !Hecke._contained_in_span_of_pseudohnf(bb*v, P, shape)
        return false
      end
    end
  end
  return true
end

function _spans_subset_of_pseudohnf(M::PMat{T, S}, P::PMat{T, S}, shape::Symbol = :upperright) where {T, S}
  # accepts :upperright or :lowerleft for the shape of P
  (shape != :upperright && shape != :lowerleft) && error("Not yet implemented.")
  for i in 1:nrows(M)
    v = sub(M.matrix, i:i, 1:ncols(P))
    if !Hecke._contained_in_span_of_pseudohnf(v, M.coeffs[i], P, shape)
      return false
    end
  end
  return true
end

function sub(P::PMat, rows::AbstractUnitRange{Int}, cols::AbstractUnitRange{Int})
  m = sub(P.matrix, rows, cols)
  return pseudo_matrix(m, P.coeffs[rows])
end

function pseudo_hnf_cohen(P::PMat)
   return _pseudo_hnf_cohen(P, Val(false))
end

function pseudo_hnf_cohen_with_transform(P::PMat)
   return _pseudo_hnf_cohen(P, Val(true))
end

function _pseudo_hnf_cohen(P::PMat, ::Val{with_transform} = Val(false)) where with_transform
   H = deepcopy(P)
   m = nrows(H)
   if with_transform
      U = identity_matrix(base_ring(H.matrix), m)
      pseudo_hnf_cohen!(H, U, true)
      return H, U
   else
      U = similar(H.matrix, 0, 0)
      pseudo_hnf_cohen!(H, U, false)
      return H
   end
end

#=
Algorithm 2.6 in "Hermite and Smith normal form algorithms over Dedekind domains"
by H. Cohen.
=#
function pseudo_hnf_cohen!(H::PMat, U::Generic.Mat{T}, with_transform::Bool = false) where T <: AbsSimpleNumFieldElem
   m = nrows(H)
   n = ncols(H)
   A = H.matrix
   K = base_ring(A)
   t = K()
   t1 = K()
   t2 = K()
   k = 1
   for i = 1:n
      j = k
      while j <= m && A[j, i] == 0
         j += 1
      end
      if j > m
         continue
      end
      if j > k
         swap_rows!(H, j, k)
         with_transform ? swap_rows!(U, j, k) : nothing
      end
      H.coeffs[k] = H.coeffs[k]*A[k, i]
      simplify(H.coeffs[k])
      with_transform ? divide_row!(U, k, A[k, i]) : nothing
      divide_row!(A, k, A[k, i])
      for j = k+1:m
         if iszero(A[j, i])
            continue
         end
         Aji = deepcopy(A[j, i])
         a = H.coeffs[j]
         aa = Aji*a
         b = H.coeffs[k]
         d = aa + b
         ad = aa//d
         simplify(ad)
         bd = b//d
         simplify(bd)
         if ad.den != 1 || bd.den != 1
            error("Ideals are not integral.")
         end
         u, v = map(K, idempotents(ad.num, bd.num))
         u = divexact(u, Aji)
         for c = i:n
            t = deepcopy(A[j, c])
            mul!(t1, A[k, c], -Aji)
            addeq!(A[j, c], t1)
            mul!(t1, t, u)
            mul!(t2, A[k, c], v)
            add!(A[k, c], t1, t2)
         end
         if with_transform
            for c = 1:m
               t = deepcopy(U[j, c])
               mul!(t1, U[k, c], -Aji)
               addeq!(U[j, c], t1)
               mul!(t1, t, u)
               mul!(t2, U[k, c], v)
               add!(U[k, c], t1, t2)
            end
         end
         H.coeffs[j] = a*b//d
         simplify(H.coeffs[j])
         H.coeffs[k] = d
         simplify(H.coeffs[k])
      end
      if iszero(A[k, i])
         continue
      end
      for j = 1:k-1
         if iszero(A[j, i])
            continue
         end
         d = H.coeffs[k]//H.coeffs[j]
         q = mod(A[j, k], d)
         q = q - A[j, k]
         for c = k:n
            mul!(t, q, A[k, c])
            addeq!(A[j, c], t)
         end
         if with_transform
            for c = 1:m
               mul!(t, q, U[k, c])
               addeq!(U[j, c], t)
            end
         end
      end
      k += 1
   end
   return nothing
end

function swap_rows!(P::PMat, i::Int, j::Int)
   swap_rows!(P.matrix, i, j)
   P.coeffs[i], P.coeffs[j] = P.coeffs[j], P.coeffs[i]
   return nothing
end

function _in_span(v::Vector{AbsSimpleNumFieldElem}, P::PMat)
   @assert length(v) == ncols(P)
   m = nrows(P)
   n = ncols(P)
   K = base_ring(P.matrix)
   x = zeros(K, m)
   t = K()
   k = 1
   for i = 1:n
      s = K()
      for j = 1:k-1
         mul!(t, P.matrix[j, i], x[j])
         addeq!(s, t)
      end
      s = v[i] - s
      if iszero(P.matrix[k, i])
         if !iszero(s)
            return false, x
         end
         continue
      end
      x[k] = divexact(s, P.matrix[k, i])
      if !(x[k] in P.coeffs[k])
         return false, x
      end
      if k == min(m, n)
         break
      end
      k += 1
   end
   return true, x
end

function pseudo_hnf_kb(P::PMat, shape::Symbol = :upperright)
  if shape == :lowerleft
    H = _pseudo_hnf_kb(pseudo_matrix(reverse_cols(P.matrix), P.coeffs), Val(false))
    reverse_cols!(H.matrix)
    reverse_rows!(H.matrix)
    reverse!(H.coeffs)
    return H
  elseif shape == :upperright
    return _pseudo_hnf_kb(P, Val(false))
  else
    error("Not yet implemented")
  end
end

function pseudo_hnf_kb_with_transform(P::PMat, shape::Symbol = :upperright)
  if shape == :lowerleft
    H, U = _pseudo_hnf_kb(pseudo_matrix(reverse_cols(P.matrix), P.coeffs), Val(true))
    reverse_cols!(H.matrix)
    reverse_rows!(H.matrix)
    reverse!(H.coeffs)
    reverse_rows!(U)
    return H, U
  elseif shape == :upperright
    return _pseudo_hnf_kb(P, Val(true))
  else
    error("Not yet implemented")
  end
end

function _pseudo_hnf_kb(P::PMat, ::Val{with_transform} = Val(false)) where with_transform
   H = deepcopy(P)
   m = nrows(H)
   if with_transform
      U = identity_matrix(base_ring(H.matrix), m)
      pseudo_hnf_kb!(H, U, true)
      return H, U
   else
      U = similar(H.matrix, 0, 0)
      pseudo_hnf_kb!(H, U, false)
      return H
   end
end

function kb_search_first_pivot(H::PMat, start_element::Int = 1)
   for r = start_element:nrows(H)
      for c = start_element:ncols(H)
         if !iszero(H.matrix[r,c])
            return r, c
         end
      end
   end
   return 0, 0
end

# Reduces the row r with pivot in column c (so r = pivot[c]) with other known pivots
function kb_reduce_row!(H::PMat{T, S}, U::Generic.Mat{T}, pivot::Vector{Int}, c::Int, with_transform::Bool) where {T <: NumFieldElem, S}
   r = pivot[c]
   A = H.matrix
   t = base_ring(A)()
   for i = c+1:ncols(A)
      p = pivot[i]
      if p == 0 || iszero(A[r, i])
         continue
      end
      d = H.coeffs[p]//H.coeffs[r]
      q = mod(A[r, i], d)
      q = q - A[r, i]
      for j = i:ncols(A)
         mul!(t, q, A[p,j])
         addeq!(A[r,j], t)
      end
      if with_transform
         for j = 1:ncols(U)
            mul!(t, q, U[p,j])
            addeq!(U[r,j], t)
         end
      end
   end
   @vprintln :PseudoHnfKB "(Partially) reduced row $r"
   @vprintln :PseudoHnfKB A
   return nothing
end

# Reduces the entries of the column c with pivots "left from c", so in the columns 1:c - 1.
function kb_reduce_column!(H::PMat{T, S}, U::Generic.Mat{T}, pivot::Vector{Int}, c::Int, with_transform::Bool, start_element::Int = 1) where {T <: NumFieldElem, S}
   r = pivot[c]
   A = H.matrix
   t = base_ring(A)()
   for i = start_element:c-1
      p = pivot[i]
      if p == 0 || iszero(A[p, c])
         continue
      end
      d = H.coeffs[r]//H.coeffs[p]
      q = mod(A[p, c], d)
      q = q - A[p, c]
      for j = c:ncols(A)
         mul!(t, q, A[r,j])
         addeq!(A[p,j], t)
      end
      if with_transform
         for j = 1:ncols(U)
            mul!(t, q, U[r,j])
            addeq!(U[p,j], t)
         end
      end
   end
   @vprintln :PseudoHnfKB "(Partially) reduced column $c"
   @vprintln :PseudoHnfKB A
   return nothing
end

# Permute the rows to get an echelon shape
function kb_sort_rows!(H::PMat{T, S}, U::Generic.Mat{T}, pivot::Vector{Int}, with_transform::Bool, start_element::Int = 1) where {T <: NumFieldElem, S}
   m = nrows(H)
   n = ncols(H)
   pivot2 = zeros(Int, m)
   for i = 1:n
      if pivot[i] == 0
         continue
      end
      pivot2[pivot[i]] = i
   end

   r1 = start_element
   for i = start_element:n
      r2 = pivot[i]
      if r2 == 0
         continue
      end
      if r1 != r2
         swap_rows!(H, r1, r2)
         with_transform ? swap_rows!(U, r1, r2) : nothing
         p = pivot2[r1]
         pivot[i] = r1
         if p != 0
            pivot[p] = r2
         end
         pivot2[r1] = i
         pivot2[r2] = p
      end
      r1 += 1
      if r1 == m
         break
      end
   end
   return nothing
end

# Produce a 1 in entry (r, c) by pushing the entry into the coefficient ideal
function kb_produce_one!(H::PMat{T, S}, U::Generic.Mat{T}, r::Int, c::Int, with_transform::Bool) where {T <: NumFieldElem, S}
   A = H.matrix
   H.coeffs[r] = simplify(H.coeffs[r]*A[r, c])
   with_transform ? divide_row!(U, r, A[r, c]) : nothing
   divide_row!(A, r, A[r, c])
   return nothing
end

# For p = pivot[c], return the gcd and the idempotents of the coefficient ideals
# necessary to produce a zero in entry (r, c)
function kb_get_idempotents_for_entry(H::PMat{T, S}, pivot::Vector{Int}, r::Int, c::Int) where {T <: NumFieldElem, S}
   K = base_ring(H.matrix)
   p = pivot[c]
   a = H.coeffs[r]
   aa = H.matrix[r, c]*a
   b = H.coeffs[p]
   d = aa + b
   ad = simplify(aa//d)
   bd = simplify(b//d)
   if !is_integral(ad) || !is_integral(bd)
      error("Ideals are not integral.")
   end
   u, v = map(K, idempotents(numerator(ad, copy = false), numerator(bd, copy = false)))
   return d, u, v
end

function pseudo_hnf_kb!(H::PMat{T, S}, U::Generic.Mat{T}, with_transform::Bool = false, start_element::Int = 1) where {T <: NumFieldElem, S}
   m = nrows(H)
   n = ncols(H)
   A = H.matrix
   K = base_ring(A)
   pivot = zeros(Int, n)
   row1, col1 = kb_search_first_pivot(H, start_element)
   if row1 == 0
      return nothing
   end
   pivot[col1] = row1
   pivot_max = col1
   kb_produce_one!(H, U, row1, col1, with_transform)
   t = K()
   t1 = K()
   t2 = K()
   for i = row1 + 1:m
      @vprintln :PseudoHnfKB "Working in row $i..."
      new_pivot = false
      for j = start_element:pivot_max
         if iszero(A[i,j])
            continue
         end
         if pivot[j] == 0
            @vprintln :PseudoHnfKB "Found new pivot ($i, $j)"
            # We found a pivot for column j in row i
            pivot[j] = i
            pivot_max = max(pivot_max, j)
            new_pivot = true
            kb_produce_one!(H, U, i, j, with_transform)
         else
            # We have a pivot for column j in another row, so we can now produce
            # a 0 in the entry (i, j)
            p = pivot[j]
            Aij = deepcopy(A[i, j])
            d, u, v = kb_get_idempotents_for_entry(H, pivot, i, j)
            u = divexact(u, Aij)
            for c = j:n
               t = deepcopy(A[i, c])
               #t1 = mul!(t1, A[p, c], -Aij)
               mul!(t1, A[p, c], -Aij)
               #A[i, c] = addeq!(A[i, c], t1)
               addeq!(A[i, c], t1)
               #t1 = mul!(t1, t, u)
               mul!(t1, t, u)
               #t2 = mul!(t2, A[p, c], v)
               mul!(t2, A[p, c], v)
               #A[p, c] = add!(A[p, c], t1, t2)
               add!(A[p, c], t1, t2)
            end
            if with_transform
               for c = 1:m
                  t = deepcopy(U[i, c])
                  #t1 = mul!(t1, U[p, c], -Aij)
                  mul!(t1, U[p, c], -Aij)
                  #U[i, c] = addeq!(U[i, c], t1)
                  addeq!(U[i, c], t1)
                  #t1 = mul!(t1, t, u)
                  mul!(t1, t, u)
                  #t2 = mul!(t2, U[p, c], v)
                  mul!(t2, U[p, c], v)
                  #U[p, c] = add!(U[p, c], t1, t2)
                  add!(U[p, c], t1, t2)
               end
            end
            H.coeffs[i] = simplify(H.coeffs[i]*H.coeffs[p]//d)
            H.coeffs[p] = simplify(d)
            @vprintln :PseudoHnfKB "Produced 0 in entry ($i, $j)"
            @vprintln :PseudoHnfKB A
         end
         # Whether we found a pivot in column j (in row i) or produced a zero
         # using the pivot in column j in another row: We have to reduce the
         # row pivot[j] again.
         kb_reduce_row!(H, U, pivot, j, with_transform)
         kb_reduce_column!(H, U, pivot, j, with_transform, start_element)
         if new_pivot
            break
         end
      end
      if !new_pivot
         # We did not find a new pivot in row i in the so far known area
         for c = pivot_max+1:n
            if !iszero(A[i,c])
               @vprintln :PseudoHnfKB "Found new pivot ($i, $c) (second attempt)"
               pivot[c] = i
               pivot_max = max(pivot_max, c)
               kb_produce_one!(H, U, i, c, with_transform)
               kb_reduce_column!(H, U, pivot, c, with_transform, start_element)
               break
            end
         end
      end
      @vprintln :PseudoHnfKB ""
   end
   kb_sort_rows!(H, U, pivot, with_transform, start_element)
   return nothing
end

mutable struct PMat2
   parent
   matrix::Generic.MatSpaceElem{AbsSimpleNumFieldElem}
   row_coeffs::Vector{AbsSimpleNumFieldOrderFractionalIdeal}
   col_coeffs::Vector{AbsSimpleNumFieldOrderFractionalIdeal}

   function PMat2(m::Generic.MatSpaceElem{AbsSimpleNumFieldElem}, r::Vector{AbsSimpleNumFieldOrderFractionalIdeal}, c::Vector{AbsSimpleNumFieldOrderFractionalIdeal})
      z = new()
      z.matrix = m
      z.row_coeffs = r
      z.col_coeffs = c
      return z
   end
end

function show(io::IO, P::PMat2)
   print(io, "Pseudo-matrix over $(parent(P.matrix[1, 1]))\n")
   print(io, "$(P.matrix)\n")
   print(io, "\nwith row ideals\n")
   for I in P.row_coeffs
      show(IOContext(io, :compact => true), I)
      print(io, "\n")
   end
   print(io, "\nand column ideals")
   for I in P.col_coeffs
      print(io, "\n")
      show(IOContext(io, :compact => true), I)
   end
end

function pseudo_matrix2(m::Generic.Mat{AbsSimpleNumFieldElem}, r::Vector{AbsSimpleNumFieldOrderFractionalIdeal}, c::Vector{AbsSimpleNumFieldOrderFractionalIdeal})
   ( nrows(m) != length(r) || ncols(m) != length(c) ) && error("Dimensions do not match.")
   return PMat2(m, r, c)
end


function pseudo_matrix2(m::Generic.Mat{AbsSimpleNumFieldOrderElem}, r::Vector{AbsSimpleNumFieldOrderFractionalIdeal}, c::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}})
   mm = change_base_ring(nf(base_ring(m)), m)
   rr = map(z -> AbsSimpleNumFieldOrderFractionalIdeal(z, ZZRingElem(1)), r)
   cc = map(z -> AbsSimpleNumFieldOrderFractionalIdeal(z, ZZRingElem(1)), c)
   return PMat(mm, rr, cc)
end

function number_of_rows(m::PMat2)
   return number_of_rows(m.matrix)
end

function number_of_columns(m::PMat2)
   return number_of_columns(m.matrix)
end

function pseudo_snf_kb(P::PMat2)
   return _pseudo_snf_kb(P, Val(false))
end

function pseudo_snf_kb_with_transform(P::PMat2)
   return _pseudo_snf_kb(P, Val(true))
end

function _pseudo_snf_kb(P::PMat2, ::Val{with_transform} = Val(false)) where with_transform
   S = deepcopy(P)
   m = nrows(S)
   n = ncols(S)
   if with_transform
      U = identity_matrix(base_ring(S.matrix), m)
      K = identity_matrix(base_ring(S.matrix), m)
      pseudo_snf_kb!(S, U, K, true)
      return S, U, K
   else
      U = similar(S.matrix, 0, 0)
      K = U
      pseudo_snf_kb!(S, U, K, false)
      return S
   end
end

function kb_clear_row!(S::PMat2, K::Generic.Mat{AbsSimpleNumFieldElem}, i::Int, with_transform::Bool)
   m = nrows(S)
   n = ncols(S)
   A = S.matrix
   t = base_ring(A)()
   t1 = base_ring(A)()
   t2 = base_ring(A)()
   for j = i+1:n
      if A[i, j] == 0
         continue
      end
      #Just for debugging, this should not happen.
      if A[i, i] != 1
         error("Pivot is not 1.")
      end
      Aij = deepcopy(A[i, j])
      a = S.col_coeffs[j]
      aa = Aij*a
      b = S.col_coeffs[i]
      d = aa + b
      ad = aa//d
      simplify(ad)
      bd = b//d
      simplify(bd)
      if ad.den != 1 || bd.den != 1
         error("Ideals are not integral.")
      end
      u, v = map(base_ring(A), idempotents(ad.num, bd.num))
      u = divexact(u, Aij)
      for r = i:m
         t = deepcopy(A[r, j])
         mul!(t1, A[r, i], -Aij)
         addeq!(A[r,j], t1)
         mul!(t1, t, u)
         mul!(t2, A[r, i], v)
         add!(A[r, i], t1, t2)
      end
      if with_transform
         for r = 1:n
            t = deepcopy(K[r, j])
            mul!(t1, K[r, i], -Aij)
            addeq!(K[r,j], t1)
            mul!(t1, t, u)
            mul!(t2, K[r, i], v)
            add!(K[r, i], t1, t2)
         end
      end
      S.col_coeffs[j] = a*b//d
      simplify(S.col_coeffs[j])
      S.col_coeffs[i] = d
      simplify(S.col_coeffs[i])
   end
   return nothing
end

function pseudo_snf_kb!(S::PMat2, U::Generic.Mat{AbsSimpleNumFieldElem}, K::Generic.Mat{AbsSimpleNumFieldElem}, with_transform::Bool = false)
   m = nrows(S)
   n = ncols(S)
   A = S.matrix
   l = min(m,n)
   i = 1
   t = base_ring(A)()
   t1 = base_ring(A)()
   t2 = base_ring(A)()
   H = pseudo_matrix(A, S.row_coeffs)
   if !iszero(A[1, 1])
      S.row_coeffs[1] = S.row_coeffs[1]*A[1, 1]
      simplify(S.row_coeffs[1])
      with_transform ? divide_row!(U, 1, A[1, 1]) : nothing
      divide_row!(A, 1, A[1, 1])
   end
   while i<=l
      !iszero(A[i, i]) ? kb_clear_row!(S, K, i, with_transform) : nothing
      pseudo_hnf_kb!(H, U, with_transform, i)
      c = i + 1
      while c <= n && iszero(A[i, c])
         c += 1
      end
      if c != n + 1
         continue
      end
      i += 1
   end
   return nothing
end

mutable struct ModDed
   pmatrix::PMat
   base_ring::AbsSimpleNumFieldOrder
   is_triu::Bool
   function ModDed(P::PMat, is_triu::Bool = false; check::Bool = true)
      if check
         is_triu = is_upper_triangular(P.matrix)
      end
      z = new()
      z.pmatrix = P
      z.base_ring = order(P.coeffs[1])
      z.is_triu = is_triu
      return z
   end
end

base_ring(M::ModDed) = M.base_ring

function show(io::IO, M::ModDed)
   print(io, "Module over $(M.base_ring) with defining pseudo-matrix")
   for i in 1:nrows(M.pmatrix.matrix)
      print(io, "\n")
      show(IOContext(io, :compact => true), M.pmatrix.coeffs[i])
      print(io, " with row $(sub(M.pmatrix.matrix, i:i, 1:ncols(M.pmatrix.matrix)))")
   end
end

ModDed(m::Generic.Mat{AbsSimpleNumFieldElem}, is_triu::Bool = false; check::Bool = true) = ModDed(pseudo_matrix(m), is_triu; check = check)

ModDed(m::Generic.Mat{AbsSimpleNumFieldOrderElem}, is_triu::Bool = false; check::Bool = true) = ModDed(pseudo_matrix(m), is_triu; check = check)

ModDed(c::Vector{AbsSimpleNumFieldOrderFractionalIdeal}) = ModDed(pseudo_matrix(c), true; check = false)

ModDed(c::Vector{AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}}) = ModDed(pseudo_matrix(c), true; check = false)

function in(v::Vector{AbsSimpleNumFieldElem}, M::ModDed)
   P = M.pmatrix
   if !M.is_triu
      P = pseudo_hnf_kb(M.pmatrix)
   end
   return _in_span(v, P)[1]
end

function simplify_basis!(M::ModDed)
   if !M.is_triu
      pseudo_hnf_kb!(M.pmatrix, M.pmatrix.matrix, false)
   end
   M.is_triu = true
   P = M.pmatrix
   r = nrows(P)
   for i = nrows(P):-1:1
      if !is_zero_row(P.matrix, i)
         break
      end
      r -= 1
   end
   deleteat!(P.coeffs, r + 1:nrows(P))
   t = reshape(P.matrix.entries, nrows(P)*ncols(P))
   for i = nrows(P):-1:r + 1
      deleteat!(t, [ i*j for j in 1:ncols(P)])
   end
   P.matrix.entries = reshape(t, r, ncols(P))
   return nothing
end

function simplify_basis(M::ModDed)
   N = deepcopy(M)
   simplify_basis!(N)
   return N
end

#function _vcat(P::PMat, Q::PMat)
#   @assert base_ring(P.matrix) == base_ring(Q.matrix)
#   m = vcat(P.matrix, Q.matrix)
#   c = vcat(P.coeffs, Q.coeffs)
#   return pseudo_matrix(m, c)
#end

function vcat(A::Vector{PMat{S, T}}) where {S, T}
  m = reduce(vcat, dense_matrix_type(S)[P.matrix for P in A])
  c = reduce(vcat, Vector{T}[P.coeffs for P in A])::Vector{T}
  return pseudo_matrix(m, c)
end

function vcat(A0::PMat, A::PMat...)
  return vcat(collect((A0, A...)))
end

function _hcat(P::PMat, Q::PMat)
   @assert base_ring(P.matrix) == base_ring(Q.matrix)
   @assert P.coeffs == Q.coeffs
   m = hcat(P.matrix, Q.matrix)
   return pseudo_matrix(m, P.coeffs)
end

function hcat(A::Vector{ <: PMat })
  @assert all( P -> P.coeffs == A[1].coeffs, A)
  m = reduce(hcat, [P.matrix for P in A])
  return pseudo_matrix(m, A[1].coeffs)
end

function hcat(A0::PMat, A::PMat...)
  return hcat(collect((A0, A...)))
end

function +(M::ModDed, N::ModDed)
   @assert base_ring(M) == base_ring(N)
   m = deepcopy(M.pmatrix)
   n = deepcopy(N.pmatrix)
   mn = vcat(m, n)
   MN = ModDed(mn; check = false)
   simplify_basis!(MN)
   return MN
end

function intersect(M::ModDed, N::ModDed)
   @assert base_ring(M) == base_ring(N)
   @assert ncols(M.pmatrix) == ncols(N.pmatrix)
   MM = simplify_basis(M)
   NN = simplify_basis(N)
   A = deepcopy(MM.pmatrix)
   B = deepcopy(NN.pmatrix)
   if nrows(B) > nrows(A)
      A, B = B, A
   end
   C1 = hcat(A, deepcopy(A))
   m = zero_matrix(base_ring(B.matrix), nrows(B), ncols(B))
   C2 = hcat(B, pseudo_matrix(m, B.coeffs))
   C = vcat(C1, C2)
   # C = [A A; B 0]
   pseudo_hnf_kb!(C, C.matrix, false)
   for i = 1:nrows(B)
      for j = 1:ncols(B)
         m[i, j] = C.matrix[i + nrows(A), j + ncols(A)]
      end
   end
   D = pseudo_matrix(m, C.coeffs[nrows(A) + 1:nrows(C)])
   MN = ModDed(D, true; check = false)
   simplify_basis!(MN)
   return MN
end

function mod(M::ModDed, p::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
   O = base_ring(M)
   Op = residue_ring(O, p)
   N = zero_matrix(Op, nrows(M.pmatrix), ncols(M.pmatrix))
   MM = M.pmatrix.matrix
   ideals = M.pmatrix.coeffs
   for i = 1:nrows(N)
      a = numerator(ideals[i]).gen_one
      if valuation(a, p) > valuation(numerator(ideals[i]).gen_two, p)
         a = numerator(ideals[i]).gen_two
      end
      for j = 1:ncols(N)
         N[i, j] = Op(O(MM[i, j]*a))
      end
   end
   return N
end

################################################################################
#
#  Print the size of a pseudo matrix
#
################################################################################

# Just for debugging
# Prints the size of the ideals/entries of a pseudo matrix
# The first column is nbits(norm(numerator)) + nbits(denominator) of the ideal
# The rest of entries are nbits(max(numerator)) + nbits(denominator)
# (The size of the entries is with respect the equation order
function size(A::PMat)
  K = parent(A.matrix[1, 1])

  println("Size is:")
  size = Array{String}(nrows(A), ncols(A) + 2)
  for i in 1:nrows(A)
    size[i, 1] = "$i"
    size[i, 2] = "$(nbits(norm(numerator(A.coeffs[i])))) $(nbits(denominator(A.coeffs[i])))"
  end
  for i in 1:nrows(A)
    for j in 1:ncols(A)
      if iszero(A.matrix[i, j])
        size[i, j + 2] = "0"
      else
        a = numerator(A.matrix[i, j])
        b = denominator(A.matrix[i, j])
        size[i, j + 2] = "$(nbits(maximum([ZZ(coeff(a, i)) for i in 0:degree(K) - 1]))) $(nbits(b))"
      end
    end
  end
  display(size)
end

function is_pseudo_hnf(M, shape::Symbol = :lowerleft)
  return is_triangular(M.matrix, shape)
end

function test_triangular()
  M = zero_matrix(FlintZZ, 3, 3)

  M = FlintZZ[1 0 0;
              0 1 0;
              0 0 1]

  @assert is_triangular(M)

  M = FlintZZ[0 0 0;
              0 1 0;
              0 0 1]

  @assert is_triangular(M)

  M = FlintZZ[1 0 0;
              0 0 0;
              0 0 1]

  @assert !is_triangular(M)

  M = FlintZZ[0 1 0;
              0 0 1;
              0 0 0]

  @assert !is_triangular(M)

  M = FlintZZ[1 0 0;
              0 1 0;
              0 0 0]

  @assert !is_triangular(M)

  M = FlintZZ[0 1 0;
              1 0 0;
              0 0 1]

  @assert !is_triangular(M)
end

function is_triangular(M::MatElem, shape::Symbol = :lowerleft)
  r = nrows(M)
  c = ncols(M)

  if shape == :lowerleft

    piv = 0

    k = 1
    while is_zero_row(M, k) && k <= r
      k = k + 1
    end
    if k == r + 1
      return true # Zero matrix
    end

    for i in k:r
      for j in c:-1:1
        if !iszero(M[i, j])
          if j <= piv
            return false
          else
            piv = j
            break
          end
        end
        if j == 1 && piv != 0
          piv = 0
        end
      end
      if piv > 0
        continue
      end
      return false # There should not be a zero row
    end
    return true
  elseif shape == :upperright
    return is_triangular(transpose(M), :lowerleft)
  end
end

function Base.hash(P::PMat, h::UInt)
  h = Base.hash(P.matrix, h)
  return Base.hash(P.coeffs, h)
end

# Returns x in K with xa integral and coprime to m

function integral_and_coprime_to(a::AbsSimpleNumFieldOrderFractionalIdeal, m::AbsNumFieldOrderIdeal)
  O = order(m)
  b = inv(a)
  B = absolute_basis(b)
  while true
    z = rand(B, -10:10)
    if iszero(z)
      continue
    end
    I = z * a
    I = simplify(I)
    @assert denominator(I) == 1
    if is_coprime(I.num, m)
      return z
    end
  end
end

function integral_and_coprime_to(a::Union{ AbsSimpleNumFieldOrderFractionalIdeal, RelNumFieldOrderFractionalIdeal }, m::Union{ AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal })
  O = order(m)

  facm = factor(m)
  faca = factor(a)

  primes = Vector{ideal_type(O)}()
  v = Vector{Int}()
  for (p, e) in faca
    if e < 0
      push!(primes, p)
      push!(v, -e)
    end
  end

  for (p, e) in facm
    if haskey(faca, p)
      if faca[p] >= 0
        push!(primes, p)
        push!(v, -faca[p])
      end
    else
      push!(primes, p)
      push!(v, ZZRingElem(0))
    end
  end

  if isempty(primes)
    return one(nf(O))
  end

  return approximate(v, primes)
end

function steinitz_form(P::PMat)
  return _steinitz_form(P, Val(false))
end

function steinitz_form_with_transform(P::PMat)
  return _steinitz_form(P, Val(true))
end

function _steinitz_form(P::PMat, ::Val{with_transform} = Val(false)) where with_transform
  if with_transform
    S, U = pseudo_hnf_with_transform(P, :lowerleft)
  else
    S = pseudo_hnf(P, :lowerleft)
  end

  K = base_ring(S.matrix)
  oneK = one(K)
  O = order(S.coeffs[1])
  start_row = 1
  for i = 1:nrows(S)
    if !iszero(S.matrix[i, 1])
      start_row = i
      break
    end
    S.coeffs[i] = oneK*O
  end
  if with_transform
    steinitz_form!(S, U, true, start_row)
    return S, U
  else
    U = similar(S.matrix, 0, 0)
    steinitz_form!(S, U, false, start_row)
    return S
  end
end

# Algorithm 4.6.2 in Hoppe: Normal forms over Dedekind domains
function steinitz_form!(M::PMat{T, S}, U::Generic.Mat{T}, with_transform::Bool = false, start_row::Int = 1) where { T <: NumFieldElem, S }
  if nrows(M) < start_row
    return nothing
  end

  A = M.matrix
  K = base_ring(A)
  oneK = one(K)
  t = K()
  t1 = K()
  O = order(M.coeffs[1])
  for r = start_row:nrows(M) - 1
    a = M.coeffs[r]

    if isone(a)
      continue
    end

    if isone(M.coeffs[r + 1])
      swap_rows!(M, r, r + 1)
      continue
    end

    if a isa AbsSimpleNumFieldOrderFractionalIdeal && a.num.is_principal == 1
      x = divexact(K(a.num.princ_gen), K(a.den))
      mul_row!(A, r, x)
      with_transform ? divide_row!(U, r, x) : nothing
      M.coeffs[r] = oneK*O
      continue
    end


    b = M.coeffs[r + 1]
    # Hoppe, Algorithm 1.8.5
    d = lcm(denominator(a), denominator(b))
    ad = simplify(a*d)
    bd = simplify(b*d)
    @assert denominator(ad) == 1 && denominator(bd) == 1
    ad = numerator(ad)
    bd = numerator(bd)
    iad = inv(ad)
    m1 = integral_and_coprime_to(iad, bd)
    mad = simplify(m1*iad)
    @assert denominator(mad) == 1
    x, m2 = idempotents(numerator(mad), bd)
    @assert x + m2 == 1
    m1 = divexact(m1, d)
    m2 = divexact(elem_in_nf(m2), d)
    @assert x + d * m2 == 1
    n1 = divexact(x, m1)
    @assert n1 * m1 + d * m2 == 1
    n2 = K(-1)*d
    # We now have m1 in a, m2 in b and n1 in a^-1, n2 in b^-1 with m1n1 - m2n2 = 1
    @assert m1 in a
    @assert m2 in b
    @assert n1 in inv(a)
    @assert n2 in inv(b)
    @assert m1 * n1 - m2*n2 == 1

    for c = 1:ncols(M)
      t = deepcopy(A[r, c])

      A[r, c] = mul!(A[r, c], A[r, c], m1)
      t1 = mul!(t1, A[r + 1, c], m2)
      A[r, c] = add!(A[r, c], A[r, c], t1)

      t1 = mul!(t1, t, n2)
      A[r + 1, c] = mul!(A[r + 1, c], A[r + 1, c], n1)
      A[r + 1, c] = add!(A[r + 1, c], A[r + 1, c], t1)
    end

    if with_transform
      for c = 1:ncols(U)
        t = deepcopy(U[r, c])

        U[r, c] = mul!(U[r, c], U[r, c], m1)
        t1 = mul!(t1, U[r + 1, c], m2)
        U[r, c] = add!(U[r, c], U[r, c], t1)

        t1 = mul!(t1, t, n2)
        U[r + 1, c] = mul!(U[r + 1, c], U[r + 1, c], n1)
        U[r + 1, c] = add!(U[r + 1, c], U[r + 1, c], t1)
      end
    end

    M.coeffs[r] = oneK*O
    M.coeffs[r + 1] = a*b
  end
  return nothing
end

################################################################################
#
#  Inverse
#
################################################################################

function inv(x::Generic.MatSpaceElem{AbsSimpleNumFieldOrderElem})
  R = base_ring(x)
  K = nf(R)
  return change_base_ring(R, inv(change_base_ring(K, x)))
end
