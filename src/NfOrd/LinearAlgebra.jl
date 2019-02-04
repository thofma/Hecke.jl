export pseudo_matrix, pseudo_hnf, PseudoMatrix, pseudo_hnf_with_trafo

function _det_bound(M::Generic.Mat{NfOrdElem})
  n = nrows(M)
  O = base_ring(M)
  d = degree(O)
  c1, c2 = Hecke.norm_change_const(O)

  return fmpz(BigInt(ceil(sqrt(c2)*c1^(n/2)*BigInt(n)^n*BigInt(d)^n*BigInt(_max_max(M))^n)))
end

function _max_max(M::Generic.Mat{NfOrdElem})
  d = FlintZZ(1)
  for i in 1:nrows(M)
    for j in 1:ncols(M)
      if !iszero(M[i, j])
        v = elem_in_basis(M[i, j])
        for k in degree(base_ring(M))
          d = max(d, abs(v[k]))
        end
      end
    end
  end
  return d
end
  
#function det(M::Generic.Mat{NfOrdElem})
#  O = base_ring(M)::NfOrd
#  B = _det_bound(M)
#  p = next_prime(2^60) # magic numbers
#  P = fmpz(1)
#  i = 1
#  res = zero(O)
#  t = 0.0
#  while P < 2*B
#    # reject some bad primes
#    if true  
#      #println("$p");
#      Omodp, pi_p = quo(O, ideal(O, p))
#      Mmodp = MatrixSpace(Omodp, nrows(M), ncols(M))(M)
#      t += @elapsed detmodp = pi_p\Hecke.det(Mmodp)
#      if i == 1
#        res = detmodp
#      elseif i >= 2
#        g, e, f = gcdx(P, fmpz(p))
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

function _get_coeff_raw(x::nmod_poly, i::Int)
  u = ccall((:nmod_poly_get_coeff_ui, :libflint), UInt, (Ref{nmod_poly}, Int), x, i)
  return u
end

@doc Markdown.doc"""
    det(M::Generic.Mat{NfOrdElem}) -> NfOrdElem
> Uses a modular algorithm to compute the determinant.    
"""   
function det(M::Generic.Mat{NfOrdElem})
  O = base_ring(M)::NfOrd
  K = nf(O)
  B = _det_bound(M)
  p = next_prime(p_start) #global  
  P = fmpz(1)
  i = 1
  res = O()
  t_det = 0.0
  t_reducing = 0.0
  t_splitting = 0.0
  used_primes = Array{UInt, 1}()
  tmp_polys = Array{nf_elem, 1}()

  while P < 2*B
    # reject some bad primes
    if isindex_divisor(O, p) 
      continue
    end

    ttt = @elapsed me = modular_init(K, p)

    push!(used_primes, UInt(p))

    t_splitting += ttt

    detmodp = nmod_poly(UInt(p))

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

  fc = crt_env(fmpz[x for x = used_primes])
  fv = Array{fmpz}(undef, length(used_primes))
  for i=1:length(used_primes)
    fv[i] = fmpz(0)
  end
  zz = fmpz()

  @assert length(used_primes) == length(tmp_polys)

  tmp_fmpz_poly = PolynomialRing(FlintZZ)[1]()

  for i in 0:degree(O)
    for j=1:length(used_primes)
      Nemo.num_coeff!(fv[j], tmp_polys[j], i)
    end
    crt!(zz, fv, fc)
    setcoeff!(tmp_fmpz_poly, i, zz)
  end

  tut = fmpq_poly(tmp_fmpz_poly)
  tut.parent = parent(nf(O).pol)
  res = mod_sym(O(nf(O)(tut)), P)
  
  #println("Modular determinant time: $t_det");
  #println("Time for reducing: $t_reducing");
  #println("Time for splitting: $t_splitting");
  #println("Used $(length(used_primes)) primes")

  return res
end

# s, t are auxillary variables, r1, r2 are the residues, m1, m2 are the moduli
# aliasing is not allowed (?)
function crt!(z::nmod_poly, r1::nmod_poly, r2::Union{nmod_poly, fq_nmod}, m1::nmod_poly, m2::nmod_poly, s::nmod_poly, t::nmod_poly)
  ccall((:nmod_poly_xgcd, :libflint), Nothing, (Ref{nmod_poly}, Ref{nmod_poly}, Ref{nmod_poly}, Ref{nmod_poly}, Ref{nmod_poly}), z, s, t, m1, m2)
  @assert Bool(ccall((:nmod_poly_is_one, :libflint), Cint, (Ref{nmod_poly}, ), z))
  # z = s*m1*r2 + t*m2*r1
  mul!(z, s, m1)
  ccall((:nmod_poly_mul, :libflint), Nothing, (Ref{nmod_poly}, Ref{nmod_poly}, Ref{fq_nmod}), z, z, r2)
  mul!(t, t, m2)
  mul!(t, t, r1)
  add!(z, z, t)
  mul!(s, m1, m2)
  rem!(z, z, s)  
end

function set!(z::nmod_poly, x::nmod_poly)
  ccall((:nmod_poly_set, :libflint), Nothing, (Ref{nmod_poly}, Ref{nmod_poly}), z, x)
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

@doc Markdown.doc"""
    mod_sym(a::NfOrdElem, m)
> Reduces the coefficients of $a$ modulo $m$, using the symmetric residue system.    
"""
function mod_sym(x::NfOrdElem, m)
  z = elem_in_basis(x)
  for i in 1:length(z)
    z[i] = mod(z[i], m)
    if 2*z[i] > m
      z[i] = z[i] - m
    end
  end
  return parent(x)(z)
end

function _basis_coord_nonneg(x::NfOrdElem)
  b = elem_in_basis(x)
  for i in 1:length(b)
    if b[i] < 0
      return false
    end
  end
  return true
end

function rand(M::Generic.MatSpace{NfOrdElem}, B::Union{Int, fmpz})
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
    if x != :parent && isdefined(P, x)
      setfield!(z, x, Base.deepcopy_internal(getfield(P, x), dict))
    end
  end
  if isdefined(P, :parent)
    z.parent = P.parent
  end
  return z
end

function show(io::IO, P::PMat)
  compact = get(io, :compact, false)
  if compact
    for i in 1:nrows(P.matrix)
      i == 1 || print(io, "\n")
      print(io, "(")
      show(IOContext(io, :compact => true), P.coeffs[i])
      print(io, ") * ")
      print(io, sub(P.matrix, i:i, 1:ncols(P.matrix)))
    end
  else
    print(io, "Pseudo-matrix over $(parent(P.matrix[1, 1]))")
    for i in 1:nrows(P.matrix)
      print(io, "\n")
      show(IOContext(io, :compact => true), P.coeffs[i])
      print(io, " with row $(sub(P.matrix, i:i, 1:ncols(P.matrix)))")
    end
  end
end

function PseudoMatrix(m::Generic.Mat{T}, c::Array{S, 1}) where {T, S}
  # sanity checks
  @assert nrows(m) == length(c)
  return PMat{T, S}(m ,c)
end

@doc Markdown.doc"""
    PseudoMatrix(m::Generic.Mat{nf_elem}, c::Array{NfOrdIdl, 1}) -> PMat{nf_elem, NfOrdFracIdl}

> Returns the (row) pseudo matrix representing the Z\_k-module 
>  $$\sum c_i m_i$$
>  where $c_i$ are the ideals in $c$ and $m_i$ the rows of $M$. 
"""
function PseudoMatrix(m::Generic.Mat{nf_elem}, c::Array{NfOrdIdl, 1})
  @assert nrows(m) == length(c)
  cc = map(z -> NfOrdFracIdl(z, fmpz(1)), c)
  return PMat{nf_elem, NfOrdFracIdl}(m, cc)
end

@doc Markdown.doc"""
    PseudoMatrix(m::Generic.Mat{NfOrdElem}, c::Array{NfOrdIdl, 1}) -> PMat{nf_elem, NfOrdFracIdl}
> Returns the (row) pseudo matrix representing the $Z_k$-module 
>  $$\sum c_i m_i$$
>  where $c_i$ are the ideals in $c$ and $m_i$ the rows of $M$. 
"""
function PseudoMatrix(m::Generic.Mat{NfOrdElem}, c::Array{NfOrdIdl, 1})
  @assert nrows(m) == length(c)
  mm = change_ring(m, nf(base_ring(m)))
  cc = map(z -> NfOrdFracIdl(z, fmpz(1)), c)
  return PMat{nf_elem, NfOrdFracIdl}(mm, cc)
end

@doc Markdown.doc"""
    PseudoMatrix(m::Generic.Mat{NfOrdElem}, c::Array{NfOrdIdl, 1}) -> PMat{nf_elem, NfOrdFracIdl}
> Returns the free (row) pseudo matrix representing the $Z_k$-module 
>  $$\sum Z_k m_i$$
>  where $m_i$ the rows of $M$. 
"""
function PseudoMatrix(m::Generic.Mat{nf_elem})
   K = base_ring(m)
   O = maximal_order(K)
   return PseudoMatrix(m, [ideal(O, K(1)) for i = 1:nrows(m)])
end

function PseudoMatrix(m::Generic.Mat{S}) where S <: RelativeElement
  L = base_ring(m)
  OL = maximal_order(L)
  K = base_ring(L)
  OK = maximal_order(K)
  return PseudoMatrix(m, [ frac_ideal(OL, identity_matrix(K, degree(L))) for i = 1:nrows(m) ])
end

function PseudoMatrix(m::Generic.Mat{S}, c::Array{T, 1}) where {S <: RelativeElement, T <: NfRelOrdIdl}
  @assert nrows(m) == length(c)
  cc = [ frac_ideal(order(c[i]), basis_pmat(c[i]), true) for i = 1:length(c) ]
  return PMat{S, typeof(cc[1])}(m, cc)
end

PseudoMatrix(m::Generic.Mat{NfOrdElem}) = PseudoMatrix(change_ring(m, nf(base_ring(m))))

function PseudoMatrix(c::Array{S, 1}) where S
   K = nf(order(c[1]))
   m = identity_matrix(K, length(c))
   return PseudoMatrix(m, c)
end

PseudoMatrix(c::Array{NfOrdIdl, 1}) = PseudoMatrix(map(z -> NfOrdFracIdl(z, fmpz(1)), c))

function nrows(m::PMat)
  return nrows(m.matrix)
end

function ncols(m::PMat)
  return ncols(m.matrix)
end

function change_ring(m::Generic.Mat{NfOrdElem}, K::AnticNumberField)
  return matrix(K, map(z -> K(z), m.entries))
end

function det(m::PMat)
  z = m.coeffs[1]
  for i in 2:nrows(m)
    if isdefined(z.num, :gen_two) && isdefined(m.coeffs[i].num, :gen_two)
    end
    z = z*m.coeffs[i]
  end
  return det(m.matrix)*z
end

# this is slow
function _coprime_integral_ideal_class(x::Union{NfOrdFracIdl, NfOrdIdl}, y::NfOrdIdl)
  O = order(y)
  #c = conjugates_init(nf(O).pol)
  #num_x_inv = inv(numerator(x))
  x_inv = inv(x)
  check = true
  z = ideal(O, O(1))
  a = nf(O)()
  i = 0
  while check
    i += 1
    a = rand(x_inv, 10)
    b = x*a
    z = divexact(numerator(b), denominator(b))
    norm(z + y) == 1 ? (check = false) : (check = true)
  end
  return z, a
end

function _coprime_integral_ideal_class(x::FacElem{NfOrdIdl, NfOrdIdlSet}, y::NfOrdIdl)
  D = typeof(x.fac)()
  D2 = Dict{nf_elem, fmpz}()
  O = order(y)
  for (I, e) in x
    II, a = _coprime_integral_ideal_class(I, y)
    D[II] = e
    D2[a] = e
  end
  return FacElem(D), FacElem(D2)
end

# this is slow
function _coprime_norm_integral_ideal_class(x::NfOrdFracIdl, y::NfOrdIdl)
  # x must be nonzero
  O = order(y)
  c = conjugates_init(nf(O).pol)
  #num_x_inv = inv(numerator(x))
  x_inv = inv(x)
  check = true
  z = ideal(O, O(1))
  a = nf(O)()
  i = 0
  while check
    i += 1
    a = rand(x_inv, 10)
    if a == 0
      continue
    end
    b = x*a
    z = divexact(numerator(b), denominator(b))
    gcd(norm(z), norm(y)) == 1 ? (check = false) : (check = true)
  end
  @assert gcd(norm(z), norm(y)) == 1
  return z, a 
end

function rand(I::Union{NfOrdIdl, AlgAssAbsOrdIdl}, B::Int)
  r = rand(-B:B, degree(order(I)))
  b = basis(I)
  z = r[1]*b[1]
  for i in 2:degree(order(I))
    z = z + r[i]*b[i]
  end
  return z
end

function rand(I::NfOrdFracIdl, B::Int)
  z = rand(numerator(I), B)
  return divexact(elem_in_nf(z), denominator(I))
end

function pseudo_hnf(P::PMat{nf_elem, NfOrdFracIdl}, shape::Symbol = :upperright, full_rank::Bool = false)
  if full_rank
    return pseudo_hnf_full_rank(P, shape)
  else
    # TODO: If P is not of full rank and nrows(P) > ncols(P)
    # find_pseudo_hnf_modulus (called by pseudo_hnf_full_rank)
    # starts an infinite loop.
    Q = try pseudo_hnf_full_rank(P, shape)
    catch e
      rethrow(e)
      pseudo_hnf_kb(P, shape)
    end
    return Q
  end
end

pseudo_hnf_with_trafo(P::PMat{nf_elem, NfOrdFracIdl}, shape::Symbol = :upperright, full_rank::Bool = false) = pseudo_hnf_kb_with_trafo(P, shape)

pseudo_hnf(P::PMat{T, S}, shape::Symbol = :upperright, full_rank::Bool = false) where {T <: RelativeElement, S} = pseudo_hnf_kb(P, shape)

pseudo_hnf_with_trafo(P::PMat{T, S}, shape::Symbol = :upperright, full_rank::Bool = false) where {T <: RelativeElement, S} = pseudo_hnf_kb_with_trafo(P, shape)

function pseudo_hnf_full_rank(P::PMat, shape::Symbol = :upperright)
  PP = deepcopy(P)
  K = parent(PP.matrix[1, 1])
  integralizer = _make_integral!(PP)
  m = find_pseudo_hnf_modulus(PP)
  PPhnf = pseudo_hnf_mod(PP, m, shape)
  for i in 1:nrows(PP)
    PPhnf.coeffs[i] = PPhnf.coeffs[i]*inv(K(integralizer))
    simplify(PPhnf.coeffs[i])
  end
  return PPhnf
end

function pseudo_hnf_full_rank_with_modulus(P::PMat, m::NfOrdIdl, shape::Symbol = :upperright)
  PP = deepcopy(P)
  K = parent(PP.matrix[1, 1])
  integralizer = _make_integral!(PP)
  m = integralizer*m
  PPhnf = pseudo_hnf_mod(PP, m, shape)
  for i in 1:nrows(PP)
    PPhnf.coeffs[i] = PPhnf.coeffs[i]*inv(K(integralizer))
    simplify(PPhnf.coeffs[i])
  end
  return PPhnf
end

function find_pseudo_hnf_modulus(P::PMat{T, S}) where {T, S}
  K = parent(P.matrix[1, 1])
  O = order(P.coeffs[1])
  if nrows(P) == ncols(P)
    m = det(P)
  else
    p = next_prime(2^61)
    permGroup = PermGroup(nrows(P))
    rowPerm = permGroup()
    rank = 0
    while rank != ncols(P)
      lp = prime_decomposition(O, p)
      for t in lp
        F, mF = ResidueField(O, t[1])
        mFF = extend(mF, K)
        Pt = zero_matrix(codomain(mFF), nrows(P), ncols(P))
        nextIdeal = false
        for i = 1:nrows(P)
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
        rowPerm = permGroup()
        rank = lu!(rowPerm, Pt)
      end
      p = next_prime(p)
    end
    Minor = zero_matrix(K, ncols(P), ncols(P))
    C = Array{S, 1}(undef, rank)
    for i = 1:nrows(P)
      if rowPerm[i] > rank
        continue
      end
      for j = 1:ncols(P)
        Minor[rowPerm[i], j] = P.matrix[i, j]
      end
      C[rowPerm[i]] = P.coeffs[i]
    end
    PMinor = PseudoMatrix(Minor, C)
    m = det(PMinor)
  end
  simplify(m)
  return numerator(m)
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

  for i in 1:nrows(P)
    mul_row!(P.matrix, i, K(z))
  end

  return z
end

function pseudo_hnf_mod(P::PMat, m::NfOrdIdl, shape::Symbol = :upperright, strategy = :split)
  O = order(m)

  t_comp_red = 0.0
  t_mod_comp = 0.0
  t_sum = 0.0
  t_div = 0.0
  t_idem = 0.0

  t_comp_red += @elapsed z = _matrix_for_reduced_span(P, m)
  t_mod_comp += @elapsed zz = strong_echelon_form(z, shape, strategy)

  res_mat = zero_matrix(nf(O), nrows(P), ncols(P))
  for i in 1:nrows(P)
    for j in 1:ncols(P)
      res_mat[i, j] = elem_in_nf(zz[i, j].elem)
    end
  end

  res = PMat{nf_elem, NfOrdFracIdl}(res_mat, [ deepcopy(x)::NfOrdFracIdl for x in P.coeffs])

  shift = 0
  if shape == :lowerleft
    shift = nrows(P) - ncols(P)
  end

  for i in 1:ncols(P)
    if iszero(zz[i + shift, i].elem)
      res.matrix[i + shift, i] = one(nf(O))
      res.coeffs[i + shift] = NfOrdFracIdl(deepcopy(m), fmpz(1))
    else
      o = ideal(O, zz[i + shift, i].elem)
      t_sum += @elapsed g = o + m
      t_div += @elapsed oo = divexact(o, g)
      t_div += @elapsed mm = divexact(m, g)
      t_idem += @elapsed e, f = idempotents(oo, mm)
      res.coeffs[i + shift] = NfOrdFracIdl(deepcopy(g), fmpz(1))
      mul_row!(res.matrix, i + shift, elem_in_nf(e))
      divide_row!(res.matrix, i + shift, elem_in_nf(zz[i + shift, i].elem))
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

  #println("computation of reduction : $t_comp_red")
  #println("modular computation      : $t_mod_comp")
  #println("computation of ideal sum : $t_sum")
  #println("computation of ideal div : $t_div")
  #println("computation of idems     : $t_idem")

  return res
end

#this is Algorithm 4 of FH2014
# we assume that span(P) \subseteq O^r
function _matrix_for_reduced_span(P::PMat, m::NfOrdIdl)
  O = order(m)
  c = Array{NfOrdIdl}(undef, nrows(P))
  mat = deepcopy(P.matrix)
  for i in 1:nrows(P)
    I, a = _coprime_norm_integral_ideal_class(P.coeffs[i], m)
    divide_row!(mat, i, a)
    c[i] = I
  end
  Om, OtoOm = quo(O, m)
  z = zero_matrix(Om, nrows(P), ncols(P))
  for i in 1:nrows(z)
    for j in 1:ncols(z)
      @assert norm(c[i])*mat[i, j] in O
      # TH TODO:
      # The following assertion will fail in case Om is the zero ring.
      # (This happens if m is the whole ring).
      # But if m is the whole ring, we actually don't have to do
      # anything.
      if isone(norm(m))
        z[i, j] = zero(Om)
      else
        @assert euclid(OtoOm(O(norm(c[i])))) == 1
        q = OtoOm(O(norm(c[i])*mat[i,j]))
        qq = inv(OtoOm(O(norm(c[i]))))
        z[i, j] = q*qq
      end
    end
  end
  return z
end

(::NfOrdQuoRing)(a::NfOrdQuoRingElem) = a

_check(a) = a.has_coord ? dot(a.elem_in_basis, basis(parent(a))) == a : true

function _check(m::Generic.Mat{NfOrdElem})
  for i in 1:nrows(m)
    for j in 1:ncols(m)
      if !_check(m[i, j].elem)
        println("$i $j not consistent: $(m[i, j]) : $(m[i, j].elem_in_basis)")
        error("dasdsad")
      end
    end
  end
end

function _check(m::Generic.Mat{NfOrdQuoRingElem})
  for i in 1:nrows(m)
    for j in 1:ncols(m)
      if !_check(m[i, j].elem)
        println("$i $j not consistent: $(m[i, j].elem) : $(m[i, j].elem.elem_in_basis)")
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
    M[i, j] = M[i, j] * r
  end
  return nothing
end

function mul_col!(M::Generic.Mat{T}, i::Int, r::T) where T
  for j in 1:nrows(M)
    M[j, i] = M[j, i]*r
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
    if !(w[1, i]//P.matrix[i, i] in P.coeffs[i])
      return false
    end
    e = w[1, i]//P.matrix[i, i]
    if shape == :upperright
      for j = i:ncols(P)
        w[1, j] = w[1, j] - e*P.matrix[i, j]
      end
    elseif shape == :lowerleft
      for j = 1:i
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
    if !(w[1, i]//P.matrix[i, i] in P.coeffs[i]*inv(a))
      return false
    end
    e = w[1, i]//P.matrix[i, i]
    if shape == :upperright
      for j = i:ncols(P)
        w[1, j] = w[1, j] - e*P.matrix[i, j]
      end
    elseif shape == :lowerleft
      for j = 1:i
        w[1, j] = w[1, j] - e*P.matrix[i, j]
      end
    end
  end
  if !iszero(w)
    return false
  end
  return true
end

function _spans_subset_of_pseudohnf(M::PMat{nf_elem, NfOrdFracIdl}, P::PMat{nf_elem, NfOrdFracIdl}, shape::Symbol = :upperright)
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

function sub(M::Generic.Mat, rows::UnitRange{Int}, cols::UnitRange{Int})
  @assert step(rows) == 1 && step(cols) == 1
  z = zero_matrix(base_ring(M), length(rows), length(cols))
  for i in rows
    for j in cols
      z[i - first(rows) + 1, j - first(cols) + 1] = M[i, j]
    end
  end
  return z
end

function sub(P::PMat, rows::UnitRange{Int}, cols::UnitRange{Int})
  m = sub(P.matrix, rows, cols)
  return PseudoMatrix(m, P.coeffs[rows])
end

function in(x::nf_elem, y::NfOrdFracIdl)
  B = inv(basis_mat(y))
  O = order(y)
  M = zero_matrix(FlintZZ, 1, degree(O))
  t = FakeFmpqMat(M)
  elem_to_mat_row!(t.num, 1, t.den, x)
  v = t*basis_mat_inv(O)
  v = v*B

  return v.den == 1
end

pseudo_matrix(x...) = PseudoMatrix(x...)

function pseudo_hnf_cohen(P::PMat)
   return _pseudo_hnf_cohen(P, Val{false})
end

function pseudo_hnf_cohen_with_trafo(P::PMat)
   return _pseudo_hnf_cohen(P, Val{true})
end

function _pseudo_hnf_cohen(P::PMat, trafo::Type{Val{T}} = Val{false}) where T
   H = deepcopy(P)
   m = nrows(H)
   if trafo == Val{true}
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
function pseudo_hnf_cohen!(H::PMat, U::Generic.Mat{T}, with_trafo::Bool = false) where T <: nf_elem
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
         with_trafo ? swap_rows!(U, j, k) : nothing
      end
      H.coeffs[k] = H.coeffs[k]*A[k, i]
      simplify(H.coeffs[k])
      with_trafo ? divide_row!(U, k, A[k, i]) : nothing
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
         if with_trafo
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
         if with_trafo
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

function _in_span(v::Vector{nf_elem}, P::PMat)
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
    H = _pseudo_hnf_kb(PseudoMatrix(_swapcols(P.matrix), P.coeffs), Val{false})
    _swapcols!(H.matrix)
    _swaprows!(H.matrix)
    reverse!(H.coeffs)
    return H
  elseif shape == :upperright
    return _pseudo_hnf_kb(P, Val{false})
  else
    error("Not yet implemented")
  end
end

function pseudo_hnf_kb_with_trafo(P::PMat, shape::Symbol = :upperright)
  if shape == :lowerleft
    H, U = _pseudo_hnf_kb(PseudoMatrix(_swapcols(P.matrix), P.coeffs), Val{true})
    _swapcols!(H.matrix)
    _swaprows!(H.matrix)
    reverse!(H.coeffs)
    _swaprows!(U)
    return H, U
  elseif shape == :upperright
    return _pseudo_hnf_kb(P, Val{true})
  else
    error("Not yet implemented")
  end
end

function _pseudo_hnf_kb(P::PMat, trafo::Type{Val{T}} = Val{false}) where T
   H = deepcopy(P)
   m = nrows(H)
   if trafo == Val{true}
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

function kb_reduce_row!(H::PMat{T, S}, U::Generic.Mat{T}, pivot::Array{Int, 1}, c::Int, with_trafo::Bool) where {T <: Union{nf_elem, RelativeElement}, S}
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
      if with_trafo
         for j = 1:ncols(U)
            mul!(t, q, U[p,j])
            addeq!(U[r,j], t)
         end
      end
   end
   return nothing
end

function kb_reduce_column!(H::PMat{T, S}, U::Generic.Mat{T}, pivot::Array{Int, 1}, c::Int, with_trafo::Bool, start_element::Int = 1) where {T <: Union{nf_elem, RelativeElement}, S}
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
      if with_trafo
         for j = 1:ncols(U)
            mul!(t, q, U[r,j])
            addeq!(U[p,j], t)
         end
      end
   end
   return nothing
end

function kb_sort_rows!(H::PMat{T, S}, U::Generic.Mat{T}, pivot::Array{Int, 1}, with_trafo::Bool, start_element::Int = 1) where {T <: Union{nf_elem, RelativeElement}, S}
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
         with_trafo ? swap_rows!(U, r1, r2) : nothing
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

const PRINT_PSEUDOHNF_SIZE = Ref{Bool}(false)

function pseudo_hnf_kb!(H::PMat{T, S}, U::Generic.Mat{T}, with_trafo::Bool = false, start_element::Int = 1) where {T <: Union{nf_elem, RelativeElement}, S}
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
   H.coeffs[row1] = H.coeffs[row1]*A[row1, col1]
   simplify(H.coeffs[row1])
   with_trafo ? divide_row!(U, row1, A[row1, col1]) : nothing
   divide_row!(A, row1, A[row1, col1])
   t = K()
   t1 = K()
   t2 = K()
   for i=row1:m-1
      if Hecke.PRINT_PSEUDOHNF_SIZE[]
        println(" Extending to $(i + 1) x $(i + 1)")
         Hecke.size(H)
      end
      new_pivot = false
      for j = start_element:pivot_max
         if iszero(A[i+1,j])
            continue
         end
         if pivot[j] == 0
            pivot[j] = i+1
            pivot_max = max(pivot_max, j)
            new_pivot = true
            H.coeffs[i+1] = H.coeffs[i+1]*A[i+1, j]
            simplify(H.coeffs[i+1])
            with_trafo ? divide_row!(U, i+1, A[i+1, j]) : nothing
            divide_row!(A, i+1, A[i+1, j])
            kb_reduce_row!(H, U, pivot, j, with_trafo)
         else
            p = pivot[j]
            Aij = deepcopy(A[i+1, j])
            a = H.coeffs[i+1]
            aa = Aij*a
            b = H.coeffs[p]
            d = aa + b
            ad = aa//d
            simplify(ad)
            bd = b//d
            simplify(bd)
            if typeof(ad) == NfOrdFracIdl
              if ad.den != 1 || bd.den != 1
                error("Ideals are not integral.")
              end
              u, v = map(K, idempotents(ad.num, bd.num))
            else
              if !isintegral(ad) || !isintegral(bd)
                error("Ideals are not integral.")
              end
              # numerator(ad) would make a deepcopy...
              adint = NfRelOrdIdl{typeof(ad).parameters...}(order(ad), basis_pmat(ad, Val{false}))
              bdint = NfRelOrdIdl{typeof(bd).parameters...}(order(bd), basis_pmat(bd, Val{false}))
              u, v = map(K, idempotents(adint, bdint))
            end
            u = divexact(u, Aij)
            for c = j:n
               t = deepcopy(A[i+1, c])
               #t1 = mul!(t1, A[p, c], -Aij)
               mul!(t1, A[p, c], -Aij)
               #A[i+1, c] = addeq!(A[i+1, c], t1)
               addeq!(A[i+1, c], t1)
               #t1 = mul!(t1, t, u)
               mul!(t1, t, u)
               #t2 = mul!(t2, A[p, c], v)
               mul!(t2, A[p, c], v)
               #A[p, c] = add!(A[p, c], t1, t2)
               add!(A[p, c], t1, t2)
            end
            if with_trafo
               for c = 1:m
                  t = deepcopy(U[i+1, c])
                  #t1 = mul!(t1, U[p, c], -Aij)
                  mul!(t1, U[p, c], -Aij)
                  #U[i+1, c] = addeq!(U[i+1, c], t1)
                  addeq!(U[i+1, c], t1)
                  #t1 = mul!(t1, t, u)
                  mul!(t1, t, u)
                  #t2 = mul!(t2, U[p, c], v)
                  mul!(t2, U[p, c], v)
                  #U[p, c] = add!(U[p, c], t1, t2)
                  add!(U[p, c], t1, t2)
               end
            end
            H.coeffs[i+1] = a*b//d
            simplify(H.coeffs[i+1])
            H.coeffs[p] = d
            simplify(H.coeffs[p])
         end
         kb_reduce_column!(H, U, pivot, j, with_trafo, start_element)
         if new_pivot
            break
         end
      end
      if !new_pivot
         for c = pivot_max+1:n
            if !iszero(A[i+1,c])
               pivot[c] = i+1
               pivot_max = max(pivot_max, c)
               H.coeffs[i+1] = H.coeffs[i+1]*A[i+1, c]
               simplify(H.coeffs[i+1])
               with_trafo ? divide_row!(U, i+1, A[i+1, c]) : nothing
               divide_row!(A, i+1, A[i+1, c])
               kb_reduce_column!(H, U, pivot, c, with_trafo, start_element)
               break
            end
         end
      end
   end
   kb_sort_rows!(H, U, pivot, with_trafo, start_element)
   return nothing
end

mutable struct PMat2
   parent
   matrix::Generic.Mat{nf_elem}
   row_coeffs::Array{NfOrdFracIdl, 1}
   col_coeffs::Array{NfOrdFracIdl, 1}

   function PMat2(m::Generic.Mat{nf_elem}, r::Array{NfOrdFracIdl, 1}, c::Array{NfOrdFracIdl, 1})
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

function PseudoMatrix2(m::Generic.Mat{nf_elem}, r::Array{NfOrdFracIdl, 1}, c::Array{NfOrdFracIdl, 1})
   ( nrows(m) != length(r) || ncols(m) != length(c) ) && error("Dimensions do not match.")
   return PMat2(m, r, c)
end


function PseudoMatrix2(m::Generic.Mat{NfOrdElem}, r::Array{NfOrdFracIdl, 1}, c::Array{NfOrdIdl, 1})
   mm = change_ring(m, nf(base_ring(m)))
   rr = map(z -> NfOrdFracIdl(z, fmpz(1)), r)
   cc = map(z -> NfOrdFracIdl(z, fmpz(1)), c)
   return PMat(mm, rr, cc)
end

function nrows(m::PMat2)
   return nrows(m.matrix)
end

function ncols(m::PMat2)
   return ncols(m.matrix)
end

function pseudo_snf_kb(P::PMat2)
   return _pseudo_snf_kb(P, Val{false})
end

function pseudo_snf_kb_with_trafo(P::PMat2)
   return _pseudo_snf_kb(P, Val{true})
end

function _pseudo_snf_kb(P::PMat2, trafo::Type{Val{T}} = Val{false}) where T
   S = deepcopy(P)
   m = nrows(S)
   n = ncols(S)
   if trafo == Val{true}
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

function kb_clear_row!(S::PMat2, K::Generic.Mat{nf_elem}, i::Int, with_trafo::Bool)
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
      if with_trafo
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

function pseudo_snf_kb!(S::PMat2, U::Generic.Mat{nf_elem}, K::Generic.Mat{nf_elem}, with_trafo::Bool = false)
   m = nrows(S)
   n = ncols(S)
   A = S.matrix
   l = min(m,n)
   i = 1
   t = base_ring(A)()
   t1 = base_ring(A)()
   t2 = base_ring(A)()
   H = PseudoMatrix(A, S.row_coeffs)
   if !iszero(A[1, 1])
      S.row_coeffs[1] = S.row_coeffs[1]*A[1, 1]
      simplify(S.row_coeffs[1])
      with_trafo ? divide_row!(U, 1, A[1, 1]) : nothing
      divide_row!(A, 1, A[1, 1])
   end
   while i<=l
      !iszero(A[i, i]) ? kb_clear_row!(S, K, i, with_trafo) : nothing
      pseudo_hnf_kb!(H, U, with_trafo, i)
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
   base_ring::NfOrd
   is_triu::Bool
   function ModDed(P::PMat, is_triu::Bool = false; check::Bool = true)
      if check
         is_triu = istriu(P.matrix)
      end
      z = new()
      z.pmatrix = P
      z.base_ring = order(P.coeffs[1])
      z.is_triu = is_triu
      return z
   end
end

base_ring(M::ModDed) = M.base_ring

function istriu(A::Generic.Mat)
   m = nrows(A)
   n = ncols(A)
   d = 0
   for r = 1:m
      for c = 1:n
         if !iszero(A[r, c])
            if c <= d
               return false
            end
            d = c
            break
         end
      end
   end
   return true
end

function show(io::IO, M::ModDed)
   print(io, "Module over $(M.base_ring) with defining pseudo-matrix")
   for i in 1:nrows(M.pmatrix.matrix)
      print(io, "\n")
      show(IOContext(io, :compact => true), M.pmatrix.coeffs[i])
      print(io, " with row $(sub(M.pmatrix.matrix, i:i, 1:ncols(M.pmatrix.matrix)))")
   end
end

ModDed(m::Generic.Mat{nf_elem}, is_triu::Bool = false; check::Bool = true) = ModDed(PseudoMatrix(m), is_triu; check = check)

ModDed(m::Generic.Mat{NfOrdElem}, is_triu::Bool = false; check::Bool = true) = ModDed(PseudoMatrix(m), is_triu; check = check)

ModDed(c::Array{NfOrdFracIdl, 1}) = ModDed(PseudoMatrix(c), true; check = false)

ModDed(c::Array{NfOrdIdl, 1}) = ModDed(PseudoMatrix(c), true; check = false)

function in(v::Vector{nf_elem}, M::ModDed)
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
      if !iszero_row(P.matrix, i)
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

function Base.vcat(P::PMat, Q::PMat)
   @assert base_ring(P.matrix) == base_ring(Q.matrix)
   m = vcat(P.matrix, Q.matrix)
   c = vcat(P.coeffs, Q.coeffs)
   return PseudoMatrix(m, c)
end

function Base.hcat(P::PMat, Q::PMat)
   @assert base_ring(P.matrix) == base_ring(Q.matrix)
   @assert P.coeffs == Q.coeffs
   m = hcat(P.matrix, Q.matrix)
   return PseudoMatrix(m, P.coeffs)
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
   C2 = hcat(B, PseudoMatrix(m, B.coeffs))
   C = vcat(C1, C2)
   # C = [A A; B 0]
   pseudo_hnf_kb!(C, C.matrix, false)
   for i = 1:nrows(B)
      for j = 1:ncols(B)
         m[i, j] = C.matrix[i + nrows(A), j + ncols(A)]
      end
   end
   D = PseudoMatrix(m, C.coeffs[nrows(A) + 1:nrows(C)])
   MN = ModDed(D, true; check = false)
   simplify_basis!(MN)
   return MN
end

function mod(M::ModDed, p::NfOrdIdl)
   O = base_ring(M)
   Op = ResidueRing(O, p)
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

function ispseudo_hnf(M, shape::Symbol = :lowerleft)
  return istriangular(M.matrix, shape)
end

function test_triangular()
  M = zero_matrix(FlintZZ, 3, 3)

  M = FlintZZ[1 0 0;
              0 1 0;
              0 0 1]

  @assert istriangular(M)

  M = FlintZZ[0 0 0;
              0 1 0;
              0 0 1]

  @assert istriangular(M)

  M = FlintZZ[1 0 0;
              0 0 0;
              0 0 1]

  @assert !istriangular(M)

  M = FlintZZ[0 1 0;
              0 0 1;
              0 0 0]

  @assert !istriangular(M)

  M = FlintZZ[1 0 0;
              0 1 0;
              0 0 0]

  @assert !istriangular(M)

  M = FlintZZ[0 1 0;
              1 0 0;
              0 0 1]

  @assert !istriangular(M)
end

function istriangular(M::MatElem, shape::Symbol = :lowerleft)
  r = nrows(M)
  c = ncols(M)

  if shape == :lowerleft

    piv = 0

    k = 1
    while iszero_row(M, k) && k <= r
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
    return ispseudo_hnf(transpose(M), :lowerleft)
  end
end
