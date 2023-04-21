################################################################################
#
#  Valuation
#
################################################################################


function valuation(a::UInt, b::UInt)
  return ccall((:n_remove, libflint), Int, (Ref{UInt}, UInt), a, b)
end

# CF:
# The idea is that valuations are mostly small, eg. in the class group
# algorithm. So this version computes the completion and the embedding into it
# at small precision and can thus compute (small) valuation at the effective
# cost of an mod(zzModPolyRingElem, zzModPolyRingElem) operation.
# Isn't it nice?
function val_func_no_index_small(p::NfOrdIdl)
  P = p.gen_one
  @assert P <= typemax(UInt)
  K = nf(order(p))
  Rx = polynomial_ring(GF(UInt(P), cached=false), cached=false)[1]
  Zx = polynomial_ring(FlintZZ, cached = false)[1]
  gR = Rx(p.gen_two.elem_in_nf)
  f = Rx(K.pol)
  gR = gcd!(gR, gR, f)
  g = lift(Zx, gR)
  k = flog(ZZRingElem(typemax(UInt)), P)
  g = hensel_lift(Zx(K.pol), g, P, k)
  Sx = polynomial_ring(residue_ring(FlintZZ, UInt(P)^k, cached=false), cached=false)[1]
  g = Sx(g)
  h = Sx()
  uP = UInt(P)
  local vfunc
  let h = h, g = g, P = P, uP = uP
    function vfunc(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
      d = denominator(x)
      nf_elem_to_nmod_poly!(h, x, false) # ignores the denominator
      h = rem!(h, h, g)
      c = Nemo.coeff_raw(h, 0)
      v = c==0 ? typemax(Int) : valuation(c, uP)
      for i=1:degree(h)
        c = Nemo.coeff_raw(h, i)
        v = min(v, c==0 ? typemax(Int) : valuation(c, uP))
      end
      return v-valuation(d, P)::Int
    end
  end
  return vfunc
end

function val_func_no_index(p::NfOrdIdl)
  P = p.gen_one
  K = nf(order(p))
  Rx, g = polynomial_ring(GF(P, cached=false), cached=false)
  Zx = polynomial_ring(FlintZZ, cached = false)[1]
  nf_elem_to_gfp_fmpz_poly!(g, p.gen_two.elem_in_nf, false)
  f = Rx(K.pol)
  g = gcd(g, f)
  g = lift(Zx, g)
  g = hensel_lift(Zx(K.pol), g, P, 10)
  Sx = polynomial_ring(residue_ring(FlintZZ, P^5, cached=false), cached=false)[1]
  g = Sx(g)
  h = Sx()
  c = ZZRingElem()
  local vfunc
  let h = h, g = g, P = P
    function vfunc(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
      d = denominator(x)
      nf_elem_to_fmpz_mod_poly!(h, x, false) # ignores the denominator
      h = rem!(h, h, g)
      _coeff_as_fmpz!(c, h, 0)
      v = iszero(c) ? 100 : valuation(c, P)
      for i=1:degree(h)
        _coeff_as_fmpz!(c, h, i)
        v = min(v, iszero(c) ? 100 : valuation(c, P))
      end
      return v-valuation(d, P)::Int
    end
  end
  return vfunc
end

function _coeff_as_fmpz!(c::ZZRingElem, f::ZZModPolyRingElem, i::Int)
  ccall((:fmpz_mod_poly_get_coeff_fmpz, libflint), Nothing,
        (Ref{ZZRingElem}, Ref{ZZModPolyRingElem}, Int, Ref{fmpz_mod_ctx_struct}), c, f, i, f.parent.base_ring.ninv)
  return nothing
end


function val_func_index(p::NfOrdIdl)
  # We are in the index divisor case. In larger examples, a lot of
  # time is spent computing denominators of order elements.
  # By using the representation matrix to multiply, we can stay in the order
  # and still be fast (faster even than in field).
  O = order(p)
  pi = inv(p)
  P = p.gen_one
  pi_2 = mod(pi.num.gen_two.elem_in_nf, P^2)
  M = representation_matrix(O(pi_2, false))


  local val
  let P = P, O = O, M = M, p = p
    function val(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
      v = 0
      d, x_mat = integral_split(x, O)
      Nemo.mul!(x_mat, x_mat, M)
      c = content(x_mat)
      vc = valuation(c, P)
      while vc > 0  # should divide and test in place
        #Carlo : How? Not clear how to improve this code.
	      divexact!(x_mat, x_mat, c)
        mul!(x_mat, x_mat, M)
        v += 1 + (vc-1)*p.splitting_type[1]
        c = content(x_mat)
        vc = valuation(c, P)
      end
      return v-Int(valuation(d, P))*p.splitting_type[1]
    end
  end
  return val
end

# CF:
# Classical algorithm of Cohen, but take a valuation element with smaller (?)
# coefficients. Core idea is that the valuation element is, originally, den*gen_two(p)^-1
# where gen_two(p) is "small". Actually, we don't care about gen_two, we
# need gen_two^-1 to be small, hence this version.
function val_fun_generic_small(p::NfOrdIdl)
  P = p.gen_one
  K = nf(order(p))
  O = order(p)
  e = anti_uniformizer(p)
  local val
  let e = e, P = P, p = p, O = O
    function val(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
      nn = ZZRingElem(0)
      v = 0
      p_mod = ZZRingElem(0)
      d = denominator(x, O)
      x *= d
      if !iszero(no)
        nn = numerator(no*(d^degree(O)))
        vp = min(valuation(nn, norm(p)), 10)
        p_mod = P^(div(vp, ramification_index(p))+1)
      else
        p_mod = P^(div(10, ramification_index(p))+1)
      end
      x = mod(x, p_mod)
      mul!(x, x, e)
      while x in O && v < 10
        v += 1
        if !iszero(no)
          nn = divexact(nn, norm(p))
          if !divisible(nn, norm(p))
            break
          end
        end
        x = mod(x, p_mod)
        mul!(x, x, e)
      end
      if v == 10
        return 100
      end
      return v-valuation(d, P)*p.splitting_type[1]
    end
  end
  return val
end

function val_func_generic(p::NfOrdIdl)
  @hassert :NfOrd 1 is_prime(p)
  P = p.gen_one
  K = nf(order(p))
  O = order(p)
  e = anti_uniformizer(p)
  local val
  let e = e, P = P, p = p, O = O
    function val(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
      nn = ZZRingElem(0)
      v = 0
      p_mod = ZZRingElem(0)
      d = denominator(x, O)
      if !iszero(no)
        nn = numerator(no*(d^degree(O)))
        p_mod = P^(div(valuation(nn, norm(p)), ramification_index(p))+1)
	      x = mod(x, p_mod)
      end
      x *= d
      x = x*e
      while x in O
        v += 1
        if !iszero(no)
          nn = divexact(nn, norm(p))
          if !divisible(nn, norm(p))
            break
          end
          x = mod(x, p_mod)
        end
        mul!(x, x, e)
      end
      return v-valuation(d, P)*p.splitting_type[1]
    end
  end
  return val
end

function valuation_with_anti_uni(a::nf_elem, anti_uni::nf_elem, I::NfOrdIdl)
  O = order(I)
  b = a*anti_uni
  if !(b in O)
    return 0
  end
  v = 1
  mul!(b, b, anti_uni)
  while b in O
    v += 1
    mul!(b, b, anti_uni)
  end
  return v
end

function _isindex_divisor(O::NfOrd, P::NfOrdIdl)
  @assert is_prime_known(P) && is_prime(P)
  if !isone(denominator(P.gen_two.elem_in_nf))
    return true
  end
  R = GF(Int(minimum(P)), cached = false)
  Rt, t = polynomial_ring(R, "x", cached = false)
  f = Rt(nf(P).pol)
  g = Rt(P.gen_two.elem_in_nf)
  d = gcd(f, g)
  if !divides(f, d^2)[1] && is_irreducible(d)
    return false
  else
    return true
  end
end

#Function that chooses the valuation depending on the properties of the ideal
function assure_valuation_function(p::NfOrdIdl)
  if isdefined(p, :valuation)
    return nothing
  end
  O = order(p)
  K = nf(O)
  # for generic ideals
  if p.splitting_type[2] == 0
    assure_2_normal(p)
    anti_uni = anti_uniformizer(p)
    local val2
    let O = O, p = p, anti_uni = anti_uni, K = K
      function val2(s::nf_elem, no::QQFieldElem = QQFieldElem(0))
        d = denominator(s, O)
        x = d*s
        if gcd(d, minimum(p, copy = false)) == 1
          return valuation_with_anti_uni(x, anti_uni, p)::Int
        else
          return valuation_with_anti_uni(x, anti_uni, p)::Int - valuation_with_anti_uni(K(d), anti_uni, p)::Int
        end
      end
    end
    p.valuation = val2
    return nothing
  end
  P = minimum(p)
  if degree(O) < 40 && p.splitting_type[1]*p.splitting_type[2] == degree(O)
    local val3
    let P = P, p = p
      function val3(s::nf_elem, no::QQFieldElem = QQFieldElem(0))
        return divexact(valuation(iszero(no) ? norm(s) : no, P)[1], p.splitting_type[2])::Int
      end
    end
    p.valuation = val3
  elseif mod(index(O), P) != 0 && ramification_index(p) == 1
    if fits(UInt, P^2)
      f1 = val_func_no_index_small(p)
      f2 = val_func_generic(p)
      local val1
      let f1 = f1, f2 = f2
        function val1(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
          v = f1(x, no)
          if v > 100  # can happen ONLY if the precision in the .._small function
                      # was too small.
            return f2(x, no)::Int
          else
            return v::Int
          end
        end
      end
      p.valuation = val1
    else
      f8 = val_func_no_index(p)
      f9 = val_func_generic(p)
      local val1
      let f8 = f8, f9 = f9
        function val_large_non_index(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
          v = f8(x, no)
          if v > 10  # can happen ONLY if the precision in the .._small function
                      # was too small.
            return f9(x, no)::Int
          else
            return v::Int
          end
        end
      end
      p.valuation = val_func_generic(p)
    end
  elseif ramification_index(p) == 1 && fits(UInt, P^2) && !_isindex_divisor(O, p)
    f3 = val_func_no_index_small(p)
    if degree(O) > 80
      f5 = val_func_generic(p)
      local val5
      let f3 = f3, f5 = f5
        function val5(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
          v = f3(x, no)
          if v > 100  # can happen ONLY if the precision in the .._small function
                      # was too small.
            return f5(x, no)::Int
          else
            return v::Int
          end
        end
      end
      p.valuation = val5
    else
      f4 = val_func_index(p)
      local val4
      let f3 = f3, f4 = f4
        function val4(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
          v = f3(x, no)
          if v > 100  # can happen ONLY if the precision in the .._small function
                      # was too small.
            return f4(x, no)::Int
          else
            return v::Int
          end
        end
      end
      p.valuation = val4
    end
  elseif degree(O) > 80
    f6 = val_func_generic(p)
    f7 = val_fun_generic_small(p)
    local val_gen
    let f7 = f7, f6 = f6
      function val_gen(x::nf_elem, no::QQFieldElem = QQFieldElem(0))
        vv = f7(x, no)
        if vv == 100
          return f6(x, no)
        else
          return vv
        end
      end
    end
    p.valuation = val_gen
  else
    p.valuation = val_func_index(p)
  end
  return nothing
end


function valuation(a::NfAbsNSElem, p::NfAbsOrdIdl, n::QQFieldElem = QQFieldElem(0))
  return valuation_naive(a, p)
end

function valuation(a::nf_elem, p::NfOrdIdl, no::QQFieldElem = QQFieldElem(0))
  if is_zero(a)
    error("element is zero")
  end
  if parent(a) !== nf(order(p))
    error("Incompatible parents")
  end
  if !is_defining_polynomial_nice(parent(a)) || order(p).is_maximal != 1
    return valuation_naive(a, p)::Int
  end
  @hassert :NfOrd 0 !iszero(a)
  assure_valuation_function(p)
  if p.is_prime != 1
    return Int(p.valuation(a, no))::Int
  end
  #First, check the content of a as a polynomial.
  #We remove the numerator of the content, as the
  #valuation for integers is much easier.
  O = order(p)
  K = nf(O)
  Zx = polynomial_ring(FlintZZ, "x")[1]
  pol_a = Zx(denominator(a)*a)
  c = content(pol_a)
  valnum = Int(valuation(c, p))
  b = divexact(a, c)

  nno = no
  if !iszero(nno)
    nno = divexact(nno, c^degree(K))
  end
  res = Int(p.valuation(b, nno))::Int
  res += valnum
  return res
end

@doc raw"""
    valuation(a::nf_elem, p::NfOrdIdl) -> ZZRingElem
    valuation(a::NfOrdElem, p::NfOrdIdl) -> ZZRingElem
    valuation(a::ZZRingElem, p::NfOrdIdl) -> ZZRingElem

Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
such that $a$ is contained in $\mathfrak p^i$.
"""
valuation(a::NfOrdElem, p::NfOrdIdl) = valuation(a.elem_in_nf, p)

@doc raw"""
    valuation(a::nf_elem, p::NfOrdIdl) -> ZZRingElem
    valuation(a::NfOrdElem, p::NfOrdIdl) -> ZZRingElem
    valuation(a::ZZRingElem, p::NfOrdIdl) -> ZZRingElem

Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
such that $a$ is contained in $\mathfrak p^i$.
"""
function valuation(a::ZZRingElem, p::NfAbsOrdIdl)
  if p.splitting_type[1] == 0
    return valuation_naive(order(p)(a), p)
  end
  P = minimum(p, copy = false)
  return valuation(a, P)* p.splitting_type[1]
end
@doc raw"""
    valuation(a::Integer, p::NfOrdIdl) -> ZZRingElem
Computes the $\mathfrak p$-adic valuation of $a$, that is, the largest $i$
such that $a$ is contained in $\mathfrak p^i$.
"""
valuation(a::Integer, p::NfAbsOrdIdl) = valuation(ZZRingElem(a), p)

#TODO: some more intelligence here...
function valuation_naive(A::NfAbsOrdIdl, B::NfAbsOrdIdl)
  @assert !isone(B)
  Bi = inv(B)
  i = 0
  C = simplify(A* Bi)
  while denominator(C) == 1
    C = simplify(Bi*C)
    i += 1
  end
  return i
end

#TODO: some more intelligence here...
#      in non-maximal orders, interesting ideals cannot be inverted
#      maybe this needs to be checked...
function valuation_naive(x::NfAbsOrdElem, B::NfAbsOrdIdl)
  @assert !isone(B)
  i = 0
  C = B
  while x in C
    i += 1
    C *= B
  end
  return i
end

function valuation_naive(x::T, B::NfAbsOrdIdl) where T <: Union{nf_elem, NfAbsNSElem}
  @assert !isone(B)
  i = 0
  C = B
  O = order(B)
  d = denominator(x, O)
  return valuation_naive(O(x*d), B) - valuation_naive(O(d), B)
end

@doc raw"""
    valuation(A::NfOrdIdl, p::NfOrdIdl) -> ZZRingElem

Computes the $\mathfrak p$-adic valuation of $A$, that is, the largest $i$
such that $A$ is contained in $\mathfrak p^i$.
"""
function valuation(A::NfAbsOrdIdl, p::NfAbsOrdIdl)
  if has_minimum(A) && has_minimum(p) && !divisible(minimum(A, copy = false), minimum(p, copy = false))
    return 0
  end
  if has_princ_gen_special(A)
    gen = princ_gen_special(A)
    return valuation(gen, p)
  end
  if A.is_principal == 1 && isdefined(A, :princ_gen)
    return valuation(A.princ_gen.elem_in_nf, p, QQFieldElem(norm(A)))
  end
  _assure_weakly_normal_presentation(A)
  if !isdefined(p, :splitting_type) || p.splitting_type[1] == 0 #ie. if p is non-prime...
    return valuation_naive(A, p)
  end
  if iszero(A.gen_two)
    return valuation(A.gen_one, p)
  end
  v1 = valuation(A.gen_one, p)
  return min(v1, valuation(A.gen_two.elem_in_nf, p, QQFieldElem(norm(A))))
end
