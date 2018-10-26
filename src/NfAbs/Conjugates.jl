export istotally_real, istotally_complex, conjugates, conjugates_real,
       conjugates_complex, conjugates_log, complex_conjugation

################################################################################
#
#  Totally real/complex predicates
#
################################################################################

@doc Markdown.doc"""
***
    istotally_real(K::AnticNumberField) -> Bool

Returns true if and only if $K$ is totally real, that is, if all roots of the
defining polynomial are real.
"""
function istotally_real(K::AnticNumberField)
  return signature(K)[1] == degree(K)
end

@doc Markdown.doc"""
***
    istotally_complex(K::AnticNumberField) -> Bool

Returns true if and only if $K$ is totally real, that is, if all roots of the
defining polynomial are not real.
"""
function istotally_complex(K::AnticNumberField)
  return signature(K)[1] == 0
end

################################################################################
#
#  Conjugates and real embeddings
#
################################################################################

@doc Markdown.doc"""
***
    conjugates(x::nf_elem, abs_tol::Int) -> Vector{acb}

> Compute the the conjugates of `x` as elements of type `acb`.
> Recall that we order the complex conjugates
> $\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
> $\sigma_{i}(x) = \overline{sigma_{i + s}(x)}$ for $r + 1 \leq i \leq r + s$.
>
> Every entry `y` of the vector returned satisfies
> `radius(real(y)) < 2^-abs_tol` and `radius(imag(y)) < 2^-abs_tol` respectively.
"""
function conjugates(x::nf_elem, abs_tol::Int = 32, T = arb)
  if T === arb
    return conjugates_arb(x, abs_tol)
  else
    error("Cannot return conjugates as type $T")
  end
end

# This is for quick and dirty computations
function __conjugates_arb(x::nf_elem, prec::Int = 32)
  K = parent(x)
  d = degree(K)
  r1, r2 = signature(K)
  conjugates = Array{acb}(undef, r1 + 2*r2)

  c = conjugate_data_arb_roots(K, -1)

  CC = AcbField(prec, false)
  RR = ArbField(prec, false)

  xpoly = arb_poly(parent(K.pol)(x), prec)

  for i in 1:r1
    o = RR()
    ccall((:arb_poly_evaluate, :libarb), Nothing,
          (Ref{arb}, Ref{arb_poly}, Ref{arb}, Int),
           o, xpoly, c.real_roots[i], prec)

    if !isfinite(o)
      error("oops")
    end
    conjugates[i] = CC(o)
  end

  for i in 1:r2
    tacb = CC()
    ccall((:arb_poly_evaluate_acb, :libarb), Nothing,
          (Ref{acb}, Ref{arb_poly}, Ref{acb}, Int),
           tacb, xpoly, c.complex_roots[i], prec)

    if !isfinite(tacb)
      error("oops")
    end

    conjugates[r1 + i] = tacb
    conjugates[r1 + i + r2] = conj(conjugates[r1 + i])
  end

  return conjugates
end

function conjugates_arb(x::nf_elem, abs_tol::Int = 32)
  K = parent(x)
  d = degree(K)
  r1, r2 = signature(K)
  conjugates = Array{acb}(undef, r1 + 2*r2)
  target_tol = abs_tol

  while true
    prec_too_low = false
    c = conjugate_data_arb_roots(K, abs_tol)

    if abs_tol > 2^18
      error("Something wrong in conjugates_arb_log")
    end

    CC = AcbField(abs_tol, false)
    RR = ArbField(abs_tol, false)

    xpoly = arb_poly(parent(K.pol)(x), abs_tol)

    for i in 1:r1
      o = RR()
      ccall((:arb_poly_evaluate, :libarb), Nothing,
            (Ref{arb}, Ref{arb_poly}, Ref{arb}, Int),
             o, xpoly, c.real_roots[i], abs_tol)

      if !isfinite(o) || !radiuslttwopower(o, -target_tol)
        abs_tol = 2*abs_tol
        prec_too_low = true
        break
      end
      conjugates[i] = CC(o)
    end

    if prec_too_low
      continue
    end

    for i in 1:r2
      tacb = CC()
      ccall((:arb_poly_evaluate_acb, :libarb), Nothing,
            (Ref{acb}, Ref{arb_poly}, Ref{acb}, Int),
             tacb, xpoly, c.complex_roots[i], abs_tol)

      if !isfinite(tacb) || !radiuslttwopower(tacb, -target_tol)
        abs_tol = 2*abs_tol
        prec_too_low = true
        break
      end

      conjugates[r1 + i] = tacb
      conjugates[r1 + i + r2] = conj(conjugates[r1 + i])
    end

    if prec_too_low
      continue
    end

    for i in 1:d
      expand!(conjugates[i], -target_tol)
    end
    return conjugates
  end
end

@doc Markdown.doc"""
***
    conjugates_arb_real(x::nf_elem, abs_tol::Int) -> Vector{arb}

> Compute the the real conjugates of `x` as elements of type `arb`.
>
> Every entry `y` of the array returned satisfies
> `radius(y) < 2^-abs_tol`.
"""
function conjugates_real(x::nf_elem, abs_tol::Int = 32, T = arb)
  if T === arb
    return conjugates_arb_real(x, abs_tol)
  else
    error("Cannot return real conjugates as type $T")
  end
end

function conjugates_arb_real(x::nf_elem, abs_tol::Int = 32)
  r1, r2 = signature(parent(x))
  c = conjugates_arb(x, abs_tol)
  z = Array{arb}(undef, r1)

  for i in 1:r1
    z[i] = real(c[i])
  end

  return z
end

@doc Markdown.doc"""
***
    conjugates_complex(x::nf_elem, abs_tol::Int) -> Vector{acb}

> Compute the the complex conjugates of `x` as elements of type `acb`.
> Recall that we order the complex conjugates
> $\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
> $\sigma_{i}(x) = \overline{sigma_{i + s}(x)}$ for $r + 1 \leq i \leq r + s$.
>
> Every entry `y` of the array returned satisfies
> `radius(real(y)) < 2^-abs_tol` and `radius(imag(y)) < 2^-abs_tol`.
"""
function conjugates_complex(x::nf_elem, abs_tol::Int = 32, T = arb)
  if T === arb
    return conjugates_arb_complex(x, abs_tol)
  else
    error("Cannot return real conjugates as type $T")
  end
end

function conjugates_arb_complex(x::nf_elem, abs_tol::Int)
  r1, r2 = signature(parent(x))
  c = conjugates_arb(x, abs_tol)
  z = Vector{acb}(undef, r2)

  for i in (r1 + 1):(r1 + r2)
    z[i - r1] = c[i]
  end

  return z
end

################################################################################
#
#  Logarithms of conjugates
#
################################################################################

@doc Markdown.doc"""
***
    conjugates_arb_log(x::nf_elem, abs_tol::Int) -> Array{arb, 1}

> Returns the elements
> $(\log(\lvert \sigma_1(x) \rvert),\dotsc,\log(\lvert\sigma_r(x) \rvert),
> \dotsc,2\log(\lvert \sigma_{r+1}(x) \rvert),\dotsc,
> 2\log(\lvert \sigma_{r+s}(x)\rvert))$ as elements of type `arb` radius
> less then `2^-abs_tol`.
"""
function conjugates_log(x::nf_elem, abs_tol::Int = 32, T = arb)
  if T === arb
    return conjugates_arb_log(x, abs_tol)
  else
    error("Cannot return real conjugates as type $T")
  end
end

function conjugates_arb_log(x::nf_elem, abs_tol::Int)
  K = parent(x)
  c = conjugate_data_arb_roots(K, abs_tol)
  r1 = length(c.real_roots)
  r2 = length(c.complex_roots)
  d = degree(K)
  target_tol = abs_tol

  # TODO: Replace this using multipoint evaluation of libarb
  z = Array{arb}(undef, r1 + r2)
  while true
    prec_too_low = false
    c = conjugate_data_arb_roots(K, abs_tol)
    if abs_tol > 2^18
      error("Something wrong in conjugates_arb_log")
    end
    xpoly = arb_poly(parent(K.pol)(x), abs_tol)
    RR = ArbField(abs_tol, false)
    for i in 1:r1
      o = RR()
      ccall((:arb_poly_evaluate, :libarb), Nothing,
            (Ref{arb}, Ref{arb_poly}, Ref{arb}, Int),
            o, xpoly, c.real_roots[i], abs_tol)
      abs!(o, o)
      log!(o, o)
      z[i] = o

      if !isfinite(z[i]) || !radiuslttwopower(z[i], -target_tol)
        abs_tol = 2*abs_tol
        prec_too_low = true
        break
      end
    end

    if prec_too_low
      continue
    end

    CC = AcbField(abs_tol, false)

    tacb = CC()
    for i in 1:r2
      oo = RR()
      ccall((:arb_poly_evaluate_acb, :libarb), Nothing,
            (Ref{acb}, Ref{arb_poly}, Ref{acb}, Int),
            tacb, xpoly, c.complex_roots[i], abs_tol)
      abs!(oo, tacb)
      log!(oo, oo)
      mul2exp!(oo, oo, 1)
      z[r1 + i] = oo

      if !isfinite(z[r1 + i]) || !radiuslttwopower(z[r1 + i], -target_tol)
        abs_tol = 2*abs_tol
        prec_too_low = true
        break
      end
    end

    if prec_too_low
      continue
    end

    for i in 1:r1 + r2
      zz = deepcopy(z[i])
      expand!(z[i], -target_tol)
    end
    return z
  end
end

function conjugates_arb_log(x::nf_elem, R::ArbField)
  z = conjugates_arb_log(x, R.prec)
  return map(R, z)
end

################################################################################
#
#  Minkowski map
#
################################################################################

@doc Markdown.doc"""
***
    minkowski_map(a::nf_elem, abs_tol::Int) -> Array{arb, 1}

> Returns the image of $a$ under the Minkowski embedding.
> Every entry of the array returned is of type `arb` with radius less then
> `2^(-abs_tol)`.
"""
function minkowski_map(a::nf_elem, abs_tol::Int = 32)
  # TODO: Rewrite this using conjugates_arb
  K = parent(a)
  A = Array{arb}(undef, degree(K))
  r, s = signature(K)
  c = conjugate_data_arb(K)
  R = PolynomialRing(AcbField(c.prec, false), "x", cached=false)[1]
  f = R(parent(K.pol)(a))
  CC = AcbField(c.prec, false)
  T = PolynomialRing(CC, "x", cached=false)[1]
  g = T(f)

  for i in 1:r
    t = evaluate(g, c.real_roots[i])
    @assert isreal(t)
    A[i] = real(t)
    if !radiuslttwopower(A[i], -abs_tol)
      refine(c)
      return minkowski_map(a, abs_tol)
    end
  end

  t = base_ring(g)()

  for i in 1:s
    t = evaluate(g, c.complex_roots[i])
    t = sqrt(CC(2))*t
    if !radiuslttwopower(t, -abs_tol)
      refine(c)
      return minkowski_map(a, abs_tol)
    end
    A[r + 2*i - 1] = real(t)
    A[r + 2*i] = imag(t)
  end

  return A
end

################################################################################
#
#  T_2
#
################################################################################

function t2(x::nf_elem, abs_tol::Int = 32, T = arb)
  if T === arb
    p = 2*abs_tol
    z = mapreduce(y -> y^2, +, minkowski_map(x, p))
    while !radiuslttwopower(z, -abs_tol)
      p = 2 * p
      z = mapreduce(y -> y^2, +, minkowski_map(x, p))
    end
    return z
  else
    error("Not yet implemented")
  end
end

############################################################################
#
#  Signs of real embeddings
#
############################################################################

#@doc Markdown.doc"""
#***
#    _signs(a::nf_elem) -> Array{Int, 1}
#> For a non-zero elements $a$ return the signs of all real embeddings.
#"""
function _signs(a::nf_elem)
  if iszero(a)
    error("element must not be zero")
  end

  p = 16
  r1, r2 = signature(parent(a))

  if r1 == 0
    return Int[]
  end

  s = Array{Int}(undef, r1)
  while true
    c = conjugates(a, p)
    done = true
    for i=1:r1
      if contains(reim(c[i])[1], 0)
        p *= 2
        done = false
        break
      end
      s[i] = ispositive(real(c[i])) ? 1 : -1
    end
    if done
      return s
    end
  end
end

#@doc Markdown.doc"""
#***
#    signs(a::FacElem{nf_elem, AnticNumberField}) -> Array{Int, 1}
#> For a non-zero elements $a$ in factored form,
#> return the signs of all real embeddings.
#"""
function _signs(a::FacElem{nf_elem, AnticNumberField})
  r1, r2 = signature(base_ring(a))
  if r1 == 0
    return Int[]
  end

  s = ones(Int, r1)

  for (k, e) = a.fac
    if iseven(e)
      continue
    end
    s .*= _signs(k)
  end
  return s
end

@doc Markdown.doc"""
    complex_conjugation(K::AnticNumberField)

Given a totally complex normal number field, this function returns the
automorphism which is the restrition of complex conjugation.
"""
function complex_conjugation(K::AnticNumberField)
  A = automorphisms(K)
  if length(A) < degree(K)
    error("Number field must be normal")
  end
  a = gen(K)
  d = degree(K)
  !istotally_complex(K) && error("Number field must be totally complex")
  imgs = Vector{nf_elem}(undef, d)

  for i in 1:d
    imgs[i] = A[i](a)
  end

  p = 32 

  while true
    c = conjugates(a, p)
    cc = Vector{acb}[ conj.(conjugates(imgs[i], p)) for i in 1:d ]
    for i in 1:d
      if !overlaps(c[d], cc[i][d])
        continue
      end
      found = true
      for j in 1:d
        if j == i
          continue
        end
        if overlaps(c[d], cc[j][d])
          found = false
          break
        end
      end
      if !found
        continue
      else
        return A[i]
      end
    end
    p = 2 * p
    if p > 2^18
      error("Precision too high in complex_conjugation")
    end
  end
end
