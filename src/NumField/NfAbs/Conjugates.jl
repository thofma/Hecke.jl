################################################################################
#
#  Totally real/complex predicates
#
################################################################################

@doc raw"""
    is_totally_real(K::NumField) -> Bool

Return `true` if and only if $K$ is totally real, that is, if all roots of the
defining polynomial are real.
"""
function is_totally_real(K::NumField)
  return iszero(signature(K)[2])
end

is_totally_real(::QQField) = true

@doc raw"""
    is_totally_complex(K::NumField) -> Bool

Return `true` if and only if $K$ is totally complex, that is, if all roots of the
defining polynomial are not real.
"""
function is_totally_complex(K::NumField)
  return iszero(signature(K)[1])
end

is_totally_complex(::QQField) = false

################################################################################
#
#  Conjugates and real embeddings
#
################################################################################

@doc raw"""
    conjugates(x::AbsSimpleNumFieldElem, abs_tol::Int) -> Vector{AcbFieldElem}

Compute the conjugates of $x$ as elements of type `AcbFieldElem`.
Recall that we order the complex conjugates
$\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
$\sigma_{i}(x) = \overline{\sigma_{i + s}(x)}$ for $r + 1 \leq i \leq r + s$.

Every entry $y$ of the vector returned satisfies
`radius(real(y)) < 2^-abs_tol` and `radius(imag(y)) < 2^-abs_tol` respectively.
"""
function conjugates(x::NumFieldElem, abs_tol::Int = 32, T = ArbFieldElem)
  if T === ArbFieldElem
    return conjugates_arb(x, abs_tol)
  else
    error("Cannot return conjugates as type $T")
  end
end

@doc raw"""
    conjugates(x::AbsSimpleNumFieldElem, C::AcbField) -> Vector{AcbFieldElem}

Compute the conjugates of $x$ as elements of type `AcbFieldElem`.
Recall that we order the complex conjugates
$\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
$\sigma_{i}(x) = \overline{\sigma_{i + s}(x)}$ for $r + 1 \leq i \leq r + s$.

Let `p` be the precision of `C`, then every entry $y$ of the vector returned
satisfies `radius(real(y)) < 2^-p` and `radius(imag(y)) < 2^-p`
respectively.
"""
function conjugates(x::NumFieldElem, C::AcbField)
  return map(C, conjugates_arb(x, precision(C)))
end

function conjugates(x::QQFieldElem, abs_tol::Int = 32)
  return [ComplexField(abs_tol)(x)]
end

# This is for quick and dirty computations
function __conjugates_arb(x::AbsSimpleNumFieldElem, prec::Int = 32)
  K = parent(x)
  d = degree(K)
  r1, r2 = signature(K)
  conjugates = Array{AcbFieldElem}(undef, r1 + 2*r2)

  c = conjugate_data_arb_roots(K, -1)

  CC = AcbField(prec, cached = false)
  RR = ArbField(prec, cached = false)

  xpoly = ArbPolyRingElem(parent(K.pol)(x), prec)

  for i in 1:r1
    o = RR()
    ccall((:arb_poly_evaluate, libarb), Nothing,
          (Ref{ArbFieldElem}, Ref{ArbPolyRingElem}, Ref{ArbFieldElem}, Int),
           o, xpoly, c.real_roots[i], prec)

    if !isfinite(o)
      error("oops")
    end
    conjugates[i] = CC(o)
  end

  for i in 1:r2
    tacb = CC()
    ccall((:arb_poly_evaluate_acb, libarb), Nothing,
          (Ref{AcbFieldElem}, Ref{ArbPolyRingElem}, Ref{AcbFieldElem}, Int),
           tacb, xpoly, c.complex_roots[i], prec)

    if !isfinite(tacb)
      error("oops")
    end

    conjugates[r1 + i] = tacb
    conjugates[r1 + i + r2] = conj(conjugates[r1 + i])
  end

  return conjugates
end

function conjugates_arb(x::AbsSimpleNumFieldElem, abs_tol::Int = 32)
  K = parent(x)
  d = degree(K)
  r1, r2 = signature(K)
  conjugates = Array{AcbFieldElem}(undef, r1 + 2*r2)
  target_tol = abs_tol
  abs_tol = Int(floor(abs_tol * 1.1))

  while true
    prec_too_low = false
    c = conjugate_data_arb_roots(K, abs_tol)

    if abs_tol < 0
      error("Precision overflow in conjugates_arb_log")
    end

    CC = AcbField(abs_tol, cached = false)
    RR = ArbField(abs_tol, cached = false)

    xpoly = ArbPolyRingElem(parent(K.pol)(x), abs_tol)

    for i in 1:r1
      o = RR()
      ccall((:arb_poly_evaluate, libarb), Nothing,
            (Ref{ArbFieldElem}, Ref{ArbPolyRingElem}, Ref{ArbFieldElem}, Int),
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
      ccall((:arb_poly_evaluate_acb, libarb), Nothing,
            (Ref{AcbFieldElem}, Ref{ArbPolyRingElem}, Ref{AcbFieldElem}, Int),
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

@doc raw"""
    conjugates_arb_real(x::AbsSimpleNumFieldElem, abs_tol::Int) -> Vector{ArbFieldElem}

Compute the real conjugates of $x$ as elements of type `ArbFieldElem`.

Every entry $y$ of the array returned satisfies
`radius(y) < 2^-abs_tol`.
"""
function conjugates_real(x::AbsSimpleNumFieldElem, abs_tol::Int = 32, T = ArbFieldElem)
  if T === ArbFieldElem
    return conjugates_arb_real(x, abs_tol)
  else
    error("Cannot return real conjugates as type $T")
  end
end

function conjugates_arb_real(x::AbsSimpleNumFieldElem, abs_tol::Int = 32)
  r1, r2 = signature(parent(x))
  c = conjugates_arb(x, abs_tol)
  z = Array{ArbFieldElem}(undef, r1)

  for i in 1:r1
    z[i] = real(c[i])
  end

  return z
end

@doc raw"""
    conjugates_complex(x::AbsSimpleNumFieldElem, abs_tol::Int) -> Vector{AcbFieldElem}

Compute the complex conjugates of $x$ as elements of type `AcbFieldElem`.
Recall that we order the complex conjugates
$\sigma_{r+1}(x),...,\sigma_{r+2s}(x)$ such that
$\sigma_{i}(x) = \overline{\sigma_{i + s}(x)}$ for $r + 1 \leq i \leq r + s$.

Every entry $y$ of the array returned satisfies
`radius(real(y)) < 2^-abs_tol` and `radius(imag(y)) < 2^-abs_tol`.
"""
function conjugates_complex(x::AbsSimpleNumFieldElem, abs_tol::Int = 32, T = ArbFieldElem)
  if T === ArbFieldElem
    return conjugates_arb_complex(x, abs_tol)
  else
    error("Cannot return real conjugates as type $T")
  end
end

function conjugates_arb_complex(x::AbsSimpleNumFieldElem, abs_tol::Int)
  r1, r2 = signature(parent(x))
  c = conjugates_arb(x, abs_tol)
  z = Vector{AcbFieldElem}(undef, r2)

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

@doc raw"""
    conjugates_arb_log(x::AbsSimpleNumFieldElem, abs_tol::Int) -> Vector{ArbFieldElem}

Returns the elements
$(\log(\lvert \sigma_1(x) \rvert),\dotsc,\log(\lvert\sigma_r(x) \rvert),
\dotsc,2\log(\lvert \sigma_{r+1}(x) \rvert),\dotsc,
2\log(\lvert \sigma_{r+s}(x)\rvert))$ as elements of type `ArbFieldElem` with radius
less then `2^-abs_tol`.
"""
function conjugates_log(x::AbsSimpleNumFieldElem, abs_tol::Int = 32, T = ArbFieldElem)
  if T === ArbFieldElem
    return conjugates_arb_log(x, abs_tol)
  else
    error("Cannot return real conjugates as type ", T)
  end
end

function conjugates_arb_log(x::AbsSimpleNumFieldElem, abs_tol::Int)
  K = parent(x)
  c = conjugate_data_arb_roots(K, abs_tol)
  r1 = length(c.real_roots)
  r2 = length(c.complex_roots)
  d = degree(K)
  target_tol = abs_tol

  # TODO: Replace this using multipoint evaluation of libarb
  z = Array{ArbFieldElem}(undef, r1 + r2)
  while true
    prec_too_low = false
    c = conjugate_data_arb_roots(K, abs_tol)
    if abs_tol > 2^20
      error("Something wrong in conjugates_arb_log")
    end
    xpoly = ArbPolyRingElem(parent(K.pol)(x), abs_tol)
    RR = ArbField(abs_tol, cached = false)
    for i in 1:r1
      o = RR()
      ccall((:arb_poly_evaluate, libarb), Nothing,
            (Ref{ArbFieldElem}, Ref{ArbPolyRingElem}, Ref{ArbFieldElem}, Int),
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

    CC = AcbField(abs_tol, cached = false)

    tacb = CC()
    for i in 1:r2
      oo = RR()
      ccall((:arb_poly_evaluate_acb, libarb), Nothing,
            (Ref{AcbFieldElem}, Ref{ArbPolyRingElem}, Ref{AcbFieldElem}, Int),
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

function conjugates_arb_log(x::AbsSimpleNumFieldElem, R::ArbField)
  z = conjugates_arb_log(x, R.prec)
  return map(R, z)
end

################################################################################
#
#  Minkowski map
#
################################################################################

@doc raw"""
    minkowski_map(a::AbsSimpleNumFieldElem, abs_tol::Int) -> Vector{ArbFieldElem}

Returns the image of $a$ under the Minkowski embedding.
Every entry of the array returned is of type `ArbFieldElem` with radius less then
`2^(-abs_tol)`.
"""
function minkowski_map(a::T, abs_tol::Int = 32) where T <: NumFieldElem
  z = _minkowski_map_and_apply(a, abs_tol, identity)
  return z
end

# The following function computes the minkowski_map, applies G to the output.
# G mus be a function (::Vector{ArbFieldElem}, abs_tol::Int) -> Bool, *
# where the first return value indicates if the result is good enough
function _minkowski_map_and_apply(a, abs_tol, G, work_tol::Int = abs_tol)
  K = parent(a)
  A = Array{ArbFieldElem}(undef, absolute_degree(K))
  c = conjugates_arb(a, work_tol)::Vector{AcbFieldElem}
  r, s = signature(K)

  for i = 1:r
    @assert isreal(c[i])
    A[i] = real(c[i])
    if !radiuslttwopower(A[i], -abs_tol)
      error("this should not happen")
    end
  end

  if work_tol > 2^18 || abs_tol > 2^18
    error("asdsd")
  end

  #R = ArbField(precision(parent(c[1])), false)
  R = ArbField(2 * work_tol, cached = false)
  sqrt2 = sqrt(R(2))

  for i in 1:s
    t = c[r + i]
    A[r + 2*i - 1] = sqrt2 * real(t)
    A[r + 2*i] = sqrt2 * imag(t)
    if !radiuslttwopower(A[r + 2*i], -abs_tol)
      return _minkowski_map_and_apply(a, abs_tol, G, Int(floor(work_tol * 2)))
    end
  end

  if typeof(G) === typeof(identity)
    return A
  else
    b, B = G(A, abs_tol)
    if b
      return B
    else
      return _minkowski_map_and_apply(a, abs_tol, G, 2*work_tol)
    end
  end
end

################################################################################
#
#  T_2
#
################################################################################

function t2(x::S, abs_tol::Int = 32, T = ArbFieldElem) where S <: NumFieldElem
  if T === ArbFieldElem
    g = function(w, abs_tol)
      z = mapreduce(y -> y^2, +, w)
      return radiuslttwopower(z, -abs_tol), z
    end
    c = _minkowski_map_and_apply(x, abs_tol, g)
    return c
  else
    throw(NotImplemented())
  end
end

############################################################################
#
#  Signs of real embeddings
#
############################################################################

#@doc raw"""
##    _signs(a::AbsSimpleNumFieldElem) -> Vector{Int}
#> For a non-zero element $a$ return the signs of all real embeddings.
#"""
function _signs(a::AbsSimpleNumFieldElem)
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
      s[i] = is_positive(real(c[i])) ? 1 : -1
    end
    if done
      return s
    end
  end
end

#@doc raw"""
##    signs(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}) -> Vector{Int}
#> For a non-zero element $a$ in factored form,
#> return the signs of all real embeddings.
#"""
function _signs(a::FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField})
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

@doc raw"""
    complex_conjugation(K::AbsSimpleNumField)

Given a normal number field, this function returns an automorphism which is the
restriction of complex conjugation at one embedding.
"""
function complex_conjugation(K::AbsSimpleNumField; auts::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}} = morphism_type(AbsSimpleNumField, AbsSimpleNumField)[])
  get_attribute!(K, :complex_conjugation) do
    if is_totally_real(K)
      return id_hom(K)
    end
    if !isempty(auts)
      A = auts
    else
      A = automorphism_list(K)
      if length(A) < degree(K)
        error("Number field must be normal")
      end
    end
    a = gen(K)
    d = length(A)
    !is_totally_complex(K) && error("Number field must be totally complex")
    #First, quick and dirty. If only one automorphism works, then we return it
    p = 32
    while true
      c = conjugates(a, p)
      for i = 1:d
        if !is_involution(A[i])
          continue
        end
        cc = conj.(conjugates(image_primitive_element(A[i]), p))
        for k = 1:d
          if overlaps(c[k], cc[k])
            found = true
            for j = 1:d
              if j == k
                continue
              end
              if overlaps(c[j], cc[k])
                found = false
                break
              end
            end
            if found
              return A[i]
            end
          end
        end
      end
      p = 2 * p
      if p > 2^18
        error("Precision too high in complex_conjugation")
      end
    end
    error("something went wrong!")
  end::morphism_type(K)
end

@doc raw"""
    conj(a::AbsSimpleNumFieldElem)

Given an element $a$ of a normal number field, return the image of $a$ under
complex conjugation.
"""
conj(a::AbsSimpleNumFieldElem) = complex_conjugation(parent(a))(a)

function _find_complex_conjugation(K::AbsSimpleNumField, A::Vector{<:NumFieldHom{AbsSimpleNumField, AbsSimpleNumField}})
  a = gen(K)
  #First, quick and dirty. If only one automorphism works, then we return it
  p = 32
  while true
    c = conjugates(a, p)
    overlap = false
    for i = 1:length(A)
      if !is_involution(A[i])
        continue
      end
      cc = conj.(conjugates(image_primitive_element(A[i]), p))
      for k = 1:degree(K)
        if overlaps(c[k], cc[k])
          overlap = true
          found = true
          for j = 1:degree(K)
            if j == k
              continue
            end
            if overlaps(c[j], cc[k])
              found = false
              break
            end
          end
          if found
            return true, A[i]
          end
        end
      end
    end
    if !overlap
      break
    end
    if p > 2^18
      error("Precision too high in complex_conjugation")
    end
  end
  return false, A[1]
end

function is_complex_conjugation(f::NumFieldHom{AbsSimpleNumField, AbsSimpleNumField})
  K = domain(f)
  @assert K == codomain(f)
  !is_totally_complex(K) && error("Number field must be totally complex")
  p = 32
  d = degree(K)
  a = gen(K)
  img_a = image_primitive_element(f)
  while true
    c = conjugates(a, p)
    cc = conj.(conjugates(img_a, p))
    for i = 1:degree(K)
      if !overlaps(c[i], cc[i])
        return false
      end
    end
    #Now I need to assure that the precision is enough.
    found = true
    for j in 1:d-1
      if overlaps(c[d], cc[j])
        found = false
        break
      end
    end
    if found
      return true
    end
    p = 2 * p
    if p > 2^18
      error("Precision too high in complex_conjugation")
    end
  end
end
