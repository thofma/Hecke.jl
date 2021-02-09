export binary_quadratic_form, can_solve, discriminant,
       fundamental_discriminant, isdiscriminant, QuadBin,
       isfundamental_discriminant, prime_form, prime_power_form, cycle,
       isindefinite, ispositive_definite, isnegative_definite, isreduced

import Nemo: can_solve

###############################################################################
#
#   Constructor
#
###############################################################################

@doc Markdown.doc"""
    binary_quadratic_form(a::T, b::T, c::T) where {T <: RingElement}

Constructs the binary quadratic form $ax^2 + bxy + cy^2$.
"""
binary_quadratic_form(a::T, b::T, c::T) where {T <: RingElem} = QuadBin(parent(a), a, b, c)

binary_quadratic_form(a::Integer, b::Integer, c::Integer) = binary_quadratic_form(FlintZZ(a), FlintZZ(b), FlintZZ(c))

@doc Markdown.doc"""
    binary_quadratic_form(R::Ring, a, b, c)

Constructs the binary quadratic form $ax^2 + bxy + cy^2$ over the ring $R$.
The elements `a`, `b` and `c` are coerced into the ring $R$.
"""
binary_quadratic_form(R::Ring, a, b, c) = binary_quadratic_form(R(a), R(b), R(c))

################################################################################
#
#  Printing
#
################################################################################

function show(io::IO, ::MIME"text/plain", f::QuadBin)
  _show(io, f, get(io, :compact, false))
end

function show(io::IO, f::QuadBin)
  _show(io, f, true)
end

function _show(io::IO, f::QuadBin, compact = false)
  if !compact
    print(io, "Binary quadratic form with equation\n")
  end
  sum = Expr(:call, :+)
  a = f[1]
  if !iszero(a)
    if isone(a)
      push!(sum.args, Expr(:call, :*, Expr(:call, :^, :x, 2)))
    else
      push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(a, context = io), Expr(:call, :^, :x, 2)))
    end
  end
  b = f[2]
  if !iszero(b)
    if isone(b)
      push!(sum.args, Expr(:call, :*, :x, :y))
    else
      push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(b, context = io), :x, :y))
    end
  end
  c = f[3]
  if !iszero(c)
    if isone(c)
      push!(sum.args, Expr(:call, :*, Expr(:call, :^, :y, 2)))
    else
      push!(sum.args, Expr(:call, :*, AbstractAlgebra.expressify(c, context = io), Expr(:call, :^, :y, 2)))
    end
  end
  print(io, AbstractAlgebra.expr_to_string(AbstractAlgebra.canonicalize(sum)))
end

################################################################################
#
#   Base ring
#
################################################################################

base_ring(f::QuadBin{T}) where {T} = f.base_ring::parent_type(T)

###############################################################################
#
#   Coefficients
#
###############################################################################

function getindex(f::QuadBin, i::Int)
  if i == 1
    return f.a
  elseif i == 2
    return f.b
  elseif i == 3
    return f.c
  else
    throw(error("Index must be between 1 and 3"))
  end
end

################################################################################
#
#   Scalar multiplication
#
################################################################################

function Base.:(*)(c::T, f::QuadBin{T}) where T <: RingElem
  return binary_quadratic_form(c * f[1], c * f[2], c * f[3])
end

function Base.:(*)(c::fmpz, f::QuadBin{T}) where T <: RingElem
  return binary_quadratic_form(c * f[1], c * f[2], c * f[3])
end

function Base.:(*)(c::Integer, f::QuadBin)
  return binary_quadratic_form(c * f[1], c * f[2], c * f[3])
end

function divexact(f::QuadBin{T}, c::T) where T <: RingElem
  return binary_quadratic_form(divexact(f[1], c), divexact(f[2], c),
                                                  divexact(f[3], c))
end

###############################################################################
#
#  Evaluation
#
###############################################################################

(f::QuadBin)(x, y) = f[1]*x^2 + f[2] * x * y + f[3] * y^2

################################################################################
#
#  Representation
#
################################################################################

@doc Markdown.doc"""
     can_solve_with_solution(f::QuadBin, n::Int64)
For a binary quadratic form $f$ with negative discriminant and an integer $n$,
returns tuple (`true`, (`x`,`y`)) if $f$(`x`,`y`) = $n$ for integers `x`,`y`.
If no such integers exist, return (`false`,(0,0))
"""
function can_solve(f::QuadBin, n::Int64)
    if discriminant(f) >= 0
        @error("$f has non-negative discriminant")
    end
    for y in 1:Int64(floor(sqrt(Int64(4*f[1]*n)//abs(Int64(discriminant(f))))))
        #now f(x,y) quadratic in one variable -> use quadratic formula
        aq = f[1]
        bq = f[2] * y
        cq = f[3] * y^2 - n
        d = bq^2 - 4*aq*cq
        if issquare(d)
            if divides(-bq + sqrt(d), 2*aq)[1]
                return(true, (divexact(-bq + sqrt(d), 2*aq), ZZ(y)))
            end
            if divides(-bq - sqrt(d), 2*aq)[1]
                return(true, (divexact(-bq - sqrt(d), 2*aq), ZZ(y)))
            end
        end
    end
    return (false, (FlintZZ(0),ZZ(0)))
end

###############################################################################
#
#   Discriminant
#
###############################################################################

@doc Markdown.doc"""
    discriminant(f::QuadBin) -> RingElem

Return the discriminant of `f = [a, b, c]`, that is, `b^2 - 4ac`.
"""
function discriminant(f::QuadBin)
  if isdefined(f, :disc)
    return f.disc
  else
    d = f[2]^2 - 4 * f[1] * f[3]
    f.disc = d
    return d
  end
end

################################################################################
#
#  Discriminant of integral binary quadratic form
#
################################################################################

@doc Markdown.doc"""
    isdiscriminant(D)

Returns `true` if $D$ is the discriminant of an integral binary quadratic form,
otherwise returns `false`.
"""
function isdiscriminant(D::Union{Integer, fmpz})
  if D == 0
    return false
  end
  m = mod(D, 4)
  if m == 0 || m == 1
    return true
  end
  return false
end

@doc Markdown.doc"""
    isfundamental_discriminant(D)

Returns `true` if $D$ is a fundamental discriminant otherwise returns `false`.
"""
function isfundamental_discriminant(D::Union{Integer, fmpz})
  m = mod(D, 4)
  if m == 1 && issquarefree(D)
    return true
  end
  if m == 0
    h = divexact(D, 4)
    c = mod(h,4)
    if (c == 2 || c == 3) && issquarefree(h)
      return true
    end
  end
  return false
end

@doc Markdown.doc"""
     conductor(D) -> fmpz
Returns the conductor of the discriminant $D$, that is, the largest
positive integer $c$ such that $\frac{D}{c^2}$ is a discriminant.
"""
function conductor(D::Union{Integer, fmpz})
  @req isdiscriminant(D) "Value ($D) not a discriminant"
  d = divexact(D, fundamental_discriminant(D))
  return isqrt(d)
end

function fundamental_discriminant(D::Union{Integer, fmpz})
  fac = factor(D)
  sqf = one(FlintZZ)
  for (p, e) in fac
    if isodd(e)
      sqf = sqf * p
    end
  end
  # sqf = is the squarefree-part, so D = sqf * square and sqf square-free
  if mod(sign(D) * sqf, 4) == 1
    return sign(D) * sqf
  else
    return sign(D) * sqf * 4
  end
end

###############################################################################
#
#   Equality
#
###############################################################################

function ==(f1::QuadBin, f2::QuadBin)
  if base_ring(f1) != base_ring(f2)
    return false
  end
  return f1[1] == f2[1] && f1[2] == f2[2] && f1[3] == f2[3]
end

###############################################################################
#
#   Arithmetic
#
###############################################################################

conjugate(f::QuadBin) = binary_quadratic_form(f[1], -f[2], f[3])

-(f::QuadBin) = binary_quadratic_form(-f[1], -f[2], -f[3])

Generic.content(f::QuadBin{fmpz}) = gcd([f[1], f[2], f[3]])

isindefinite(f::QuadBin) = discriminant(f) > 0 ? true : false

isnegative_definite(f::QuadBin) = (discriminant(f) < 0 && f[1] < 0)

ispositive_definite(f::QuadBin) = (discriminant(f) < 0 && f[1] > 0)

Base.iszero(f::QuadBin) = (f[1] == 0 && f[2] == 0 && f[3] == 0)

isprimitive(f::QuadBin) = (isone(content(f)))

isreducible(f::QuadBin) = issquare(discriminant(f))

###############################################################################
#
#   Composition
#
###############################################################################


@doc Markdown.doc"""
    compose(f1::QuadBin, f2::QuadBin)

Returns the composition of the binary quadratic forms $f_1$ and $f_2$. The
result is not reduced, uses Dirichlet Composition.
"""
function compose(f1::QuadBin{fmpz}, f2::QuadBin{fmpz})
  #discriminants have to match
  D = discriminant(f1)
  D2 = discriminant(f2)
  if D != D2
    error("discriminants do not match")
  end
  (h, n_1, n_2) = gcdx(f1[1], f2[1])
  (e, n_3, n3) = gcdx(h, divexact(f1[2]+f2[2], 2))

  (n1, n2) = (n_3 * n_1, n_3 * n_2)
  B = n1 * divexact(f1[1] * f2[2], e) + n2 * divexact(f1[2] * f2[1], e) + n3 * divexact(f1[2] * f2[2] + D, 2*e)
  return binary_quadratic_form(divexact(f1[1]*f2[1], e^2), B, divexact(e^2*(B^2-D), 4*f1[1]*f2[1]))
end

###############################################################################
#
#   Prime Forms
#
###############################################################################

function _sqrtmod4P(d::fmpz, p::fmpz)
    if jacobi_symbol(mod(d, p), p) == -1
        error("$d is no square modulo $p")
    end
    if p == 2
        if iseven(d)
            return 2 * mod(divexact(d, 4), 2)
        else
            return 1
        end
    else
        r = sqrtmod(d, p)
        if mod(r,2) == mod(d,2)
            return r
        else
            return p-r
        end
    end
end

function _number_of_primeforms(d::fmpz, p::fmpz)
    return jacobi_symbol(mod(d, p), p) + 1
end

@doc Markdown.doc"""
     prime_form(d::fmpz, p::fmpz)
Returns an integral binary quadratic form of discriminant $d$ and leading coefficient
$p$ where $p$ is a prime number.
"""
function prime_form(d::fmpz, p::fmpz)
    if !isdiscriminant(d)
        error("$d is no discriminant")
    end
    if _number_of_primeforms(d, p) == 0
        error("prime form does not exist")
    end
    b = _sqrtmod4P(d, p)
    return binary_quadratic_form(p, b, divexact(b^2-d, 4*p))
end

function _sqrtmod4PE(d::fmpz, p::fmpz, e)
    if mod(d,p) == 0
        n = 1
        while (2*n + 2  <= e && mod(p^(2n+2), d) == 0)
            n = n + 1
        end
        if (p == 2 && !mod(2^(-2*n)*d, 4) in [0,1])
            n = n -2
        end
        d0 = divexact(d, p^(2*n))
        e0 = e - 2*n
        if e0 == 0
            return p^n*mod(d0, 2)
        else return p^n * _sqrtmod4PE(d0, p^e0, e)
        end
    else
        b = _sqrtmod4P(d, p)
        f = 1
        while f < e
            k = mod(divexact(d-b^2, b*4*p^f), p)
            b = mod(b + 2*k*p^f, 2*p^(f+1))
            f = f + 1
        end
        if b > p^e
            return b-2*p^e
        else
            return b
        end
    end
end

@doc Markdown.doc"""
     prime_power_form(d::fmpz, p::fmpz, e)
Returns an integral binary quadratic form of discriminant $d$ and leading coefficient
$p$^$e$ where $p$ is a prime number.
"""
function prime_power_form(d::fmpz, p::fmpz, e)
    if !isdiscriminant(d)
        @error("$d is no discriminant")
    end
    b = _sqrtmod4PE(d, p, e)
    c = divexact(b^2-d, 4*p^e)
    f = binary_quadratic_form(p^e, b, c)
    if discriminant(f) != d
        @error("prime power form does not exist")
    end
    return f
end

################################################################################
#
#  Equivalence
#
################################################################################

@doc Markdown.doc"""
    isequivalent(f::QuadBin{fmpz}, g::QuadBin{fmpz}; proper::Bool = false)

Return whether `f` and `g` are (properly) equivalent.
"""
function isequivalent(f::QuadBin{fmpz}, g::QuadBin{fmpz}; proper::Bool = true)
  d = discriminant(f)
  if d != discriminant(g)
    return false
  end

  if issquare(d)
    return _isequivalent_reducible(f, g, proper = proper)[1]
  end

  if isindefinite(f)
    fred = reduction(f)
    gred = reduction(g)
    if issquare(d)
      # Make sure we terminate in a form with c = 0
      while !iszero(fred[3])
        fred, = _rho(fred)
      end
      while !iszero(gred[3])
        gred, = _rho(gred)
      end
      b = fred[2]
      a = fred[1]
      a0 = gred[1]
      if proper
        return (a - a0) % (2*b) == 0
      else
        g = gcd(a, b)
        return (a * a0 - g^2 ) % (2 * b * g) == 0
      end
    end

    prop_cyc = cycle(gred, proper = true)

    is_prop = fred in prop_cyc
    if proper || is_prop
      return is_prop
    end
    
    # note that our definition of improper equivalence
    # differs from that of Buchmann and Vollmer
    # their action is det f * q(f(x,y))
    # ours is q(f(x,y))

    # an improper equivalence in our convention

    fred = binary_quadratic_form(fred[3], fred[2], fred[1])
    @assert isreduced(fred)
    return fred in prop_cyc
  else
    if ispositive_definite(f) && !ispositive_definite(g)
      return false
    end

    if isnegative_definite(f) && !isnegative_definite(g)
      return false
    end

    fred = reduction(f)
    gred = reduction(g)
    if fred == gred
      return true
    end

    if !proper
      f1 = reduction(binary_quadratic_form(f[3], f[2], f[1]))
      return f1 == gred
    end
    
    return false
  end
end

function _isequivalent_reducible(f::QuadBin{fmpz}, g::QuadBin{fmpz}; proper = true)
  if discriminant(f) != discriminant(g)
    return false
  end

  c = content(f) 
  if content(g) != c
    return false
  end

  fpr = divexact(f, c)
  gpr = divexact(g, c)

  fred, Tf = _reduction(fpr)
  gred, Tg = _reduction(gpr)

  fl = fred == gred

  if proper || fl
    T = Tf * inv(Tg)
    if fl
      @assert Hecke._action(f, T) == g
    end
    return fl, T
  end

  if fred[1] == invmod(gred[1], gred[2])
    gg = binary_quadratic_form(gred[1], -gred[2], zero(fmpz))
    _, Tgg = reduction_with_transformation(gg)
    T = Tf * inv(Tg * matrix(FlintZZ, 2, 2, [1, 0, 0, -1]) * Tgg)
    @assert Hecke._action(f, T) == g
    return true, T
  end

  return false, Tf
end

################################################################################
#
#  Reduction and cycles
#
################################################################################

@doc Markdown.doc"""
    reduction(f::QuadBin{fmpz}) -> QuadBin{fmpz}

Return a reduced binary quadratic form equivalent to `f`.
"""
function reduction(f::QuadBin{fmpz})
  g, _ = _reduction(f)
  return g
end

@doc Markdown.doc"""
    reduction_with_transformation(f::QuadBin{fmpz}) -> QuadBin{fmpz}, Mat{fmpz}

Return a reduced binary quadratic form `g` equivalent to `f` and a matrix `T`
such that `f.T = g`.
"""
function reduction_with_transformation(f::QuadBin{fmpz})
  return _reduction(f)
end

function _reduction(f::QuadBin{fmpz})
  if isreducible(f)
    return _reduction_reducible(f)
  end

  if isreduced(f)
    return f, identity_matrix(FlintZZ, 2)
  end

  if isindefinite(f)
    return _reduction_indefinite(f)
  end

  throw(NotImplemented())
end

# TODO (TH):
# - Make the functions operate on (a, b, c)
# - Don't build up T, just do the operations directly on U
function _reduction_indefinite(f)
  # Compute a reduced form in the proper equivalence class of f
  RR = ArbField(53, cached = false)
  U = identity_matrix(FlintZZ, 2)
  d = sqrt(RR(discriminant(f)))
  while !isreduced(f)
    a = f[1]
    b = f[2]
    c = f[3]
    cabs = abs(c)
    # Now compute rho(f) as defined on p. 122, equation (6.12) in [BV2007]
    if !iszero(cabs)
      if cabs >= d
        s = sign(c) * round(fmpz, fmpq(cabs + b, 2 * cabs), RoundDown) # floor(cabs + b/2 * abs)
      else
        @assert d > cabs # might fail with precision too low
        e = floor(divexact(d + b, 2 * cabs))
        fl, o = unique_integer(e)
        @assert fl # might fail with precision too low
        s = sign(c) * o
      end
      T = matrix(FlintZZ, 2, 2, [0, -1, 1, s])
      U = U * T
      _f = binary_quadratic_form(c, -b + 2*s*c, c*s*s - b*s + a)
      @assert _buchmann_vollmer_action(f, T) == _f
      f = _f
    else
      if b < 0
        T = matrix(FlintZZ, 2, 2, [1, 0, 0, -1])
        U = U * T
        _f = binar_quadratic_form(a, -b, c)
        @assert _buchmann_vollmer_action(f, T) == _f
        f = _f
      else
        q, r = divrem(a, b)
        if 2*r > b
          q, r = divrem(a, -b)
          q = -q
        end
        T = matrix(FlintZZ, 2, 2, [1, 0, -q, 1])
        U = U * T
        _f = binary_quadratic_form(r, b, c)
        @assert _buchmann_vollmer_action(f, T) == _f
        f = _f
      end
    end
  end
  return f, U
end

function _reduction_reducible(f::QuadBin)
  d = discriminant(f)
  N = sqrt(d)
  @assert N^2 == d
  @assert isprimitive(f)
  if iszero(f[1])
    x = -f[3]
    y = f[2]
  else
    x = N - f[2]
    y = 2 * f[1]
  end
  @assert iszero(f(x, y))
  gg = gcd(x, y)
  x = divexact(x, gg)
  y = divexact(y, gg)
  _,w, _z = gcdx(x, y)
  z = -_z
  @assert x * w - y * z == 1
  T = matrix(FlintZZ, 2, 2, [x, z, y, w])
  g = Hecke._action(f, T)
  # Now g = [0, +/- N, g[2]]
  @assert iszero(g[1])
  @assert abs(g[2]) == N
  TT = matrix(FlintZZ, 2, 2, [0, -1, 1, 0])
  g = Hecke._action(g, TT)
  T = T * TT
  # Now g = [g[1], N, 0]
  @assert abs(g[2]) == N
  if g[2] < 0
    aa = invmod(g[1], N)
    t = divexact(a * aa' - 1)
    # a * aa - N * t == 1
    @assert a * aa - N * t == 1
    TT = matrix(FlintZZ, 2, 2, [aa, -N, -t, a])
    g = Hecke._action(g, TT)
    T = T * TT
  end
  @assert g[2] == N
  _t, r = divrem(g[1], N)
  if r < 0
    r += N
    _t -= 1
  end
  @assert r >= 0
  @assert r < N
  @assert g[1] - _t * N == r
  TT = matrix(FlintZZ, 2, 2, [1, 0, -_t, 1])
  g = Hecke._action(g, TT)
  T = T * TT
  @assert 1 <= g[1] < N && g[2] == N && iszero(g[3])
  @assert det(T) == 1
  @assert g == Hecke._action(f, T)
  return g, T
end

function _buchmann_vollmer_action(f::QuadBin, M)
  a = f[1]
  b = f[2]
  c = f[3]
  s = M[1, 1]
  t = M[1, 2]
  u = M[2, 1]
  v = M[2, 2]
  a1 = f(s, u)
  b1 = 2*(a*s*t + c*u*v) + b*(s*v + t*u)
  c1 = f(t, v)
  return det(M) * binary_quadratic_form(a1, b1, c1)
end

function _action(f::QuadBin, M)
  a = f[1]
  b = f[2]
  c = f[3]
  s = M[1, 1]
  t = M[1, 2]
  u = M[2, 1]
  v = M[2, 2]
  a1 = f(s, u)
  b1 = 2*(a*s*t + c*u*v) + b*(s*v + t*u)
  c1 = f(t, v)
  return binary_quadratic_form(a1, b1, c1)
end

@doc Markdown.doc"""
    isreduced(f::QuadBin{fmpz}) -> Bool

Return whether `f` is reduced in the following sense. Let `f = [a, b, c]`
be of discriminant `D`.

If `f` is positive definite (`D < 0` and `a > 0`), then `f` is reduced if and
only if `|b| <= a <= c`, and `b >= 0` if `a = b` or `a = c`.

If `f` is negative definite (`D < 0` and `a < 0`), then `f` is reduced if and
only if `[-a, b, -c]` is reduced.

If `f` is indefinite (`D > 0), then `f` is reduced if and only if
`|sqrt{D} - 2|a|| < b < \sqrt{D}|` or `a = 0` and `-b < 2c <= b` or `c = 0` and
`-b < 2a <= b`.
"""
function isreduced(f::QuadBin{fmpz})
  D = discriminant(f)
  a = f[1]
  b = f[2]
  c = f[3]
  if D < 0 && a > 0
    return ((-a < b <= a < c) || (0 <= b <= a == c))
  elseif D <0 && a < 0
    return ((a < b <= -a < -c) || (0 <= b <= -a == -c))
  else
    # First the two easy conditions
    if (0 == a && -b < 2*c <= b) || (0 == c && -b < 2*a <= b)
      return true
    end

    if (b^2 > D)
      return false
    end

    R = ArbField(64, cached = false)
    d = sqrt(R(D))
    z = abs(d - 2 * abs(a))
    @assert !contains(z, b)
    if z < b
      return true
    else
      return false
    end
  end
end

@doc Markdown.doc"""
    cycle(f::QuadBin{fmpz}; proper::Bool = false) -> Vector{QuadBin{fmpz}}

Return the cycle of `f` as defined by Buchmann--Vollmer (Algorithm 6.1). The
cycle consists of all reduced, equivalent forms `g`, such that first coefficient of
`f` and `g` have the same sign. The proper cycle consists of all equivalent forms,
and has either the same or twice the size of the cycle. In the latter case, the
cycle has odd length.
"""
function cycle(f::QuadBin{fmpz}; proper::Bool = false)
  @req isindefinite(f) "Quadratic form must be indefinite"
  @req isreduced(f) "Quadratic form must be reduced"

  if issquare(discriminant(f))
    throw(NotImplemented())
  end

  if proper
    # Proposition 6.10.5 in [BV2007]
    # If we decided to cache this, this must be changed
    C = cycle(f, proper = false)
    if isodd(length(C))
      append!(C, C)
    end

    for i in 1:div(length(C), 2)
      C[2*i], = _tau(C[2*i]) # tau returns also the operator
    end
    return C
  end

  return _nonproper_cycle(f)
end

function _nonproper_cycle(f::QuadBin{fmpz})
  if isdefined(f, :nonproper_cycle)
    return f.nonproper_cycle::Vector{QuadBin{fmpz}}
  end
  C = typeof(f)[f]
  Q1, T = _rhotau(f)
  while !(f == Q1)
    push!(C, Q1)
    Q1, = _rhotau(Q1)
  end
  f.nonproper_cycle = C
  return C
end

# Transform f into rho(tau(f)), as defined in equation (6.12) of
# Buchmann--Vollmer 2007.
function _rhotau(f::QuadBin{fmpz})
  RR = ArbField(64, cached = false)
  d = sqrt(RR(discriminant(f)))
  a = f[1]
  b = f[2]
  c = f[3]
  cabs = abs(c)
  if cabs >= d
    s = sign(c) * round(fmpz, fmpq(cabs + b, 2 * cabs), RoundDown) # floor(cabs + b/2 * abs)
  else
    @assert d > cabs # might fail with precision too low
    e = floor(divexact(d + b, 2 * cabs))
    fl, o = unique_integer(e)
    @assert fl # might fail with precision too low
    s = sign(c) * o
  end
  g = binary_quadratic_form(-c, -b + 2*s*c, -(a - b*s + c*s*s))
  T = matrix(FlintZZ, 2, 2, [0, 1, 1, -s])
  @assert _buchmann_vollmer_action(f, T) == g
  return (g, T)
end

# Apply the rho operator as defined by Buchmann--Vollmer
function _rho(f::QuadBin{fmpz})
  RR = ArbField(64, cached = false)
  d = sqrt(RR(discriminant(f)))
  a = f[1]
  b = f[2]
  c = f[3]
  cabs = abs(c)
  # Now compute rho(f) as defined on p. 122, equation (6.12) in [BV2007]
  if cabs >= d
    s = sign(c) * round(fmpz, fmpq(cabs + b, 2 * cabs), RoundDown) # floor(cabs + b/2 * abs)
  else
    @assert d > cabs # might fail with precision too low
    e = floor(divexact(d + b, 2 * cabs))
    fl, o = unique_integer(e)
    @assert fl # might fail with precision too low
    s = sign(c) * o
  end
  T = matrix(FlintZZ, 2, 2, [0, -1, 1, s])
  g = binary_quadratic_form(c, -b + 2*s*c, a - b*s + c*s*s)
  @assert _buchmann_vollmer_action(f, T) == g
  return g, T
end

# Apply the tau operator of Buchmann--Vollmer, which turns
# [a, b, c] into [-a, b, -c]
function _tau(f::QuadBin{fmpz})
  T = matrix(FlintZZ, 2, 2, [1, 0, 0, -1])
  g = binary_quadratic_form(-f[1], f[2], -f[3])
  @assert _buchmann_vollmer_action(f, T) == g
  return g, T
end
