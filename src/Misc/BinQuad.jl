export binary_quadratic_form, can_solve, discriminant,
       fundamental_discriminant, isdiscriminant, QuadBin,
       isfundamental_discriminant, prime_form, prime_power_form, cycle,
       isindefinite, ispositive_definite, isnegative_definite, isreduced

###############################################################################
#
#   Constructor
#
###############################################################################

@doc Markdown.doc"""
     binary_quadratic_form(a, b, c)
Constructs the integral binary quadratic form $a$ * x^2 + $b$ * x * y + $c$ * y^2.
"""
binary_quadratic_form(a, b, c) = QuadBin(a, b, c)

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

###############################################################################
#
#   Values
#
###############################################################################

(f::QuadBin)(x,y) = f[1]*x^2 + f[2] * x * y + f[3] * y^2

@doc Markdown.doc"""
     can_solve(f::QuadBin, n::Int64)
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
    return (false,(ZZ(0),ZZ(0)))
end

###############################################################################
#
#   Discriminant
#
###############################################################################

discriminant(f::QuadBin) = f[2]^2 - 4 * f[1] * f[3]

@doc Markdown.doc"""
     isdiscriminant(D)
Returns `true` if $D$ is the discriminant of an integral binary
quadratic form, otherwise returns `false`.
"""
function isdiscriminant(D)
    if D == 0
        return false
    end
    m = mod(D,4)
    if m == 0 || m == 1
        return true
    end
    return false
end

@doc Markdown.doc"""
     isfundamental_discriminant(D)
Returns `true` if $D$ is a fundamental discriminant i.e. has conductor `1`,
otherwise returns `false`.
"""
function isfundamental_discriminant(D)
    m = mod(D,4)
    if m == 1 && issquarefree(D)
        return true
    end
    if m == 0
        h = divexact(D,4)
        c = mod(h,4)
        if (c == 2 || c == 3) && issquarefree(h)
            return true
        end
    end
    return false
end

@doc Markdown.doc"""
     conductor(D)
Returns the conductor of the discriminant $D$ i.e. the largest
positive integer $c$ such that $\frac{D}{c^2}$ is a discriminant.
"""
function conductor(D)
  !isdiscriminant(D) && error("$D is no discriminant")
  d = divexact(D, fundamental_discriminant(D))
  return isqrt(d)
end

function fundamental_discriminant(D)
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
  return f1[1] == f2[1] && f1[2] == f2[2] && f1[3] == f2[3]
end

###############################################################################
#
#   Arithmetic
#
###############################################################################

conjugate(f::QuadBin) = binary_quadratic_form(f[1], -f[2], f[3])

-(f::QuadBin) = binary_quadratic_form(-f[1], -f[2], -f[3])

Generic.content(f::QuadBin) = gcd([f[1], f[2], f[3]])

isindefinite(f::QuadBin) = discriminant(f) > 0 ? true : false

isnegative_definite(f::QuadBin) = (discriminant(f) < 0 && f[1] < 0)

ispositive_definite(f::QuadBin) = (discriminant(f) < 0 && f[1] > 0)

Base.iszero(f::QuadBin) = (f[1] == 0 && f[2] == 0 && f[3] == 0)

isprimitive(f::QuadBin) = (content(f) == 1)

isreducible(f::QuadBin) = issquare(discriminant(f))

function isreduced(f::QuadBin)
    if ispositive_definite(f)
        return (abs(f[2]) <= f[1] <= f[3]) && (f[2] >= 0 || (f[1] != f[2] && f[1] != f[3]))
    end

    if isnegative_definite(f)
        return isreduced(-conjugate(f))
    end

    D = Int64(discriminant(f))

    if isindefinite(f)
        h = (abs(sqrt(D) - float(Int64(2*abs(f[1])))) < f[2] < sqrt(D)) || f[1] == 0 && -f[2] < 2*f[3] <= f[2]
        return (h || f[3]==0 && -f[2] < 2*f[1] <= f[2])
    end
end

###############################################################################
#
#   Reduction
#
###############################################################################

@doc Markdown.doc"""
     reduce(f::QuadBin)
Returns for the positive (or negative) definite binary quadratic form $f$ an equivalent
reduced form.
"""
function Base.reduce(f::QuadBin)
    if isindefinite(f)
        @error("Not implemented for $f indefinite")
    end
    if isnegative_definite(f)
        return reduce(-conjugate(f))
    end
    if ispositive_definite(f)
        return _reduce(f)[1]
    end
end

function _rho(f::QuadBin, T::fmpz_mat)
    s = _round_erec(f[2]//(2*f[3]))
    res_f = binary_quadratic_form(f[3], -f[2] + 2*s*f[3], f[3]*s^2 - f[2]*s + f[1])
    return(res_f, matrix(ZZ, 2, 2, [T[2], T[1] + s*T[2], T[4], T[3] + s*T[4]]))
end

function _normalize(f::QuadBin)
    s = _round_erec((f[1]-f[2])//(2*f[1]), dir = "down")
    res_f = binary_quadratic_form(f[1], f[2] + 2*s*f[1], f[1]*s^2 + f[2]*s + f[3])
    return(res_f, matrix(ZZ, 2, 2, [1, s, 0, 1]))
end

function _reduce(f::QuadBin)
    (g, T) = _normalize(f)
    while !_isreduced(g)
        (g, T) = _rho(g, T)
    end
    return (g, T)
end

function _isreduced(f::QuadBin)
    bol1 = f[1] <= f[3]
    bol2 = true
    if f[1] == f[3]
        bol2 = 0 <= f[2]
    end
    #reduced is checked, could be omitted
    bol3 = -f[1] < f[2] && f[2] <= f[1]

    return bol1 && bol2 && bol3
end

###############################################################################
#
#   Other Utilities
#
###############################################################################

function _round_erec(x::fmpq; dir = "none")
    if dir == "up"
        return fmpz(Int64(ceil(Rational{Int64}(x.num, x.den))))
    end
    if dir == "down"
        return fmpz(Int64(floor(Rational{Int64}(x.num, x.den))))
    end
    if dir == "none"
        if abs(x-_round_erec(x, dir = "up")) <= abs(x-_round_erec(x, dir = "down"))
            return _round_erec(x, dir = "up")
        else
            return _round_erec(x, dir = "down")
        end
    end
end

###############################################################################
#
#   Composition
#
###############################################################################

#COR7.3.17: f1,f2  same discriminant
# function Hecke.compose(f1::QuadBin, f2::QuadBin)
#     d = discriminant(f1)
#     Bm = numerator((b(f1) + b(f2))//2)
#     m = gcd(gcd(a(f1), a(f2)), Bm)
#     A = numerator((a(f1)*a(f2))//m^2)
#     #better?
#     j=1
#     k=1
#     l=1
#     while true
#         j = rand(-50:50)
#         k = rand(-50:50)
#         l = rand(-50:50)
#         if j*a(f2) + k*a(f1) + l*Bm == m
#             break
#         end
#     end
#     s = numerator(j*a(f2)*b(f1) + k*a(f1)*b(f2) + numerator((l*(b(f1)*b(f2)+d))//2)//m)
#     B = mod(s,2*A)
#     C = numerator((B^2-d)//(4*A))
#     return(QuadBin(A, B, C))
# end

###COMPOSITION###(Dirichlet)
#using Dirichlet composition, compare warwick Def 2.10

@doc Markdown.doc"""
     compose(f1::QuadBin, f2::QuadBin)
Returns the composition of the binary quadratic forms $f1$ and $f2$.
The result is not reduced, uses Dirichlet Composition.
"""
function compose(f1::QuadBin, f2::QuadBin)
    #discriminants have to match
    D = discriminant(f1)
    D2 = discriminant(f2)
    if !(D==D2)
        @error("discriminants do not match")
    end
    (h, n_1, n_2) = gcdx(f1[1], f2[1])
    (e, n_3, n3) = gcdx(h, divexact(f1[2]+f2[2], 2))

    (n1, n2) = (n_3 * n_1, n_3 * n_2)
    B = n1 * divexact(f1[1] * f2[2], e) + n2 * divexact(f1[2] * f2[1], e) + n3 * divexact(f1[2] * f2[2] + D, 2*e)
    return QuadBin(divexact(f1[1]*f2[1], e^2), B, divexact(e^2*(B^2-D), 4*f1[1]*f2[1]))
end

# cmpr Buchmann Alg 6.1
@doc Markdown.doc"""
     cycle(f::QuadBin)
Returns the cycle of the irreducible indefinite reduced form $f$.
"""
function cycle(f::QuadBin)
    if !isindefinite(f)
        @error("$f not indefinite")
    elseif !isreduced(f)
        @error("$f not reduced")
    elseif isreducible(f)
        @error("$f reducible")
    end

    Cycle = Vector([f])
    g = _rhoTau(f)
    while !(g==f)
        push!(Cycle, g)
        g = _rhoTau(g)
    end
    return Cycle
end

function _rhoTau(f::QuadBin)
    #s = round(f[2]//(2*f[3]))
    num = Int64(f[2])+Int64(floor(sqrt(Int64(discriminant(f)))))
    den = Int64(2*abs(f[3]))
    s =  Int64(Int64(floor(num/den)))
    return QuadBin(abs(f[3]), -f[2] + 2*s*abs(f[3]), -(f[1] + f[2]*s + f[3]*s^2))
end

###############################################################################
#
#   Prime Forms
#
###############################################################################

function _sqrtmod4P(d::fmpz, p::fmpz)
    if jacobi_symbol(mod(d, p), p) == -1
        @error("$d is no square modulo $p")
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
        @error("$d is no discriminant")
    end
    if _number_of_primeforms(d, p) == 0
        @error("prime form does not exist")
    end
    b = _sqrtmod4P(d, p)
    return QuadBin(p, b, divexact(b^2-d, 4*p))
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
    f = QuadBin(p^e, b, c)
    if discriminant(f) != d
        @error("prime power form does not exist")
    end
    return f
end
