# From Nemo/src/HeckeMoreStuff.jl
function shift_right(a::QadicFieldElem, n::Int)
    b = deepcopy(a)
    b.val -= n
    return b
end

function shift_left(a::QadicFieldElem, n::Int)
    b = deepcopy(a)
    b.val += n
    return b
end

Base.length(a::QadicFieldElem) = a.length

function Base.setprecision(q::QadicFieldElem, N::Int)
    r = parent(q)()
    r.N = N
    ccall((:padic_poly_set, libflint), Nothing, (Ref{QadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}), r, q, parent(q))
    return r
end

function Base.setprecision(q::PadicFieldElem, N::Int)
    r = parent(q)()
    r.N = N
    ccall((:padic_set, libflint), Nothing, (Ref{PadicFieldElem}, Ref{PadicFieldElem}, Ref{PadicField}), r, q, parent(q))
    return r
end

function setprecision!(q::QadicFieldElem, N::Int)
    if N >= q.N
        q.N = N
    end
    q.N = N
    ccall((:qadic_reduce, libflint), Nothing, (Ref{QadicFieldElem}, Ref{QadicField}), q, parent(q))
    #  @assert N >= q.N
    return q
end

function Base.setprecision(f::Generic.MPoly{QadicFieldElem}, N::Int)
    return map_coefficients(x -> setprecision(x, N), f, parent=parent(f))
end

function setprecision!(a::AbstractArray{QadicFieldElem}, N::Int)
    for x = a
        setprecision!(x, N)
    end
end

function Base.setprecision(a::AbstractArray{QadicFieldElem}, N::Int)
    return map(x -> setprecision(x, N), a)
end

function setprecision!(a::Generic.MatSpaceElem{QadicFieldElem}, N::Int)
    setprecision!(a.entries, N)
end

function Base.setprecision(a::Generic.MatSpaceElem{QadicFieldElem}, N::Int)
    b = deepcopy(a)
    setprecision!(b, N)
    return B
end

function tr(r::QadicFieldElem)
    t = coefficient_ring(parent(r))()
    ccall((:qadic_trace, libflint), Nothing, (Ref{PadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}), t, r, parent(r))
    return t
end

function norm(r::QadicFieldElem)
    t = coefficient_ring(parent(r))()
    ccall((:qadic_norm, libflint), Nothing, (Ref{PadicFieldElem}, Ref{QadicFieldElem}, Ref{QadicField}), t, r, parent(r))
    return t
end

function (Rx::Generic.PolyRing{PadicFieldElem})(a::QadicFieldElem)
    Qq = parent(a)
    #@assert Rx === parent(defining_polynomial(Qq))
    R = base_ring(Rx)
    coeffs = Vector{PadicFieldElem}(undef, degree(Qq))
    for i = 1:length(coeffs)
        c = R()
        ccall((:padic_poly_get_coeff_padic, libflint), Nothing,
            (Ref{PadicFieldElem}, Ref{QadicFieldElem}, Int, Ref{QadicField}), c, a, i - 1, parent(a))
        coeffs[i] = c
    end
    return Rx(coeffs)
end

function coeff(x::QadicFieldElem, i::Int)
    R = PadicField(prime(parent(x)))
    c = R()
    ccall((:padic_poly_get_coeff_padic, libflint), Nothing,
        (Ref{PadicFieldElem}, Ref{QadicFieldElem}, Int, Ref{QadicField}), c, x, i, parent(x))
    return c
end

function setcoeff!(x::QadicFieldElem, i::Int, y::PadicFieldElem)
    ccall((:padic_poly_set_coeff_padic, libflint), Nothing,
        (Ref{QadicFieldElem}, Int, Ref{PadicFieldElem}, Ref{QadicField}), x, i, y, parent(x))
end

function setcoeff!(x::QadicFieldElem, i::Int, y::UInt)
    return setcoeff!(x, i, ZZRingElem(y))
end

function setcoeff!(x::QadicFieldElem, i::Int, y::ZZRingElem)
    R = PadicField(prime(parent(x)))
    Y = R(ZZRingElem(y))
    ccall((:padic_poly_set_coeff_padic, libflint), Nothing,
        (Ref{QadicFieldElem}, Int, Ref{PadicFieldElem}, Ref{QadicField}), x, i, Y, parent(x))
end

function coefficient_ring(Q::QadicField)
    return PadicField(prime(Q))
end

function prime(R::PadicField, i::Int)
    p = ZZRingElem()
    ccall((:padic_ctx_pow_ui, libflint), Nothing, (Ref{ZZRingElem}, Int, Ref{PadicField}), p, i, R)
    return p
end

function *(A::ZZMatrix, B::MatElem{PadicFieldElem})
    return matrix(base_ring(B), A) * B
end

^(a::QadicFieldElem, b::QadicFieldElem) = exp(b * log(a))
^(a::PadicFieldElem, b::PadicFieldElem) = exp(b * log(a))

//(a::QadicFieldElem, b::QadicFieldElem) = divexact(a, b)
//(a::PadicFieldElem, b::QadicFieldElem) = divexact(a, b)
//(a::QadicFieldElem, b::PadicFieldElem) = divexact(a, b)

@doc raw"""
    lift(a::PadicFieldElem) -> ZZRingElem

Returns the positive canonical representative in $\mathbb{Z}$. $a$ needs
to be integral.
"""
function lift(a::PadicFieldElem)
    b = ZZRingElem()
    R = parent(a)

    if iszero(a)
        return ZZ(0)
    end
    ccall((:padic_get_fmpz, libflint), Nothing, (Ref{ZZRingElem}, Ref{PadicFieldElem}, Ref{PadicField}), b, a, R)
    return b
end

function Base.setprecision(f::Generic.Poly{PadicFieldElem}, N::Int)
    g = parent(f)()
    fit!(g, length(f))
    for i = 1:length(f)
        g.coeffs[i] = setprecision!(f.coeffs[i], N)
    end
    set_length!(g, normalise(g, length(f)))
    return g
end

function setprecision!(f::Generic.Poly{PadicFieldElem}, N::Int)
    for i = 1:length(f)
        f.coeffs[i] = setprecision!(f.coeffs[i], N)
    end
    return f
end

function rem!(x::AbstractAlgebra.Generic.Poly{T}, y::AbstractAlgebra.Generic.Poly{T}, z::AbstractAlgebra.Generic.Poly{T}) where {T<:Union{PadicFieldElem,QadicFieldElem}}
    x = rem(y, z)
    return x
end

function setprecision!(f::Generic.Poly{QadicFieldElem}, N::Int)
    for i = 1:length(f)
        setprecision!(f.coeffs[i], N)
    end
    set_length!(f, normalise(f, length(f)))
    return f
end

function Base.setprecision(f::Generic.Poly{QadicFieldElem}, N::Int)
    g = map_coefficients(x -> setprecision(x, N), f, parent=parent(f))
    return g
end

function setprecision!(a::PadicFieldElem, n::Int)
    return setprecision(a, n)
end

prime_field(k::PadicField) = k

function gens(k::PadicField, K::PadicField)
    return [k(1)]
end

function norm(f::PolyRingElem{PadicFieldElem})
    return f
end

degree(::PadicField) = 1
