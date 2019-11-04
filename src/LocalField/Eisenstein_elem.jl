###############################################################################
#
#   Type and parent object methods
#
###############################################################################

parent_type(::Type{eisf_elem}) = EisensteinField

@doc Markdown.doc"""
    parent(a::eisf_elem)
> Return the parent of the given number field element.
"""
parent(a::eisf_elem) = a.parent

elem_type(::Type{EisensteinField{T}}) where T = eisf_elem

@doc Markdown.doc"""
    base_ring(a::eisf_elem)
> Returns the base ring of the parent of `a`.
"""
base_ring(a::eisf_elem) = a.base_ring

@doc Markdown.doc"""
    base_field(a::eisf_elem)
> Returns the base ring of the parent of `a`.
"""
base_field(a::eisf_elem) = base_ring(a)

isdomain_type(::Type{eisf_elem}) = true

isexact_type(::Type{eisf_elem}) = false

function check_parent(a::eisf_elem, b::eisf_elem)
   a.parent != b.parent && error("Incompatible EisensteinField elements")
end

###############################################################################
#
#   Basic manipulation
#
###############################################################################


function hash(a::eisf_elem, h::UInt)
    error("Not Implemented")
    return
end

function deepcopy(a::eisf_elem)
    r = parent(a)()
    r.data_ring_elt = deepcopy(a.data_ring_elt)
    return r
end

#TODO: UNSAFE ZERO SHOULD NOT RETURN AN ELEMENT. The fix should occur in AbstractAlgebra.
#TODO: Make this more efficient.
function zero!(a::eisf_elem)
    a.data_ring_elt = zero(parent(a)).data_ring_elt
    a
end


# @doc Markdown.doc"""
#     isgen(a::eisf_elem)
# > Return `true` if the given number field element is the generator of the
# > number field, otherwise return `false`.
# """
# function isgen(a::eisf_elem)
#    return ccall((:eisf_elem_is_gen, :libantic), Bool,
#                 (Ref{eisf_elem}, Ref{EisensteinField}), a, a.parent)
# end

@doc Markdown.doc"""
    isone(a::eisf_elem)
> Return `true` if the given number field element is the multiplicative
> identity of the number field, i.e. one, otherwise return `false`.
"""
function isone(a::eisf_elem)
   return a == parent(a)(1)
end

@doc Markdown.doc"""
    iszero(a::eisf_elem)
> Return `true` if the given number field element is the additive
> identity of the number field, i.e. zero, otherwise return `false`.
"""
function iszero(a::eisf_elem)
   return a == parent(a)(0)
end

@doc Markdown.doc"""
    isunit(a::eisf_elem)
> Return `true` if the given number field element is invertible, i.e. nonzero,
> otherwise return `false`.
"""
isunit(a::eisf_elem) = !iszero(a)


@doc Markdown.doc"""
    precision(a::eisf_elem)
Return the minimum precision of the coefficients of `a`.
"""
function precision(a::eisf_elem)
    return minimum(precision.(coefficients(a)))
end


#######################################################
if false

@doc Markdown.doc"""
    coeff(x::eisf_elem, n::Int)
> Return the $n$-th coefficient of the polynomial representation of the given
> number field element. Coefficients are numbered from $0$, starting with the
> constant coefficient.
"""
function coeff(x::eisf_elem, n::Int)
   n < 0 && throw(DomainError("Index must be non-negative: $n"))
   z = fmpq()
   ccall((:eisf_elem_get_coeff_fmpq, :libantic), Nothing,
     (Ref{fmpq}, Ref{eisf_elem}, Int, Ref{EisensteinField}), z, x, n, parent(x))
   return z
end

function num_coeff!(z::fmpz, x::eisf_elem, n::Int)
   n < 0 && throw(DomainError("Index must be non-negative: $n"))
   ccall((:eisf_elem_get_coeff_fmpz, :libantic), Nothing,
     (Ref{fmpz}, Ref{eisf_elem}, Int, Ref{EisensteinField}), z, x, n, parent(x))
   return z
end

@doc Markdown.doc"""
    denominator(a::eisf_elem)
> Return the denominator of the polynomial representation of the given number
> field element.
"""
function denominator(a::eisf_elem)
   z = fmpz()
   ccall((:eisf_elem_get_den, :libantic), Nothing,
         (Ref{fmpz}, Ref{eisf_elem}, Ref{EisensteinField}),
         z, a, a.parent)
   return z
end

function elem_from_mat_row(a::EisensteinField, b::fmpz_mat, i::Int, d::fmpz)
   Generic._checkbounds(nrows(b), i) || throw(BoundsError())
   ncols(b) == degree(a) || error("Wrong number of columns")
   z = a()
   ccall((:eisf_elem_set_fmpz_mat_row, :libantic), Nothing,
        (Ref{eisf_elem}, Ref{fmpz_mat}, Int, Ref{fmpz}, Ref{EisensteinField}),
        z, b, i - 1, d, a)
   return z
end

function elem_to_mat_row!(a::fmpz_mat, i::Int, d::fmpz, b::eisf_elem)
   ccall((:eisf_elem_get_fmpz_mat_row, :libantic), Nothing,
         (Ref{fmpz_mat}, Int, Ref{fmpz}, Ref{eisf_elem}, Ref{EisensteinField}),
         a, i - 1, d, b, b.parent)
   nothing
 end


end #if


###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function show(io::IO, x::eisf_elem)
   print(io, x.data_ring_elt)
end

needs_parentheses(::eisf_elem) = true

displayed_with_minus_in_front(::eisf_elem) = false

show_minus_one(::Type{eisf_elem}) = true

canonical_unit(x::eisf_elem) = x

###############################################################################
#
#   Unary operators
#
###############################################################################

function -(a::eisf_elem)
    b = deepcopy(a)
    b.data_ring_elt = -a.data_ring_elt
    return b
end

function valuation(a::eisf_elem)
    coeffs = coefficients(a)

    min = valuation(coeffs[0])
    for i = 1:length(coeffs)-1
        newv = valuation(coeffs[i]) + (i)//absolute_degree(parent(a))
        if newv < min
            min = newv
        end
    end
    return min
end

#TODO: Replace `inv` with a Hensel lifting version.
inv(a::eisf_elem) = one(parent(a))//a


################################################################################
#
#  Lifting and residue fields
#
################################################################################


function lift(x::FinFieldElem, K::EisensteinField)
    return K(lift(x, base_ring(K)))
end


# function residue_image(a::padic)
#     Fp = ResidueRing(FlintZZ,parent(a).p)
#     return Fp(lift(a))
# end

# function residue_image(a::qadic)
#     display("WARNING!!!! Lazy testing code, assumes that the residue field is given "*
#             "by a Conway polynomial.")

#     Qq = parent(a)
#     R,x = PolynomialRing(FlintZZ,"x")

#     Fp = FlintFiniteField(prime(Qq))
#     Fq = FlintFiniteField(prime(Qq), degree(Qq), "b")[1]
#     return Fq(change_base_ring(lift(R,a),Fp))
# end

# function residue_image(a::eisf_elem)
#     coeffs = coefficients(a.data_ring_elt.data)
    
#     for i = 0:length(coeffs)-1
#         newv = valuation(coeffs[i]) + (i)//degree(a.parent.pol)
#         if newv < 0
#             error("Valuation of input is negative.")
#         end
#     end
#     return residue_image(coeffs[0])
# end

###############################################################################
#
#   Coefficients
#
###############################################################################

coefficients(a::eisf_elem) = coefficients(a.data_ring_elt.data)

coeffs(a::eisf_elem) = coefficients(a)

coeff(a::eisf_elem, i::Int) = coeff(a.data_ring_elt.data, i)

function setcoeff!(a::eisf_elem, i::Int64, c::NALocalFieldElem)
    setcoeff!(a.data_ring_elt.data, i, c)
end

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    r = a.parent()
    r.data_ring_elt = a.data_ring_elt + b.data_ring_elt
    return r
end

function -(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    r = a.parent()
    r.data_ring_elt = a.data_ring_elt - b.data_ring_elt
    return r
end

function *(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    r = a.parent()
    r.data_ring_elt = a.data_ring_elt * b.data_ring_elt
    return r
end

function /(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    r = a.parent()
    r.data_ring_elt = a.data_ring_elt // b.data_ring_elt
    return r
end

divexact(a::eisf_elem, b::eisf_elem) = a/b

###############################################################################
#
#   Ad hoc binary operators
#
###############################################################################

function +(a::eisf_elem, b::Union{Int,fmpz,fmpq,FlintLocalFieldElem})
   r = a.parent()
   r.data_ring_elt = a.data_ring_elt + b
   return r
end

function -(a::eisf_elem, b::Union{Int,fmpz,fmpq,FlintLocalFieldElem})
   r = a.parent()
   r.data_ring_elt = a.data_ring_elt - b
   return r
end

function -(a::Union{Int,fmpz,fmpq,FlintLocalFieldElem}, b::eisf_elem)
   r = b.parent()
   r.data_ring_elt = a - b.data_ring_elt
   return r
end

+(a::eisf_elem, b::Integer) = a + fmpz(b)

-(a::eisf_elem, b::Integer) = a - fmpz(b)

-(a::Integer, b::eisf_elem) = fmpz(a) - b

+(a::Integer, b::eisf_elem) = b + a

+(a::fmpq, b::eisf_elem) = b + a

+(a::Rational, b::eisf_elem) = fmpq(a) + b

+(a::eisf_elem, b::Rational) = b + a

-(a::Rational, b::eisf_elem) = fmpq(a) - b

-(a::eisf_elem, b::Rational) = a - fmpq(b)

function *(a::eisf_elem, b::Union{Int,fmpz,fmpq,FlintLocalFieldElem})
    r = a.parent()
    r.data_ring_elt = a.data_ring_elt*b
    return r
end

function *(a::Rational, b::eisf_elem)
  return fmpq(a) * b
end

*(a::eisf_elem, b::Rational) = b * a

*(a::eisf_elem, b::Integer) = a * fmpz(b)

*(a::Integer, b::eisf_elem) = b * a

*(a::fmpz, b::eisf_elem) = b * a

*(a::fmpq, b::eisf_elem) = b * a


function /(a::eisf_elem, b::Union{Int,fmpz,fmpq,FlintLocalFieldElem})
    r = a.parent()
    r.data_ring_elt = a.data_ring_elt/b
    return r
end

//(a::eisf_elem, b::Int) = a / parent(a)(b)

//(a::eisf_elem, b::fmpz) = a / parent(a)(b)

//(a::eisf_elem, b::Integer) = a // parent(a)(fmpz(b))

//(a::eisf_elem, b::fmpq) = a / parent(a)(b)

//(a::Integer, b::eisf_elem) = parent(b)(a) / b

//(a::fmpz, b::eisf_elem) = parent(b)(a) / b

//(a::fmpq, b::eisf_elem) = parent(b)(a) / b

//(a::Rational, b::eisf_elem) = parent(b)(fmpq(a)) / b

//(a::eisf_elem, b::Rational) = a / parent(a)(fmpq(b))

###############################################################################
#
#   Powering
#
###############################################################################

function ^(a::eisf_elem, n::Int)
    r = a.parent()
    r.data_ring_elt = a.data_ring_elt^n
   return r
end

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    return a.data_ring_elt == b.data_ring_elt
end

################################################################################
#
#  Unsafe operations
#
################################################################################

@inline function add!(z::eisf_elem, x::eisf_elem, y::eisf_elem)
  add!(z.data_ring_elt, x.data_ring_elt, y.data_ring_elt)
  return z
end

@inline function sub!(z::eisf_elem, x::eisf_elem, y::eisf_elem)
  sub!(z.data_ring_elt, x.data_ring_elt, y.data_ring_elt)
  return z
end

@inline function mul!(z::eisf_elem, x::eisf_elem, y::eisf_elem)
  mul!(z.data_ring_elt, x.data_ring_elt, y.data_ring_elt)
  return z
end

function addeq!(z::eisf_elem, x::eisf_elem)
  addeq!(z.data_ring_elt, x.data_ring_elt)
  return z
end


###############################################################################
#
#   Parent object call overloads
#
###############################################################################

@doc Markdown.doc"""
    (a::EisensteinField)()

> Return an empty (0) element.    
"""
function (a::EisensteinField)()
    z = eisf_elem(a)
    #u = z.u
    z.data_ring_elt = a.data_ring()
    return z
end


###############################################################################
#
#    Coercion logic
#
###############################################################################

"""
    The logic here enables coercion to go up/down a tower
    with no fear of infinite recursion. At the start, 
    we calculate the absolute degree of the element and the
    target field. Comparing these, we then know whether we
    need to pull the element up the tower or move it down
    the tower of it's parent.

    Since the base of a tower is always a Flint type, one of
    the specialized methods will catch the recursion call, and
    succeed or fail accordingly.

    NOTE: NALocalFields must have an `absolute_degree` method.
"""

function check_coercion_compatible(K::NALocalField, L::NALocalField)
    characteristic(K) != characteristic(L) && error("Cannot coerce element. Characteristics do not agree.")
    prime(K) != prime(L) && error("Cannot coerce element. Topologies do not agree.")
    return true
end

function (a::EisensteinField)(b::NALocalFieldElem)
    parent(b) == a && return b
    K = a
    L = parent(b)
    check_coercion_compatible(K, L)

    dK = absolute_degree(K)
    dL = absolute_degree(L)

    if dK > dL
        return coerce_up(a,b)
    elseif dK < dL
        return coerce_down(a,b)
    end
    error("Cannot coerce element.")        
end

function coerce_up(a::NALocalField, b::NALocalFieldElem)
    if parent(b) == base_ring(a)
        r = eisf_elem(a)
        r.data_ring_elt = a.data_ring(b)
        return r
    end
    return coerce_up(a, coerce_up(base_ring(a),b))
end

function coerce_up(a::FlintLocalField, b::eisf_elem)
    error("Cannot coerce element.")
end

# We add a redundant characteristic check just to be safe. We anticipate the addition
# of the FLINT function fields eventually. We advise the user not to call this method directly.
function coerce_up(a::FlintLocalField, b::FlintLocalFieldElem)
    characteristic(a) != characteristic(parent(b)) && error("Cannot coerce element. Characteristics do not agree.")
    
    if typeof(a) == FlintPadicField && typeof(parent(b)) == FlintQadicField
        error("Cannot coerce element.")
    else
        return a(b)
    end
end

function coerce_down(a::NALocalField, b::NALocalFieldElem)
    K = parent(b)
    
    for j=1:degree(K)-1
        !iszero(coeff(b,j)) && error("Cannot coerce element.")
    end
    
    L  = base_ring(K)
    b0 = coeff(b,0)
    
    # If the parents agree, return.    
    if L == a
        @assert parent(b0) == L
        return deepcopy(b0)
    else
        return coerce_down(a, b0)
    end
end

function coerce_down(a::NALocalField, b::FlintLocalFieldElem)
    error("Cannot coerce element.")
end

function coerce_down(a::FlintLocalField, b::FlintLocalFieldElem)
    return a(b)
end

######
# Ad hoc coercions (Needed as methods cannot be added to abstract types.)

function (a::FlintPadicField)(b::qadic)
    # TODO: add various asserts? Asserts in Qp() might catch errors already.
    return a(coeff(b,0))
end

function (a::FlintPadicField)(b::eisf_elem)
    parent(b) == a && return b
    K = a
    L = parent(b)
    check_coercion_compatible(K, L)
    return coerce_down(a,b)
end

function (a::FlintQadicField)(b::eisf_elem)
    parent(b) == a && return b
    K = a
    L = parent(b)
    check_coercion_compatible(K, L)
    return coerce_down(a,b)
end


function (a::EisensteinField)(c::fmpz)
    z = eisf_elem(a)
    z.data_ring_elt = a.data_ring(c)
    return z
end

function (a::EisensteinField)(c::fmpq)
    z = eisf_elem(a)
    z.data_ring_elt = a.data_ring(c)
    return z
end

(a::EisensteinField)(c::Integer) = a(fmpz(c))

(a::EisensteinField)(c::Rational) = a(fmpq(c))

    
###############################################################################
#
#   Random generation
#
###############################################################################

@doc Markdown.doc"""
    rand(K::NALocalField)
Return a random element of the non-archimedean Local Field ``K``, according to the distribution:
``a_{n-1} \pi^{n-1} + \ldots + a_0``, 
with each ``a_i`` the i.i.d standard distributions on the base field. 
"""
function rand(K::NALocalField)
    pi = gen(K)
    B  = base_ring(K)
    n  = degree(K)
   return sum(K(rand(B))*pi^j for j=0:n-1)
end
