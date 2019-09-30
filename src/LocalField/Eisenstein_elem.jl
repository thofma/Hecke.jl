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
    base_ring(a::EisensteinField)
> Not implemented.
"""
base_ring(a::EisensteinField) = a.base_ring

@doc Markdown.doc"""
    base_ring(a::eisf_elem)
> Not implemented.
"""
base_ring(a::eisf_elem) = a.base_ring

isdomain_type(::Type{eisf_elem}) = true

isexact_type(::Type{eisf_elem}) = false

@doc Markdown.doc"""
    var(a::EisensteinField)
> Returns the identifier (as a symbol, not a string), that is used for printing
> the generator of the given number field.
"""
var(a::EisensteinField) = a.S

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
    r.res_ring_elt = deepcopy(a.res_ring_elt)
    return r
end

@doc Markdown.doc"""
    gen(a::EisensteinField)
> Return the generator of the given EisensteinField.
"""
function gen(a::EisensteinField)
    r = eisf_elem(a)
    r.res_ring_elt = gen(a.res_ring)
   return r
end



@doc Markdown.doc"""
    one(a::EisensteinField)
> Return the multiplicative identity, i.e. one, in the given number field.
"""
function one(a::EisensteinField)
    return a(1)
end

@doc Markdown.doc"""
    zero(a::EisensteinField)
> Return the multiplicative identity, i.e. one, in the given number field.
"""
function zero(a::EisensteinField)
    return a(0)
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


function deepcopy_internal(d::eisf_elem, dict::IdDict)
   z = eisf_elem(parent(d), d)
   return z
end

end #if

@doc Markdown.doc"""
    degree(a::EisensteinField)
> Return the degree of the given number field, i.e. the degree of its
> defining polynomial.
"""
degree(a::EisensteinField) = degree(a.pol)

# By our definition, the generator of a field of eisenstein type is the uniformizer.
uniformizer(a::EisensteinField) = gen(a)


###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function show(io::IO, a::EisensteinField{T}) where T
   print(io, "Eisenstein extension over local field of type $T")
   print(io, " with defining polynomial ", a.pol)
end

function show(io::IO, x::eisf_elem)
   print(io, x.res_ring_elt)
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
    b = a.parent(a)
    b.res_ring_elt = -a.res_ring_elt
    return b
end

function valuation(a::eisf_elem)
    coeffs = coefficients(a.res_ring_elt.data)

    min = valuation(coeffs[0])
    for i = 1:length(coeffs)-1
        newv = valuation(coeffs[i]) + (i)//degree(a.parent.pol)
        if newv < min
            min = newv
        end
    end
    return min
end

function residue_image(a::padic)
    Fp = ResidueRing(FlintZZ,parent(a).p)
    return Fp(lift(a))
end


function residue_image(a::eisf_elem)
    coeffs = coefficients(a.res_ring_elt.data)
    
    for i = 0:length(coeffs)-1
        newv = valuation(coeffs[i]) + (i)//degree(a.parent.pol)
        if newv < 0
            error("Valuation of input is negative.")
        end
    end
    return residue_image(coeffs[0])
end

inv(a::eisf_elem) = one(parent(a))//a

###############################################################################
#
#   Binary operators
#
###############################################################################

function +(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    r = a.parent()
    r.res_ring_elt = a.res_ring_elt + b.res_ring_elt
    return r
end

function -(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    r = a.parent()
    r.res_ring_elt = a.res_ring_elt - b.res_ring_elt
    return r
end

function *(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    r = a.parent()
    r.res_ring_elt = a.res_ring_elt * b.res_ring_elt
    return r
end

function divexact(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    r = a.parent()
    r.res_ring_elt = a.res_ring_elt // b.res_ring_elt
    return r
end

/(a::eisf_elem, b::eisf_elem) = divexact(a,b)

###############################################################################
#
#   Ad hoc binary operators
#
###############################################################################

function +(a::eisf_elem, b::Union{Int,fmpz,fmpq,padic})
   r = a.parent()
   r.res_ring_elt = a.res_ring_elt + b
   return r
end

function -(a::eisf_elem, b::Union{Int,fmpz,fmpq,padic})
   r = a.parent()
   r.res_ring_elt = a.res_ring_elt - b
   return r
end

function -(a::Union{Int,fmpz,fmpq,padic}, b::eisf_elem)
   r = b.parent()
   r.res_ring_elt = a - b.res_ring_elt
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

function *(a::eisf_elem, b::Union{Int,fmpz,fmpq,padic})
    r = a.parent()
    r.res_ring_elt = a.res_ring_elt*b
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


function /(a::eisf_elem, b::Union{Int,fmpz,fmpq,padic})
    r = a.parent()
    r.res_ring_elt = a.res_ring_elt*b
    return r
end

###
if false
//(a::eisf_elem, b::Int) = divexact(a, b)

//(a::eisf_elem, b::fmpz) = divexact(a, b)

//(a::eisf_elem, b::Integer) = a//fmpz(b)

//(a::eisf_elem, b::fmpq) = divexact(a, b)

//(a::Integer, b::eisf_elem) = divexact(a, b)

//(a::fmpz, b::eisf_elem) = divexact(a, b)

//(a::fmpq, b::eisf_elem) = divexact(a, b)

//(a::Rational, b::eisf_elem) = divexact(fmpq(a), b)

//(a::eisf_elem, b::Rational) = divexact(a, fmpq(b))

end # if

###############################################################################
#
#   Powering
#
###############################################################################

function ^(a::eisf_elem, n::Int)
    r = a.parent()
    r.res_ring_elt = a.res_ring_elt^n
   return r
end

###############################################################################
#
#   Comparison
#
###############################################################################

function ==(a::eisf_elem, b::eisf_elem)
    check_parent(a, b)
    return a.res_ring_elt == b.res_ring_elt
end

################################################################################
#
#  Unsafe operations
#
################################################################################

@inline function add!(z::eisf_elem, x::eisf_elem, y::eisf_elem)
  add!(z.res_ring_elt, x.res_ring_elt, y.res_ring_elt)
  return z
end

@inline function sub!(z::eisf_elem, x::eisf_elem, y::eisf_elem)
  sub!(z.res_ring_elt, x.res_ring_elt, y.res_ring_elt)
  return z
end

@inline function mul!(z::eisf_elem, x::eisf_elem, y::eisf_elem)
  mul!(z.res_ring_elt, x.res_ring_elt, y.res_ring_elt)
  return z
end

function addeq!(z::eisf_elem, x::eisf_elem)
  addeq!(z.res_ring_elt, x.res_ring_elt)
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
    z.res_ring_elt = a.res_ring()
    return z
end

function (a::EisensteinField)(b::eisf_elem)
   parent(b) != a && error("Cannot coerce element")
   return b
end

function (a::EisensteinField)(b::padic)
    parent(b) != base_ring(a) && error("Cannot coerce element")
    r = eisf_elem(a)
    r.res_ring_elt = a.res_ring(b)
   return r
end


@doc Markdown.doc"""
    (a::EisensteinField)(c::Int)

> Return $c$ as an element in $a$.
"""
# function (a::EisensteinField)(c::Int)
#     z = eisf_elem(a)
#     z.res_ring_elt = a.res_ring(c)
#     return z
# end

function (a::EisensteinField)(c::fmpz)
    z = eisf_elem(a)
    z.res_ring_elt = a.res_ring(c)
    return z
end

(a::EisensteinField)(c::Integer) = a(fmpz(c))

### Comment block.
if false



function (a::EisensteinField)(c::fmpq)
   z = eisf_elem(a)
   ccall((:eisf_elem_set_fmpq, :libantic), Nothing,
         (Ref{eisf_elem}, Ref{fmpq}, Ref{EisensteinField}), z, c, a)
   return z
end

(a::EisensteinField)(c::Rational) = a(fmpq(c))



# Debatable if we actually want this functionality...
function (a::EisensteinField)(pol::fmpq_poly)
   pol = parent(a.pol)(pol) # check pol has correct parent
   z = eisf_elem(a)
   if length(pol) >= length(a.pol)
      pol = mod(pol, a.pol)
   end
   ccall((:eisf_elem_set_fmpq_poly, :libantic), Nothing,
         (Ref{eisf_elem}, Ref{fmpq_poly}, Ref{EisensteinField}), z, pol, a)
   return z
end

function (a::FmpqPolyRing)(b::eisf_elem)
   parent(parent(b).pol) != a && error("Cannot coerce from field to polynomial ring")
   r = a()
   ccall((:eisf_elem_get_fmpq_poly, :libantic), Nothing,
         (Ref{fmpq_poly}, Ref{eisf_elem}, Ref{EisensteinField}), r, b, parent(b))
   return r
end

end #if
    
###############################################################################
#
#   Random generation
#
###############################################################################

if false
    
function rand(K::EisensteinField, r::UnitRange{Int64})
   R = parent(K.pol)
   n = degree(K.pol)
   return K(rand(R, (n-1):(n-1), r)) 
end

end #if
    
###############################################################################
#
#   EisensteinField constructor
#
###############################################################################

@doc Markdown.doc"""
    EisenteinField(f::fmpq_poly, s::AbstractString; cached::Bool = true, check::Bool = true)
> Return a tuple $R, x$ consisting of the parent object $R$ and generator $x$
> of the local field $\mathbb{Q}_p/(f)$ where $f$ is the supplied polynomial.
> The supplied string `s` specifies how the generator of the field extension
> should be printed.

> WARNING: Defaults are actually cached::Bool = false, check::Bool = false
"""
function EisensteinField(f::AbstractAlgebra.Generic.Poly{<:NALocalFieldElem}, s::AbstractString;
                         cached::Bool = false, check::Bool = true)
   S = Symbol(s)
   parent_obj = EisensteinField(f, S, cached, check)
   return parent_obj, gen(parent_obj)
end

