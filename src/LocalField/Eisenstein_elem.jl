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

elem_type(::Type{EisensteinField}) = eisf_elem

@doc Markdown.doc"""
    base_ring(a::EisensteinField)
> Not implemented.
"""
base_ring(a::EisensteinField) = error("Not implemented.")

@doc Markdown.doc"""
    base_ring(a::eisf_elem)
> Not implemented.
"""
base_ring(a::eisf_elem) = error("Not implemented")

# What is this?
# isdomain_type(::Type{eisf_elem}) = true

@doc Markdown.doc"""
    var(a::EisensteinField)
> Returns the identifier (as a symbol, not a string), that is used for printing
> the generator of the given number field.
"""
var(a::EisensteinField) = a.S

function check_parent(a::eisf_elem, b::eisf_elem)
   a.parent != b.parent && error("Incompatible EisensteinField elements")
end

# What is this?
# show_minus_one(::Type{eisf_elem}) = false

###############################################################################
#
#   Basic manipulation
#
###############################################################################


function hash(a::eisf_elem, h::UInt)
    error("Not Implemented")
    return
end

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
    gen(a::EisensteinField)
> Return the generator of the given number field.
"""
function gen(a::EisensteinField)
   r = eisf_elem(a)
   ccall((:eisf_elem_gen, :libantic), Nothing,
         (Ref{eisf_elem}, Ref{EisensteinField}), r, a)
   return r
end

@doc Markdown.doc"""
    one(a::EisensteinField)
> Return the multiplicative identity, i.e. one, in the given number field.
"""
function one(a::EisensteinField)
   r = eisf_elem(a)
   ccall((:eisf_elem_one, :libantic), Nothing,
         (Ref{eisf_elem}, Ref{EisensteinField}), r, a)
   return r
end

@doc Markdown.doc"""
    zero(a::EisensteinField)
> Return the multiplicative identity, i.e. one, in the given number field.
"""
function zero(a::EisensteinField)
   r = eisf_elem(a)
   ccall((:eisf_elem_zero, :libantic), Nothing,
         (Ref{eisf_elem}, Ref{EisensteinField}), r, a)
   return r
end

@doc Markdown.doc"""
    isgen(a::eisf_elem)
> Return `true` if the given number field element is the generator of the
> number field, otherwise return `false`.
"""
function isgen(a::eisf_elem)
   return ccall((:eisf_elem_is_gen, :libantic), Bool,
                (Ref{eisf_elem}, Ref{EisensteinField}), a, a.parent)
end

@doc Markdown.doc"""
    isone(a::eisf_elem)
> Return `true` if the given number field element is the multiplicative
> identity of the number field, i.e. one, otherwise return `false`.
"""
function isone(a::eisf_elem)
   return ccall((:eisf_elem_is_one, :libantic), Bool,
                (Ref{eisf_elem}, Ref{EisensteinField}), a, a.parent)
end

@doc Markdown.doc"""
    iszero(a::eisf_elem)
> Return `true` if the given number field element is the additive
> identity of the number field, i.e. zero, otherwise return `false`.
"""
function iszero(a::eisf_elem)
   return ccall((:eisf_elem_is_zero, :libantic), Bool,
                (Ref{eisf_elem}, Ref{EisensteinField}), a, a.parent)
end

@doc Markdown.doc"""
    isunit(a::eisf_elem)
> Return `true` if the given number field element is invertible, i.e. nonzero,
> otherwise return `false`.
"""
isunit(a::eisf_elem) = !iszero(a)

@doc Markdown.doc"""
    isinteger(a::eisf_elem)
> Return `true` if the given number field element is an integer, otherwise
> return `false`.
"""
function isinteger(a::eisf_elem)
   b = ccall((:eisf_elem_is_integer, :libantic), Cint,
             (Ref{eisf_elem}, Ref{EisensteinField}), a, a.parent)
   return Bool(b)
end

@doc Markdown.doc"""
    isrational(a::eisf_elem)
> Return `true` if the given number field element is a rational number,
> otherwise `false`.
"""
function isrational(a::eisf_elem)
   b = ccall((:eisf_elem_is_rational, :libantic), Cint,
             (Ref{eisf_elem}, Ref{EisensteinField}), a, a.parent)
   return Bool(b)
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

@doc Markdown.doc"""
    degree(a::EisensteinField)
> Return the degree of the given number field, i.e. the degree of its
> defining polynomial.
"""
degree(a::EisensteinField) = a.pol_length-1

@doc Markdown.doc"""
    signature(a::EisensteinField)
> Return the signature of the given number field, i.e. a tuple $r, s$
> consisting of $r$, the number of real embeddings and $s$, half the number of
> complex embeddings.
"""
signature(a::EisensteinField) = signature(a.pol)

function deepcopy_internal(d::eisf_elem, dict::IdDict)
   z = eisf_elem(parent(d), d)
   return z
end

end #if

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
    u = z.u
    return z.res_ring_elt = a.res_ring
    return z
end

### Comment block.
if false

@doc Markdown.doc"""
    (a::EisensteinField)(c::Int)

> Return $c$ as an element in $a$.
"""
function (a::EisensteinField)(c::Int)
   z = eisf_elem(a)
   ccall((:eisf_elem_set_si, :libantic), Nothing,
         (Ref{eisf_elem}, Int, Ref{EisensteinField}), z, c, a)
   return z
end

(a::EisensteinField)(c::Integer) = a(fmpz(c))

function (a::EisensteinField)(c::fmpz)
   z = eisf_elem(a)
   ccall((:eisf_elem_set_fmpz, :libantic), Nothing,
         (Ref{eisf_elem}, Ref{fmpz}, Ref{EisensteinField}), z, c, a)
   return z
end

function (a::EisensteinField)(c::fmpq)
   z = eisf_elem(a)
   ccall((:eisf_elem_set_fmpq, :libantic), Nothing,
         (Ref{eisf_elem}, Ref{fmpq}, Ref{EisensteinField}), z, c, a)
   return z
end

(a::EisensteinField)(c::Rational) = a(fmpq(c))

function (a::EisensteinField)(b::eisf_elem)
   parent(b) != a && error("Cannot coerce element")
   return b
end


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

###############################################################################
#
#   Random generation
#
###############################################################################

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
"""
function EisensteinField(f::fmpq_poly, s::AbstractString;
                         cached::Bool = true, check::Bool = true)
   S = Symbol(s)
   parent_obj = EisensteinField(f, S, cached, check)
   return parent_obj, gen(parent_obj)
end

