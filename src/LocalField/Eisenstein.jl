

#export

################################################################################
#
#  Basic interface
#
################################################################################

@doc Markdown.doc"""
    var(a::EisensteinField)
> Returns the identifier (as a symbol, not a string), that is used for printing
> the generator of the given Eisenstein field.
"""
var(a::EisensteinField) = a.S

@doc Markdown.doc"""
    gen(a::EisensteinField)
> Return the generator of the given EisensteinField.
"""
function gen(a::EisensteinField)
    r = eisf_elem(a)
    r.data_ring_elt = gen(a.data_ring)
   return r
end

@doc Markdown.doc"""
    one(a::EisensteinField)
> Return the multiplicative identity, i.e. one, in the given Eisenstein field.
"""
function one(a::EisensteinField)
    return a(1)
end

@doc Markdown.doc"""
    zero(a::EisensteinField)
> Return the multiplicative identity, i.e. one, in the given Eisenstein field.
"""
function zero(a::EisensteinField)
    return a(0)
end

################################################################################
#
#  Base field, basic base field functions, and uniformizer
#
################################################################################

@doc Markdown.doc"""
    base_ring(a::EisensteinField)
> Returns the base ring of `a`.
"""
base_ring(a::EisensteinField) = a.base_ring

@doc Markdown.doc"""
    base_field(a::EisensteinField)
> Returns the base ring of `a`.
"""
base_field(a::EisensteinField) = base_ring(a)


# TODO: Decide whether this is a "relative" or absolute method.
@doc Markdown.doc"""
    degree(a::EisensteinField)
> Return the degree of the given Eisenstein field over it's base. i.e. the degree of its
> defining polynomial.
"""
degree(a::EisensteinField) = degree(a.pol)

@doc Markdown.doc"""
    absolute_degree(a::NALocalField)
> Return the absolute degree of the given Eisenstein field over the ground padic field.
"""
absolute_degree(a::PadicField) = 1
absolute_degree(a::QadicField) = degree(a)

function absolute_degree(a::NALocalField)
    return degree(a)*absolute_degree(base_ring(a))
end
    
# By our definition, the generator of a field of eisenstein type is the uniformizer.
uniformizer(a::EisensteinField) = gen(a)

@doc Markdown.doc"""
    basis(K::EisensteinField) -> Array{eisf_elem,1}

Returns a basis for $K$ over its base ring.
"""
function basis(K::EisensteinField)
    n = degree(K)
    g = gen(K);
    d = Array{typeof(g)}(undef, n)
    b = K(1)
    for i = 1:n-1
        d[i] = b
        b *= g
    end
    d[n] = b
    return d
end


################################################################################
#
#  Predicates
#
################################################################################

issimple(::Type{EisensteinField}) = true

issimple(::EisensteinField) = true


###############################################################################
#
#   AbstractString I/O
#
###############################################################################

function show(io::IO, a::EisensteinField{T}) where T
   print(io, "Eisenstein extension over local field of type $T")
   print(io, " with defining polynomial ", a.pol)
end

################################################################################
#
#  Field constructions
#
################################################################################

@doc Markdown.doc"""
    EisenteinField(f::AbstractAlgebra.Generic.Poly{<:NALocalFieldElem}, 
                   s::AbstractString; cached::Bool = true, check::Bool = true)
> Return a tuple $R, x$ consisting of the parent object $R$ and generator $x$
> of the local field $\mathbb{Q}_p/(f)$ where $f$ is the supplied polynomial.
> The supplied string `s` specifies how the generator of the field extension
> should be printed.

> WARNING: Defaults are actually cached::Bool = false, check::Bool = true
"""
function EisensteinField(f::AbstractAlgebra.Generic.Poly{<:NALocalFieldElem},
                         s::AbstractString;
                         cached::Bool = false, check::Bool = true)
    return EisensteinField(f, Symbol(s), cached, check)
end


################################################################################
#
#  Characteristic
#
################################################################################

characteristic(::EisensteinField) = 0

################################################################################
#
#  Class group
#
################################################################################

@doc Markdown.doc"""
    class_group(K::EisensteinField) -> GrpAbFinGen, Map

Returns the class group as an abelian group and a map from this group to the set
of ideals of the maximal order. 

NOTE: This function is not implemented.
"""
function class_group(K::EisensteinField)
  error("Not implemented.")
end

################################################################################
#
#  Residue Field
#
################################################################################

function ResidueField(K::EisensteinField)
    k, mp_struct = ResidueField(base_ring(K))

    # Unpack the map structure to get the maps to/from the residue field.
    base_res  = mp_struct.f
    base_lift = mp_struct.g

    T = elem_type(k)
    
    _residue = function(x::eisf_elem)
        v = valuation(x)
        v < 0 && error("element $x is not integral.")
        return base_res(coeff(x,0))
    end

    #TODO: See if the residue field elem type can be declared dynamically.
    function _lift(x)
        return K(base_lift(x))
    end
    
    return k, MapFromFunc(_residue, _lift, K, k)
end

