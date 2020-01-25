
############################################################################################
#
#   Abstract Types
#
############################################################################################

#abstract type NonArchimedeanLocalField     <: AbstractAlgebra.Field end
#abstract type NonArchimedeanLocalFieldElem <: AbstractAlgebra.FieldElem end

# Alias
#NALocalField     = NonArchimedeanLocalField
#NALocalFieldElem = NonArchimedeanLocalFieldElem


############################################################################################
#
#   EisensteinField
#
############################################################################################

const EisensteinFieldID = Dict{Tuple{FmpqPolyRing, fmpq_poly, Symbol}, Field}()

# TODO: Investigate the type of coefficient field element (whether padic/qadic should be allowed).

# TODO: Should cache the prime and absolute degree for an eisenstein field.
# Coefficients of the defining polynomial are approximate.
# Defining polynomial *can* change precision.
@doc Markdown.doc"""
    EisensteinField{NonArchLocalFieldElem} <: NonArchLocalField

> Type for Eisenstein extensions of local fields. Data fields are
> - base_ring -- The ring of coefficients of the primitive element, which is also a uniformizer.
> - pol       -- Defining polynomial.
> - S         -- Symbol representing the primitive element.
> - data_ring -- Ring storing representatives of the elements. The ring is the ResidueField defined by pol.
> - auxilliary_data -- for that sweet, sweet, Hecke magic.
"""
mutable struct EisensteinField{NonArchLocalFieldElem} <: NonArchLocalField
    
    # Cache inverse of the polynomial.
    #
    #pinv_dinv::Ptr{Nothing}
    #pinv_n::Int
    #pinv_norm::Int
    
    #powers   # Cached powers of the primitive element exceeding the degree.
    
    #traces_coeffs::Ptr{Nothing}  # Chached traces of the basis elements.
    #traces_den::Int
    #traces_alloc::Int
    #traces_length::Int

    base_ring::NonArchLocalField
    pol::PolyElem{NonArchLocalFieldElem}
    S::Symbol
    prec_max::Int # Eisenstein fields are defined by an approximate polynomial, so
                  # element precision will not exceed `prec_max` after a division.
    
    auxilliary_data::Array{Any, 1} # Storage for extensible data.

    ## Temporary to get things off the ground. This may well be a poor choice.
    ## Actually, this has been working fairly well! Just need to be careful with division...
    data_ring::AbstractAlgebra.Generic.ResField{<:AbstractAlgebra.Generic.Poly{<:NALocalFieldElem}}
    
    function EisensteinField(pol::AbstractAlgebra.Generic.Poly{T}, s::Symbol,
                             cached::Bool = false, check::Bool = true) where T<:NALocalFieldElem

        check && !is_eisenstein(pol) && error("Polynomial must be eisenstein over base ring.")

        if cached && haskey(EisensteinFieldID, (parent(pol), pol, s))
            return EisensteinFieldID[parent(pol), pol, s]::EisensteinField
        end
                     
        eisf = new{T}()
        eisf.pol = pol
        eisf.base_ring = base_ring(pol)
        eisf.S = s
        eisf.prec_max = precision(eisf.base_ring)
        
        # Construct a new parent to actually print a generator nicely.
        P,Pvar = PolynomialRing(base_ring(pol), string(s))
        eisf.data_ring = ResidueField(P, pol(Pvar), cached=cached)

        # Construct the generator
        g = eisf_elem(eisf)
        g.data_ring_elt = gen(eisf.data_ring)

        eisf.auxilliary_data = Array{Any}(undef, 5)
        if cached
            EisensteinFieldID[parent(pol), pol, s] = eisf
        end
        return eisf, g
   end
end


@doc Markdown.doc"""
    eisf_elem <: NALocalFieldElem

> Element type for an EisensteinField. Data fields are:
> - parent        -- The EisensteinField to which the element belongs.
> - data_ring_elt -- The representative in the data ring.
"""
mutable struct eisf_elem <: NALocalFieldElem

    # Cached data (unclear if these should be updated after every arithmetic operation.)
    #u::eisf_unit_internal
    #v::Integer
    #N::Integer
    
    data_ring_elt::AbstractAlgebra.Generic.ResF{<:AbstractAlgebra.Generic.Poly{<:NALocalFieldElem}}
    parent::EisensteinField

    function eisf_elem(p::EisensteinField)
        r = new()
        r.parent = p
        return r
    end

    function eisf_elem(p::EisensteinField, a::eisf_elem)
        r = new()
        r.parent = p
        r.data_ring_elt = deepcopy(a.data_ring_elt)
        return r
    end
end


### The TODO list ###
#=
1. Representation of elements (We might need a `u*pi^a*p^b` representation).
   Or, we could just do full pi-adic expansions. (I feel like this is mostly insane.)

2. Internal structure (as a residue ring, or as something more specific?)

3. Element constructors.


=#
