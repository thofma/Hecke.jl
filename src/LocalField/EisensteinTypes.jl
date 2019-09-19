

## Doing things with Eisenstein extensions.

const EisensteinFieldID = Dict{Tuple{FmpqPolyRing, fmpq_poly, Symbol}, Field}()

# TODO: Investigate the type of coefficient field element (whether padic/qadic should be allowed).

# Coefficients of the defining polynomial are approximate.
# Defining polynomial *can* change precision.

mutable struct EisensteinField{padic} <: AbstractAlgebra.Field
    
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

    pol
    S::Symbol
    auxilliary_data::Array{Any, 1} # Storage for extensible data.

    res_ring ## Temporary to get things off the ground. This may well be a poor choice.
    
    function EisensteinField(pol::AbstractAlgebra.Generic.Poly{padic}, s::Symbol,
                                  cached::Bool = false, check::Bool = false)
        check && error("Irreducibility check not implemented") &&
            !isirreducible(pol) && error("Polynomial must be irreducible")

        if cached && haskey(EisensteinFieldID, (parent(pol), pol, s))
            return EisensteinFieldID[parent(pol), pol, s]::EisensteinField
        end
                     
        eisf = new{padic}()
        eisf.pol = pol        
        eisf.S = s
        eisf.res_ring = ResidueRing(parent(pol), pol)
        
        #nf.auxilliary_data = Array{Any}(undef, 5)
        if cached
            EisensteinFieldID[parent(pol), pol, s] = eisf
        end
        return eisf
   end
end


# Internal structure of elements could be a residue ring class.
# (Perhaps better is to have an internal polynomial representation, and do the reductions myself.)

mutable struct eisf_unit_internal <: FieldElem
    
    elem_coeffs
    res_ring_elt     # Very likely we will need to implement operations from scratch.
    debug_parent::EisensteinField # This should be removed eventually.
end

mutable struct eisf_elem <: FieldElem
    u::eisf_unit_internal
    v::Integer
    N::Integer
    res_ring_elt
    parent::EisensteinField

    function eisf_elem(p::EisensteinField)
        r = new()
        r.parent = p
        return r
    end

    function eisf_elem(p::EisensteinField, a::eisf_elem)
        r = new()
        r.parent = p
        r.res_ring_elt = deepcopy(a.res_ring_elt)
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
