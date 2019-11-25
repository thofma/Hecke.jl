
#########################################################################################
#
#   Local regulators
#
#########################################################################################


function log_conjugates_matrix(u::Array{T, 1}, p, prec::Int = 10) where T
    k = parent(u[1])
    
    emb_classes = map(x->embedding_classes(x,p,prec), u)
    if any(length(ec) > 1 for ec in emb_classes)
        error("Function still in development. The present issue is a lack of `compositum` method.")
    end    
    log_embeddings = map(x->iwasawa_log(x[1]), emb_classes) # Should be adapted in general.

    @info "" log_embeddings

    # TODO: One needs to construct a common embedding into Cp of the various embeddings,
    #       before the conjugates can be properly computed.
    
    log_conjugates = map(x->galois_orbit.(x), log_embeddings)

    @info (log_conjugates)
    
    return matrix(log_conjugates)
end

function log_conjugates_matrix(K::AnticNumberField, p, prec::Int = 10)  
    # u, mu = unit_group_fac_elem(R)
    u, mu = unit_group(maximal_order(K)) # Not optimal, but good enough.
    return log_conjugates_matrix([K(mu(u[i])) for i=2:ngens(u)], p, prec)
end

function log_conjugates_matrix(R::NfAbsOrd, p, prec::Int = 10)    
    return log_conjugates_matrix(number_field(R), p, prec)    
end


@doc Markdown.doc"""
    regulator_iwasawa(K::AnticNumberField, C::qAdicConj, n::Int = 10) -> qadic
    regulator_iwasawa(R::NfAbsOrd, C::qAdicConj, n::Int = 10) -> qadic

For a totally real field $K$, the regulator as defined by Iwasawa: the determinant of the
matrix containing the logarithms of the conjugates, supplemented by a column containing all $1$.

The p-adic regulator is not well-defined in many cases.
"""
function regulator_iwasawa(u::Array{T, 1}, p, prec::Int = 10) where T

    k = parent(u[1])
    #@assert istotally_real(k)
    #c = map(x -> conjugates_log(x, C, prec, all = true, flat = false), u)

    m = log_conjugates_matrix(u,p,prec)
    m = hcat(m, matrix(base_ring(m), nrows(m), 1, [one(base_ring(m)) for i=1:nrows(m)]))
    return det(m)//degree(k)
end

"""
    regulator_iwasawa(u::Array{T, 1}, C::qAdicConj, n::Int = 10) where {T<: FacElem{nf_elem, AnticNumberField}} -> qadic

This function is not implemented. One can compute the conjugates of the factor base and take the appropriate linear combinations of the logs.
"""
function regulator_iwasawa(U::Array{T, 1}, p, prec::Int = 10) where T <: FacElem{nf_elem, AnticNumberField}

    # Note: Don't expect this code to work. It's merely a design template.

    # Find the factor base.
    all_keys = Set{nf_elem}()
    for u in U
        Ftable = factor_dict(u)
        all_keys = union(all_keys, Set(keys(Ftable)))
    end
    
    # Construct the log conjugates
    log_conj_factors = Dict(ky=>galois_orbit.(log.(embedding_classes(ky, p, prec)))
                            for ky in all_keys)

    # Unfortunately, nothing further will work without common compositums.
    error("Function still in development. The present issue is a lack of `compositum` method.")

    # Below is a template for how to continue.
    reg_matrix_rows = []
    for u in U
        Ftable = factor_dict(u)

        # The `sum` is actually julia's array sum. This is what you actually want.
        push!(reg_matrix_rows, sum([Ftable[k]*x for x in log_conj_factors[ky]]
                                   for ky in keys(Ftable)))
    end

    m = matrix(reg_matrix_rows)
    return det(m)
end

function regulator_iwasawa(K::AnticNumberField, p, prec::Int = 10)  
    # u, mu = unit_group_fac_elem(R)
    u, mu = unit_group(maximal_order(K)) # Not optimal, but good enough.
    return regulator_iwasawa([K(mu(u[i])) for i=2:ngens(u)], p, prec)
end

function regulator_iwasawa(R::NfAbsOrd, p, prec::Int = 10)    
    return regulator_iwasawa(number_field(R), p, prec)    
end


# TODO: Move to AbstractAlgebra
function matrix(a::Array{Array{T, 1}, 1}) where {T}
  return matrix(hcat(a...))
end


############################################################################################
#
# New stuff.

"""
    galois_compositum(local_fields)
Returns the compositum of the Galois closures of the fields in `local_fields`. Note that the
compositum of the fields is not canonically defined, but it's Galois closure is.
"""

"""
    minimal_compositum(local_fields)
Returns a (non-canonical) field `L` and a collection of embeddings [K -> L for K in local fields]. 
The degree of `L` is minimal among the fields which admit such embeddings.
"""
