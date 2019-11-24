
# Nemo fixes

# Ensure the generator of a degree 1 extension is just 1.
function unram_gen(Q::FlintQadicField)
    return degree(Q)==1 ? one(Q) : gen(Q)
end

# Check to ensure that the balls around the centers of the specified elements
# overlap.
function error_balls_disjoint(a,b)
    # We rely on the current FLINT implementation of `==`.
    return a != b
end

function gens(P::NfOrdIdl)
    @assert has_2_elem(P)
    (P.gen_one, P.gen_two)
end

# TODO: make the coeffs methods more consistent.
function coeffs(a::FinFieldElem)
    k = parent(a)
    coeff_field = GF(k.p)
    if degree(k) == 1
        return [one(coeff_field)]
    else
        return [coeff_field(coeff(a,j)) for j=0:degree(k)-1]
    end
end

function coeffs(a::qadic)
    k = parent(a)
    return [coeff(a,j) for j=0:degree(k)-1]
end

function mod_sym(a,b)
    c = mod(a,b)
    return c < b/2 ? c : c-b
end

function sym_lift(a::padic)
    u = unit_part(a)
    p = prime(a.parent)
    N = precision(a)
    v = valuation(a)
    return mod_sym(u, p^(N-v))*FlintQQ(p)^v
end

#############
# Linear Algebra

@doc Markdown.doc"""
    underdetermined_solve(A,b)
Solves the equation `Ax=b`. Return the first index of the column where the last entry is non-zero.
"""
# TODO: This method needs to be made more reliable. The return structure of `N` is a bit wacky.
function underdetermined_solve(A,b)

    M = hcat(A,-b)
    nu,N = nullspace(M)

    display(N)

    ind = 0
    for j=1:size(N,2)
        if isone(N[size(N,1),j])
            ind=j
            break
        end
    end
    @assert !iszero(ind)

    return nu,N,ind
end

@doc Markdown.doc"""
    underdetermined_solve_first(A,b)
Return the first basis column of the solutions to Ax=b, if it exists.
"""
function underdetermined_solve_first(A,b)
    nu,N,ind = underdetermined_solve(A,b)
    return N[1:size(N,1)-1,ind]
end

##############
# Mpoly

@doc Markdown.doc"""
    coeffs(f::AbstractAlgebra.Generic.MPolyElem, i::Integer)
Return the coefficients of the polynomial with respect to the $i$-th variable.
"""
function coeffs(f::AbstractAlgebra.Generic.MPolyElem, i::Integer)
    e_vecs = collect(exponent_vectors(f))
    t_list = collect(terms(f))

    m = gens(parent(f))[i]
    D = Dict(e=>t for (e,t) in zip(e_vecs, t_list))
    
    max_j = maximum(e[i] for e in e_vecs)

    output = AbstractAlgebra.Generic.MPolyElem[]
    for j = 0:max_j
        j_term_exps = filter(e-> e[i] == j, e_vecs)
        push!(output, sum(divexact(D[e], m^j)  for e in j_term_exps))
    end
    return output
end

@doc Markdown.doc"""
    coeffs(f::AbstractAlgebra.Generic.MPolyElem, m::AbstractAlgebra.Generic.MPolyElem)
Return the coefficients of the polynomial with respect to the variable $m$.
"""
function coeffs(f::AbstractAlgebra.Generic.MPolyElem, m::AbstractAlgebra.Generic.MPolyElem)
    i = findfirst(a->a==m, gens(parent(f)))
    return coeffs(f, i)
end

##################
# Qadic

####
## Coercion for qadic fields (because FLINT didn't bother...)

# TODO: The map should be a local field map type, not Any.
const RegisteredQadicCoercions = Dict{Tuple{FlintQadicField, FlintQadicField}, Any}()

function _create_qadic_coercion(a::FlintQadicField, b::FlintQadicField)
    i = degree(a)
    j = degree(b)
    i > j && error("Coercion to qadic subfields not implemented.")
    !divides(j,i)[1] && error("Degrees of qadic fields are incompatible for coercion.")
    
    if i==j
        RegisteredQadicCoercions[a,b] = x->b(x)
    else
        f = defining_polynomial(a)
        gen_img = roots(f, b)[1][1]
        coerce_func = x->sum(gen_img^i*coeffs(x)[i+1] for i=0:degree(a)-1)
        
        RegisteredQadicCoercions[a,b] = coerce_func
    end
    return
end

# TODO: turn this into (a::FlintQadicField)(b::qadic) and move to NEMO.
function coerce_up(a::FlintQadicField, b::qadic)
    if !haskey(RegisteredQadicCoercions, (parent(b), a))
        _create_qadic_coercion(parent(b), a)
    end
    return RegisteredQadicCoercions[parent(b), a](b)
end
