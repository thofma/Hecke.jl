
#########################################################################################
#
#   Embedding classes (up to equivalence) interface
#
#########################################################################################

# Return the embeddings, up to local Galois automorphisms, of a number field element `a`.
# Treatment is different in ramified versus unramified cases due to the extra structure.
# i.e, a factorization method is present in the unramified case.

function embedding_classes(a::nf_elem, p, prec=10)
    K = parent(a)
    comps = completions(K,p, prec)
    embeddings_up_to_equiv = [mp(a) for (field,mp) in comps]
    return embeddings_up_to_equiv
end

function embedding_classes_unramified(a::nf_elem, p::fmpz, prec=10)
    K = parent(a)
    completions = unramified_completions(K, p, prec)
    embeddings_up_to_equiv = [mp(a) for (field, mp) in completions]
    
    return embeddings_up_to_equiv
end

function embedding_classes_ramified(a::nf_elem, p::fmpz, prec=10)
    K = parent(a)
    completions = ramified_completions(K, p, prec)
    embeddings_up_to_equiv = [mp(a) for (field, mp) in completions]
    
    return embeddings_up_to_equiv
end


function embedding_classes_unramified(a::nf_elem, p::Integer, prec=10)
    embedding_classes_unramified(a, FlintZZ(p), prec)
end

function embedding_classes_ramified(a::nf_elem, p::Integer, prec=10)
    embedding_classes_ramified(a, FlintZZ(p), prec)
end


#########################################################################################
#
#   Conjugates interface
#
#########################################################################################


#to compare to the classical conjugates
#  all = true/ false: only on of a pair of complex conjugates is returned
#  flat = true/ false: return (Re, Im) or the complex number
#TODO: not sure how this would work in the ramified, not-normal case.
@doc Markdown.doc"""
    conjugates(a::nf_elem, C::qAdicConj, n::Int = 10; flat::Bool = false, all:Bool = true) -> []

Returns an array of the q-adic conjugates of $a$: Let $p Z_K = \prod P_i$ for the maximal order
$Z_K$ of the parent of $a$. Then $K \otimes Q_p = \prod K_{P_i}$. For each of the $P_i$
a $q$-adic (unramifed) extension $K_{P_i}$ of $Q_p$ is computed, sth. $a$ has $\deg P_i = \deg K_{P_i}$
many cojugates in $K_{P_i}$.
If {{{all = true}}} and {{{ flat = false}}}, the default, then all $n$ conjugates are returned.
If {{{all = false}}}, then for each $P_i$ only one conjugate is returned, the others could be 
xomputed using automorphisms (the Frobenius).
If {{{flat = true}}}, then instead of the conjugates, only the $p$-adic coefficients are returned.
"""
function local_conjugates(a::nf_elem, p::fmpz, prec=10)
    return galois_orbit.(embedding_classes(a, p, prec))
end

function local_conjugates(a::nf_elem, p::Integer, prec=10)
    return local_conjugates(a, fmpz(p), prec)
end


#########################################################################################
#
#   Frobenius application interface
#
#########################################################################################

@doc Markdown.doc"""
    frobenius(f::PolyElem)
Apply frobenius to the coefficients of the polynomial `f`, returns a new polynomial.
"""
function frobenius(f::PolyElem)
    g = deepcopy(f)
    g.coeffs = frobenius.(f.coeffs)
    return g
end

#TODO: implement a proper Frobenius - with caching of the frobenius_a element
# Function to apply each of [id, frob, frob^2, ..., frob^n] to an object,
# whatever that might mean.
function _frobenius_orbit(a, n)
    result = [a]
    y = a
    for i=2:n
        y = frobenius(y)
        push!(result, y)
    end
    return result
end

@doc Markdown.doc"""
    frobenius_orbit(a)
Returns the array [a, frob(a), ..., frob^d(a)]. The number `d` is defined as:
-- the degree of the parent of `a`, if `a` is a `qadic` element.
-- the degree of the base_field of the parent of `a`, if `a` is a polynomial.
"""
function frobenius_orbit(a::FieldElem)
    return _frobenius_orbit(a, degree(parent(a)))
end

function frobenius_orbit(f::PolyElem{qadic})
    return _frobenius_orbit(f, degree(base_ring(parent(f))))
end


#########################################################################################
#
#   Orbits under the galois group (of a local field).
#
#########################################################################################


function galois_orbit(a::qadic)
    return frobenius_orbit(a)
end

function galois_orbit(f::PolyElem{qadic})
    return frobenius_orbit(f)
end

function galois_orbit(a::eisf_elem)
    G = galois_group(parent(a))
    return [mp(a) for mp in G]
end

@doc Markdown.doc"""
    galois_group(K)
Return the galois group of the galois closure of $K$. Rather, return a list of julia functions
defining the field automorphisms over the prime field.
"""
function galois_group(K)
    #TODO: At the time of writing, there wasn't a clear paradigm for how Galois groups of fields
    # should work. Please update this code once the appropriate design has been determined.
    
    Kgal, mp = galois_closure(K)
    @assert gen(Kgal) == mp(gen(K))
    
    f = defining_polynomial(Kgal)
    f_orbit = galois_orbit(f)
    
    gen_rts = vcat([map(x->x[1], roots(g, Kgal)) for g in f_orbit]...)
    galois_maps = [a->sum(coeff(a,i)*rt^i for i=0:degree(Kgal)-1) for rt in gen_rts]

    return galois_maps
end

function galois_group(K::FlintQadicField)
    #TODO: At the time of writing, there wasn't a clear paradigm for how Galois groups of fields
    # should work. Please update this code once the appropriate design has been determined.
    d = absolute_degree(K)
    return [x->frobenius(x,i) for i=1:d]
end

function galois_group(K::FlintPadicField)
    #TODO: At the time of writing, there wasn't a clear paradigm for how Galois groups of fields
    # should work. Please update this code once the appropriate design has been determined.
    return [identity]
end

#########################################################################################
#
#   Misc group functions.
#
#########################################################################################

function orbit(G,a)
    return [mp(a) for mp in G]
end


# This function is now obsolete. Use coeffs.(embedding_classes(a)) instead.
#
# function flat(a::Array{qadic, 1})
#   if flat
#     r = padic[]
#     for x = re
#       for i=1:degree(parent(x))
#         push!(r, coeff(x, i-1))
#       end
#     end
#     return r
#   else
#     return re
#   end
# end


#########################################################################################
#
#   Galois closures
#
#########################################################################################

@doc Markdown.doc"""
    field_of_definition(a::padic)
    field_of_definition(a::qadic)
Returns the degree of the extension defining `a`.
"""
function degree_of_field_of_definition(a::qadic)
    for d in filter(x->x>0, divisors(degree(parent(a))))
        if a == frobenius(a,d)
            return d
        end
    end
    error("No power of frobenius of $a equals $a.")
end

function degree_of_field_of_definition(a::padic)
    return 1
end


@doc Markdown.doc"""
    galois_closure(K::EisensteinField)
Returns an Eisenstein field `L` such that `L/Qp` is Galois. Also return a map.
Note that the Eisenstein Field will be over a Qadic base, which might be an extension of
the base field of $K$.
"""
function galois_closure(K::EisensteinField)
    !is_tamely_ramified(K) && error("Wild ramification still not possible.")
    is_tamely_ramified(K) && return _galois_closure_tamely_ramified(K)
end

function galois_closure(K::FlintLocalField)
    return K, identity
end

function _galois_closure_tamely_ramified(K::EisensteinField)
    L, mp_to_squash, _ = simple_extension(K)

    # TODO: Add reference.
    # The size of the Galois closure of a tamely ramified extension is given by
    # the classification of tamely ramified extensions. (given by a poly of the form `X^e-u*p`.)
    # 
    frob_orbit_size = lcm(map(degree_of_field_of_definition, coefficients(L.pol)))

    g = change_base_ring(L, L.pol)
    X = gen(parent(g))
    h = fprimpart(g(uniformizer(L)*X))

    # Note that $h$ is guarenteed to be squarefree over the residue field by the
    # tameness assumption, since the degree of `h` is coprime to `p`.

    k,res = ResidueField(L)
    ext_degrees = map(x->degree(x[1]), factor(map_coeffs(res, h)))

    Lgal, _, mp_to_gal = unramified_extension(L, frob_orbit_size*lcm(ext_degrees))

    #@info "" mp_to_gal mp_to_squash
    
    return Lgal, (mp_to_gal === mp_to_squash === identity) ? identity : x->mp_to_gal(mp_to_squash(x))
end

@doc Markdown.doc"""
    is_tamely_ramified(K::NALocalField)
"""
function is_tamely_ramified(K::NALocalField)
    return gcd(prime(K), ramification_degree(K)) == 1
end

