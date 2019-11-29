export sharpen!, sharpen_base!, completion, completions, ramified_completion, unramified_completion, ramified_completions, unramified_completions
    
#########################################################################################
#
#   Sharpening
#
#########################################################################################

# Contexts for sharpening.

# Reminicent of the "qAdicConj" context, but more general.
# Structure to keep track of information while performing a newton lift. The polynomial
# is always exact. However, the root can either live in an approximate field, or 
mutable struct RootSharpenCtx{T}
    polynomial             # Should be an exact polynomial
    #derivative_polynomial # cached derivative of polynomial. Not clear if this should be cached.
    field                  # field of definition of root
    prime                  # The prime with respect to which newton lifting will be done.
    root                   # the root of a polynomial
    root_derivative_inv    # Basically, `1/f'(a)`.
    precision              # current precision of the root

    function RootSharpenCtx{T}(polynomial, root::T) where T <: NALocalFieldElem
        ctx = new()
        ctx.polynomial = change_base_ring(FlintZZ, polynomial)
        ctx.field = parent(root)
        ctx.prime = prime(parent(root))
        ctx.root  = root 
        ctx.precision = precision(root)
        return ctx
    end

    function RootSharpenCtx{T}(polynomial, root::T, rt_der_inv, prime, prec) where T
        ctx = new()
        ctx.polynomial = change_base_ring(FlintZZ, polynomial)
        ctx.field = parent(root)
        ctx.prime = prime
        ctx.root  = root
        ctx.root_derivative_inv = rt_der_inv
        ctx.precision = prec

        #@info "Before the struct is returned" polynomial typeof(polynomial)
        return ctx
    end
end


"""
    RootSharpenCtx(polynomial, root_appx::nf_elem, res_mp, prime, prec)
Given a polynomial `f`, and an approximate root such that `f(res_mp(root_appx)) = 0`,
and maps to/from the residue ring, construct a RootSharpenContext that solves 
`f(root_appx) = 0 mod P^n`, where `P` is the kernel of `res_mp: maximal_order(K) --> k`.

The root is assumed to be simple in the residue ring.
"""
function RootSharpenCtx(R, f, root_appx, res_mp, prime, prec)

    k = parent(root_appx)
    BO = basis(R)

    A = matrix(coeffs.(res_mp.(BO)))
    b = matrix(coeffs(root_appx))

    #@info A
    y = underdetermined_solve_first(A,b) # should be solve(A,b) in the future.
    @hassert :qAdic 1 A*b == y
    
    # This is the lift of the generator of the Qadic subfield of the completion.
    root_appx_nf = sum([a*b for (a,b) in zip(BO,lift(y))])

    # Root derivative inverse approximation
    fp  = change_base_ring(k, f)

    @info root_appx
    @assert fp(root_appx) == 0
    
    fps = derivative(fp)
    rt_der_in_k = fps(root_appx)

    b = matrix(coeffs(inv(rt_der_in_k)))
    y = underdetermined_solve_first(A,b) # should be solve(A,b)
    @hassert :qAdic 1 A*b == y
    
    
    # This is the lift of the generator of the Qadic subfield of the completion.
    root_der_appx = R(sum([a*b for (a,b) in zip(BO,lift(y))]))
    
    #@info "Before constructor call:" f typeof(f)
    ctx = RootSharpenCtx{typeof(root_appx_nf)}(f, root_appx_nf, root_der_appx, prime, 1)
    #@info "After constructor call:" f typeof(f)

    #TODO: Some very strange things happen sometimes when this function returns.
    # it requires some investigation.
    return ctx
end

root(C::RootSharpenCtx) = C.root

# Sharpen the root in the context to level `n`
function sharpen_root!(ctx::RootSharpenCtx{T}, prec) where T<:NALocalFieldElem
        
    f  = ctx.polynomial
    ctx.precision > prec  && error("Cannot sharpen to lower precision.")
    ctx.precision == prec && return
    ctx.precision = prec

    
    # sharpen field defining polynomials trivially
    K = ctx.field

    if !isa(K, FlintLocalField)
        sharpen_base!(K,prec)
        setprecision!(K.pol, prec)        
    end
    K.prec_max = prec
    
    # Then newton lift the roots
    # Hope it is continuous.
    test = newton_lift!(f, ctx.root)

    @info "" test precision(ctx.root)

    return ctx
end

# Sharpen the root in the context to level `n`
function sharpen_root!(ctx::RootSharpenCtx, prec)
        
    ctx.precision > prec  && error("Cannot sharpen to lower precision.")
    ctx.precision == prec && return

    (a,o) = let
        # Perform a newton iteration, but over the number field.
        # Input:  f(a) = 0 mod p, o*f'(a) = 1 mod p,
        # Output: `a` such that f(a) = 0 mod p^n
        
        f  = ctx.polynomial
        ppow = ctx.prime ^ ctx.precision
        a = ctx.root
        k = ctx.precision
        o = ctx.root_derivative_inv
        
        while k < prec
            ppow *= ppow
            k *= 2

            pa = [one(a)]
            while length(pa) <= degree(f)
                push!(pa, pa[end]*a)
                mod_sym!(pa[end], ppow)
            end
            fa  = sum(coeff(f, i-1) * pa[i] for i=1:length(pa))
            fsa = sum(coeff(f, i) * i * pa[i] for i=1:length(pa)-1)  
            o = o*(2-fsa*o)
            a = a - fa*o
            mod_sym!(o, ppow)
            mod_sym!(a, ppow)
        end
        (a,o)
    end #### End Claus' code.

    ctx.precision = prec
    ctx.root = a
    ctx.root_derivative_inv = o
    return ctx
end


# Sharpening context for defining a completion map via linear algebra.
# TODO: Investigate name.
mutable struct DixonSharpenCtx
    local_basis_lift
    prime_ideal # Thing to understand maximal_order/P^N
    avec    # coordinates of the number field generator
    pie_vec # coordinates of uniformizer^e
    img_nf_gen
    pi
    delta
end


#****************************************************************************

"""
    sharpen!(K::EisensteinField, g::PolyElem, new_prec)
Mutate the Eisenstein field so that the defining polynomial has coefficients
with precision `new_prec`. The base ring of `K` must have precision at least `new_prec`. For
further information, see the documentation.
"""
function sharpen!(K::EisensteinField, new_prec)

    if new_prec > base_ring(K).prec_max
        error("Base field must be explicitly sharpened to the desired precision prior "*
              "to sharpening the extension. For more information, see the documentation.")
    end
    f = K.pol
    f = setprecision!(f, new_prec)
    sharpen!(K, f, new_prec)
end

"""
    sharpen!(K::EisensteinField, g::PolyElem, new_prec)
Given a polynomial `g` whose coefficients are coercible into the base ring of `K`, and a
new precision, mutate the Eisenstein field so that the defining polynomial has coefficients
with precision `new_prec`. The base ring of `K` must have precision at least `new_prec`. For
further information, see the documentation.
"""
function sharpen!(K::EisensteinField, g::PolyElem, new_prec)

    # Note: The base field must also be sharpened in order for pre-existing elements
    #       to live in the same field. This means other extensions defined over the
    #       same base field are affected by the mutated!!!
    #
    #       For this reason. The base field has to be explicitly sharpened before
    #       any sharpening of extensions occurs.
    
    if new_prec > base_ring(K).prec_max
        error("Base field must be explicitly sharpened to the desired precision prior "*
              "to sharpening the extension. For more information, see the documentation.")
    end

    # Prepare new defining polynomial.
    Rdat = K.data_ring
    Rx   = Rdat.base_ring
    gp = g(gen(Rx))

    # Precision can only increase by sharpen! There should be a separate method to drop precision.
    @assert minimum(precision.(coefficients(gp))) <= new_prec    
    if error_balls_disjoint(gp, Rdat.modulus)
        error("New polynomial does not refine coefficients of the existing defining polynomial.")
    end
    
    Rdat.modulus = gp
    K.pol = Rdat.modulus
    K.prec_max = new_prec
    return K
end

@doc Markdown.doc"""
    sharpen!(completion_map, new_prec)

Given a completion map `map: K -> Kp` from a number field `K` to a local field `Kp`, and a new precision `new_prec`, mutate `map` and `Kp` so that `Kp` has element precision `new_prec` and so that the elements in the image of the map are defined at the higher precision.

NOTE: This method will sharpen the base field of `Kp`, which will affect anything with a 
reference to it. The precision can only be increased by `sharpen!`.
"""
function sharpen!(completion_map::NACompletionMap, new_prec)
    completion_map = sharpen_forward_map!(completion_map, new_prec,
                                          forward_sharpening_context(completion_map))
    completion_map = sharpen_backward_map!(completion_map, new_prec,
                                           backward_sharpening_context(completion_map))
    return completion_map
end


# Sharpen via polynomial (RootSharpenCtx)
#=
The point of this interface is to allow the sharpening of the completion map to a field 
by fixing the defining polynomials and sharpening the root. 
=#

#TODO: Once Contexts encapsulate the principal sharpening problem,
# There is no need for the multitude of functions.
function sharpen_forward_map!(completion_map, new_prec, ctx::RootSharpenCtx)
    sharpen_root!(ctx, new_prec)
    return completion_map
end

function sharpen_backward_map!(completion_map, new_prec, ctx::RootSharpenCtx)
    sharpen_root!(ctx, new_prec)
    return completion_map
end

function sharpen_backward_map!(completion_map, new_prec, ctx::Nothing)
    return completion_map
end


function sharpen_forward_map!(completion_map, new_prec, DixCtx::DixonSharpenCtx)

    K  = domain(completion_map)
    Kp = codomain(completion_map)

    P = DixCtx.prime_ideal
    
    # TODO: The sharpening methods can be improved a lot with a decent caching strategy.
    # TODO: Replace asserts with something compiler-safe
        
    lif = preimage_function(completion_map)

    # Sharpen the base ring.
    sharpen_base!(Kp, new_prec)
    Kp_unram = base_field(Kp)
    
    max_ord = maximal_order(K)
    pi = max_ord(lif(gen(Kp)))
    e  = degree(Kp)
    f  = degree(Kp_unram)

    delta_p = unram_gen(Kp_unram)
    delta   = max_ord(lif(Kp(delta_p)))

    ####
    # Sharpen the defining polynomial
    #
    # TODO: Things that should be cached:
    # -- local_basis_lift
    # -- Dixon lifting data for the solution to Ag = error

    
    # Construct the integer matrix encoding coordinates with respect to pi, delta modulo P^N.
    # Basis elements for the local field and the ideal P^prec
    BKp = [pi^i*delta^j for j=0:f-1 for i=0:e-1]
    BPn = basis(P^new_prec)
    local_basis_lift = hcat(matrix(coordinates.(BKp)), matrix(coordinates.(BPn)))
    

    @info "" precision(base_ring(Kp)) new_prec

    gnew = let
        N = underdetermined_solve_first(local_basis_lift, -matrix([coordinates(pi^e)]))
        RX,X = PolynomialRing(Kp_unram,"X")
        X^e + sum(X^i*delta_p^j * N[i*f + j + 1] for j=0:f-1 for i=0:e-1)
    end

    @info gnew

    sharpen!(Kp, gnew, new_prec)

    ####
    # Sharpen the inclusion map
    #
    # TODO: Things that should be cached:
    # -- coefficients defining the image of the number field generator.

    # Update delta_p to be the new generator.
    delta_p = unram_gen(Kp_unram)
    
    img_nf_gen = let
        a = gen(K)
        avec = matrix(FlintZZ, length(coeffs(a)), 1, coeffs(a))        
        N = underdetermined_solve_first(local_basis_lift, avec)
        sum(gen(Kp)^i*delta_p^j * N[i*f + j + 1] for j=0:f-1 for i=0:e-1)
    end
    
    DixCtx.img_nf_gen = img_nf_gen
    return completion_map
end


@doc Markdown.doc"""
    sharpen!(K::FlintLocalField, new_prec)
Change the `prec_max` field of `K`. Effectively, this increases the precision of new elements
created in `K`.
"""
function sharpen!(K::FlintLocalField, new_prec)
    setprecision!(K, new_prec)
end

@doc Markdown.doc"""
    sharpen_base!(K::NALocalField, new_prec)
    sharpen_base!(K::EisensteinField, g::PolyElem, new_prec)

Apply `sharpen!` to the base field of `K`. If the base field is an Eisenstein field, a polynomial
may be provided.
"""
function sharpen_base!(K::NALocalField, new_prec)
    Q = base_ring(K)
    sharpen!(Q, new_prec)
    return K
end

function sharpen_base!(K::EisensteinField, g::PolyElem, new_prec)
    Q = base_ring(K)
    typeof(Q) <: FlintLocalField && (
        error("Polynomial cannot be provided if base field is a FlintLocalField"))
    sharpen!(Q, g, new_prec)
    return K
end

@doc Markdown.doc"""
    sharpen_tower!(K::NALocalField, new_prec)

Apply `sharpen!(*, new_prec)` to all fields in the tower defining `K` (including `K`).
"""
function sharpen_tower!(K::FlintLocalField, new_prec)
    if isa(K, FlintLocalField)
        sharpen!(K, new_prec)
        return K
    end
    sharpen_tower!(base_field(K), new_prec)
    return K
end

function setprecision!(a::eisf_elem, N)
    for c in coeffs(a)
        setprecision!(c, N)
    end
    return a
end

function setprecision!(f::AbstractAlgebra.Generic.Poly{<:NALocalFieldElem}, N::Int)
  for i=1:length(f)
    setprecision!(f.coeffs[i], N)
  end
  return f
end


#########################################################################################
#
#   Conway root in number fields.
#
#########################################################################################

#=
(R, f, root_appx, res_mp, prime, prec)

    k = parent(root_appx)
    BO = basis(R)

    A = matrix(coeffs.(res_mp.(BO)))
    b = matrix(coeffs(root_appx))

    #@info A
    y = underdetermined_solve_first(A,b) # should be solve(A,b) in the future.
    @hassert :qAdic 1 A*b == y
    
    # This is the lift of the generator of the Qadic subfield of the completion.
    root_appx_nf = sum([a*b for (a,b) in zip(BO,lift(y))])

    # Root derivative inverse approximation
    fp  = change_base_ring(k, f)

    @info root_appx
    @assert fp(root_appx) == 0
    
    fps = derivative(fp)
    rt_der_in_k = fps(root_appx)

    b = matrix(coeffs(inv(rt_der_in_k)))
    y = underdetermined_solve_first(A,b) # should be solve(A,b)
    @hassert :qAdic 1 A*b == y
    
    
    # This is the lift of the generator of the Qadic subfield of the completion.
    root_der_appx = R(sum([a*b for (a,b) in zip(BO,lift(y))]))
    
    #@info "Before constructor call:" f typeof(f)
    ctx = RootSharpenCtx{typeof(root_appx_nf)}(f, root_appx_nf, root_der_appx, prime, 1)
    #@info "After constructor call:" f typeof(f)

    #TODO: Some very strange things happen sometimes when this function returns.
    # it requires some investigation.
return ctx
=#

"""
    _root_ctx_for_number_field(basis, basis_img, f, ff_root, prime, prec)

Given a `basis` for some order in a number field, mapping to `basis_img` in the parent
of `ff_root`, a polynomial `f` such that `f(ff_root) == 0`, a `prime` and a precision `prec`,
returns a RootSharpenCtx for solving `f(a) = 0 mod P^n` in the number field.
"""
function _root_ctx_for_number_field(basis, basis_img, f, ff_root, prime, prec)

    k = parent(ff_root)
    d = degree(k)
    
    # Solve a linear system to figure out how to express the root of the
    # polynomial defining the completion in terms of the image of the basis.
    a_entries = hcat(coeffs.(basis_img)...)    
    A = matrix(a_entries)

    lift_to_nf = let        
        b = matrix(GF(Int64(prime)), d, 1, [coeff(ff_root, j-1) for j=1:d]) #Finite field types...
        #@info "" b typeof(b)
        y = underdetermined_solve_first(A, b)
        @hassert :qAdic 1 A*y == b
        
        lift_to_nf = sum([a*b for (a,b) in zip(basis, lift(y))])
    end
    
    invder_in_nf = let
        fso = inv(derivative(f)(ff_root))
        b = matrix(GF(Int64(prime)), d, 1, [coeff(fso, j-1) for j=1:d])
        z = underdetermined_solve_first(A, b)
        @assert A*z == b
        
        sum([a*b for (a,b) in zip(basis, lift(z))])
    end
    #@info "" f f(ff_root) invder_in_nf*derivative

    # Lift the data from the residue field back to the number field.
    T = typeof(lift_to_nf)
    ctx = RootSharpenCtx{T}(f, lift_to_nf, invder_in_nf, prime, 1)
    return ctx

end

#########################################################################################
#
#   Completion (single)
#
#########################################################################################

function completion(K::NumField{T} where T, P::NfOrdIdl, prec=10; skip_map_inverse=false)
    if ramification_index(P) == 1
        return unramified_completion(K, P, skip_map_inverse=skip_map_inverse)
    else
        return ramified_completion(K, P, prec, skip_map_inverse=skip_map_inverse)
    end
end

function ramified_completion(K::NumField{T} where T, P::NfOrdIdl, prec=10; skip_map_inverse=false)
    generic_completion(K, P, prec, skip_map_inverse=skip_map_inverse)
end
    
function generic_completion(K::NumField{T} where T, P::NfOrdIdl, prec=10; skip_map_inverse=false)

    # Determine a polynomial over Kp_unram which annihilates pi.

    # The method used here is to find a solution to `g(b) mod P^prec`, where
    # the residue image of `b` is a (Conway) generator for the residue field.

    # This is definitely not the best algorithm. In the unramified, non-index-divisor
    # case, computing powers of `P` is trivial. In the other (likely important)
    # cases, it is likely worthwhile to see if computing powers is also easy.
    
    @assert has_2_elem(P)
    a  = gen(K)
    p  = gens(P)[1]
    pi = gens(P)[2]
    max_order = maximal_order(K)

    
    # Determine ramification index.
    e = ramification_index(P)
    d = degree(K)

    # Figure out the unramified part.
    k,res = ResidueField(max_order,P)
    f = degree(k)
    Kp_unram = QadicField(p, f, prec)
    
    # Lift the conway generator of the finite field to the number field.
    # We are actually forced to use a root of the Conway polynomial (lifted to ZZ).
    # Thus, we need to use a RootSharpenCtx to define/sharpen the unramified extension.

    # Set up the root sharpen context with the Conway polynomial

    con_pol, rt = let
        pol = defining_polynomial(Kp_unram)
        if degree(pol) == 1
            pol = polynomial([fmpz(-1),fmpz(1)]) # This is x-1
        else
            pol = polynomial(lift.(coefficients(pol)))
        end
        pol, roots(change_base_ring(k, pol))[1]
    end

    B = basis(max_order)
    conway_root_ctx = _root_ctx_for_number_field(B, res.(B), con_pol, rt, p, 2)

    #@info "" (derivative(conway_root_ctx.polynomial)(root(conway_root_ctx))*conway_root_ctx.root_derivative_inv -1) in P
    
    sharpen_root!(conway_root_ctx, prec)

    #@info conway_root_ctx conway_root_ctx.polynomial(root(conway_root_ctx)) in P^2
    #@info "" Kp_unram con_pol con_pol(root(conway_root_ctx))
    
    sharpen_root!(conway_root_ctx, prec)
    delta = max_order(root(conway_root_ctx))
    delta_p = unram_gen(Kp_unram)

    @assert (con_pol(delta) in P)
    #@info "" Kp_unram delta delta_p
    
    # Construct the integer matrix encoding coordinates with respect to pi, delta modulo P^N.
    # Basis elements for the local field and the ideal P^(prec*e). This gives `prec` digits of
    # precision on the ground field.
    BKp = [pi^i*delta^j for j=0:f-1 for i=0:e-1]
    BPn = basis(P^(prec*e))
    local_basis_lift = hcat(matrix(coordinates.(BKp)), matrix(coordinates.(BPn)))

    ##################################################
    # Build the completion structure.
    g = let
        #N = underdetermined_solve_first(local_basis_lift, -matrix([coordinates(pi^e)]))
        N = solve(local_basis_lift, -matrix([coordinates(pi^e)]))
        RX,X = PolynomialRing(Kp_unram,"X")
        
        X^e + sum(X^i*delta_p^j * N[i*f + j + 1] for j=0:f-1 for i=0:e-1 )
    end

    #@info "" g
    Kp, Y = EisensteinField(g,"_\$")

    ##################################################
    # Compute the maps
    
    img_nf_gen = let
        avec = matrix(FlintZZ, length(coeffs(a)), 1, coeffs(a))        
        #N = underdetermined_solve_first(local_basis_lift, avec)
        N = solve(local_basis_lift, avec)        
        sum(Y^i*delta_p^j * N[i*f + j + 1] for j=0:f-1 for i=0:e-1)
    end

    #@info "Printing nf gen image:" img_nf_gen

    # Cache the sharpening data in some way.
    DixCtx = DixonSharpenCtx(local_basis_lift,
                             P,
                             matrix(FlintZZ, length(coeffs(a)), 1, coeffs(a)),
                             -matrix([coordinates(pi^e)]),
                             img_nf_gen, pi, delta)


    
    # Construct the forward map, embedding $K$ into its completion.
    # The map is determined by the image of the number field generators.
    function embedding_map(a::nf_elem)
        return sum(coeffs(a)[j+1] * DixCtx.img_nf_gen^j for j=0:d-1)
    end

    # Construct the lifting map, from the completion back to $K$. The map is determined by
    # the lifts of the generators of the ramified/unramified parts of the eisenstein extension.
    function lift_map(x::eisf_elem)
        iszero(x) && return zero(K)
        qadic_coeffs = coeffs(x)
        return sum(pi^i * delta^j * K(sym_lift(coeffs(qadic_coeffs[i])[j+1]))
                   for j=0:f-1 for i=0:length(qadic_coeffs)-1 )        
    end

    completion_map = NACompletionMap(K, Kp, embedding_map, lift_map, DixCtx, nothing)
    
    #TODO: Move to proper tests
    # Sanity check the returns
    #@info "" embedding_map(K(delta)) delta_p    
    #@info "" Kp.pol embedding_map(gen(K)) change_base_ring(Kp,K.pol)(embedding_map(gen(K)))
    
    @assert iszero(change_base_ring(Kp,K.pol)(embedding_map(gen(K))))

    return Kp, completion_map
end


@doc Markdown.doc"""
    completion(K::AnticNumberField, P::NfOrdIdl) -> FlintQadicField, Map{AnticNumberField -> FlintQadicField}
The completion of $K$ wrt to the topology induced by the valuation at $P$. $P$ needs
to be unramifed.
The map giving the embedding of $K$ into the completion, admits a pointwise pre-image to obtain a lift.
Note, that the map is not well defined by this data: $K$ will have $\deg P$ many embeddings.
"""
function unramified_completion(K::AnticNumberField, P::NfOrdIdl, prec=10; skip_map_inverse=false)
    #non-unique!! will have deg(P) many
    p = minimum(P)
    pi = P.gen_two.elem_in_nf
    predicate = (Kp,inj) -> valuation(inj(pi)) > 0
    
    return unramified_completion(K, p, predicate, prec, skip_map_inverse=skip_map_inverse)
end

# Find the first unramified completion over `p` such that `predicate(Kp,inj)` is `true`.
# the default value of predicate is `(x,y)->false`
function unramified_completion(K::AnticNumberField, p::fmpz, predicate=(x,y)->false, prec=10;
                               skip_map_inverse=false)

    R = _unram_gen_images(K,p,prec)    
    for rt in R
        (Kp, inj) = unramified_completion(K, rt, prec, skip_map_inverse=true)
        if predicate(Kp,inj)
            return unramified_completion(K, rt, prec, skip_map_inverse=skip_map_inverse)
        end
    end
    error("Predicate is false for every unramified completion.")
end

""" Compute the different q-adic roots of K.pol"""
function _unram_gen_images(K::AnticNumberField, p::fmpz, prec)
    
    # TODO: The Hensel context will fail if K.pol is a power modulo p.
    f = change_base_ring(FlintZZ, K.pol)
    H  = Hecke.factor_mod_pk_init(f, Int(p))
    lf = factor_mod_pk(H, prec)

    # Note there is only one qadic field per degree here.
    fields = [QadicField(p, d, prec) for d = Set(degree(y) for y = keys(lf))]
    rts = qadic[]
    for Q in fields
        for g = keys(lf)
            if degree(g) == degree(Q)
                push!(rts, any_root(g, Q)[1])
            end
        end
    end

    return rts
end


@doc Markdown.doc"""
    completion(K::AnticNumberField, p::fmpz, i::Int) -> FlintQadicField, Map

The completion corresponding to the $i$-th conjugate in the non-canonical ordering of
{{{conjugates}}}.
"""
function completion(K::AnticNumberField, p::fmpz, i::Int)
    @assert 0<i<=degree(K)
    return unramified_completions(K, fmpz(p))[i]
end

completion(K::AnticNumberField, p::Integer, i::Int) = completion(K, FlintZZ(p), i)


# Give the unramified completion where gen(K) is mapped to `gen_img`. It is assumed that
# gen_img satisfied `change_base_ring(Kp, K.pol)(gen_img) == 0`.
function unramified_completion(K::AnticNumberField, gen_img::qadic, prec=10; skip_map_inverse=false)

    p = prime(parent(gen_img))    
    Zx = PolynomialRing(FlintZZ, cached = false)[1]

    # The element `a` is replaced by a polynomial. It is assumed that the variable
    # in the polynomial is identified with the generator of the number field.    
    function embedding_map(a)
        @assert parent(a) == K
        d = denominator(a)
        f = Zx(d*a)
        return inv(parent(gen_img)(d))*f(gen_img)
    end    

    # Initialize the sharpening context for later increases to precision.
    forward_sharpening_ctx = RootSharpenCtx{typeof(gen_img)}(K.pol, gen_img)
    
    if !skip_map_inverse

        # The choice is correct here because the correct residue image function.
        R, mR = ResidueField(parent(gen_img))
        d = degree(R)
        
        # Construct the array of powers of the primitive element.
        # pa = [one(R), mR(gen_img)]
        # d = degree(R)
        # while length(pa) < d
        #     push!(pa, pa[end]*pa[2])
        # end

        f = defining_polynomial(parent(gen_img), FlintZZ)
        pa   = d==1 ? [one(R)] : powers(mR(gen_img), d-1)
        pows = d==1 ? [one(K)] : powers(gen(K), d-1)
        
        backward_sharpening_ctx = _root_ctx_for_number_field(pows, pa, f, gen(R), p, prec)
        sharpen_root!(backward_sharpening_ctx, prec)

        lift_map = function(x::qadic)
            iszero(x) && return K(0)
            
            n = x.length
            r = K(lift(coeff(x, n-1)))
            while n > 1
                n -= 1
                r = r*backward_sharpening_ctx.root + lift(coeff(x, n-1))
            end
            return r
        end
        
    else
        lift_map(x::qadic) = (
            error("Completion lift map definition was skipped during initialization."))
        backward_sharpening_ctx = nothing
    end

    Kp = parent(gen_img)
    @assert iszero(change_base_ring(Kp,K.pol)(embedding_map(gen(K))))
    
    comp_map = NACompletionMap(K, Kp, embedding_map, lift_map,
                               forward_sharpening_ctx, backward_sharpening_ctx)
    return Kp, comp_map
end

#########################################################################################
#
#   Completions (plural)
#
#########################################################################################


# Returns the unramified completions of $K$ over the prime $p$.
function unramified_completions(K::AnticNumberField, p::fmpz, prec=10)

    # TODO: The HenselCtx fails to properly detect the correct unramified completion
    # if `K.pol mod p` is pathological.
    
    # TODO: This is the last bastion of the qAdicConj structure!
    # Since in the unramified case we complete via factorizations, we first
    # construct the roots data needed to define/sharpen the extension.
    #C = qAdicConj(K, Int(p))
    #roots(C.C, prec)
    R = _unram_gen_images(K, p, prec) 
    return [unramified_completion(K, rt, prec) for rt in R]
end

function unramified_completions(K::AnticNumberField, p, prec=10)
    unramified_completions(K::AnticNumberField, FlintZZ(p), prec)
end

function ramified_completions(K::AnticNumberField, p, prec=10)
    lp = prime_decomposition(maximal_order(K), p)
    ramified_prime_ideals = [P[1] for P in lp if isramified(P)]

    T = Array{EisensteinField, 1}
    return T([Hecke.completion(K,P, precision) for P in ramified_prime_ideals])
end

function completions(K::AnticNumberField, p, prec=10)    
    if isramified(maximal_order(K), p)
        lp = prime_decomposition(maximal_order(K), p)
        prime_ideals = [P[1] for P in lp]
        return [completion(K,P,prec) for P in prime_ideals]
    else
        return unramified_completions(K, p, prec)
    end
end
