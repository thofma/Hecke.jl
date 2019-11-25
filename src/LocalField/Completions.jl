export sharpen!, completion
    
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
    return K
end

@doc Markdown.doc"""
    sharpen!(completion_map, new_prec)

Given a completion map `map: K -> Kp` from a number field `K` to a local field `Kp`, and a new precision `new_prec`, mutate `map` and `Kp` so that `Kp` has element precision `new_prec` and so that the elements in the image of the map are defined at the higher precision.

NOTE: This method will sharpen the base field of `Kp`, which will affect anything with a 
reference to it. The precision can only be increased by `sharpen!`.
"""
function sharpen!(completion_map, new_prec)
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

    K   = domain(completion_map)
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
function sharpen!(K::FlintPadicField, new_prec)
    K.prec_max = new_prec
    return K
end

function sharpen!(K::FlintQadicField, new_prec)
    K.prec_max = new_prec
    return K
end

@doc Markdown.doc"""
    sharpen_base!(K::EisensteinField, new_prec)
Apply `sharpen!` to the base field of `K`.
"""
function sharpen_base!(K::EisensteinField, new_prec)
    Q = base_ring(K)
    @assert typeof(Q) <: FlintLocalField
    sharpen!(Q, new_prec)
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
    # TODO: We are actually forced to use a root of the Conway polynomial (lifted to ZZ).
    #       Thus, we need to use a RootSharpenCtx to define/sharpen the unramified extension.
    conway_root_ctx = let

        # Set up the root sharpen context with the Conway polynomial
        con_pol = defining_polynomial(Kp_unram)
        if degree(con_pol) == 1
            con_pol = polynomial([fmpz(-1),fmpz(1)]) # x-1
        else
            con_pol = polynomial(lift.(coefficients(con_pol)))
        end

        #@info "" delta_appx typeof(delta_appx)
        #@info "" con_pol typeof(con_pol)        
        #@info "" typeof(map_coeffs(x->res(max_order(FlintZZ(x))), con_pol))
                
        RootSharpenCtx(max_order, con_pol, gen(k), res, p, 1)
    end

    sharpen_root!(conway_root_ctx, prec)
    delta = max_order(root(conway_root_ctx))
    
    delta_p = unram_gen(Kp_unram)
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

    #@info change_base_ring(Kp,K.pol)(embedding_map(gen(K)))
    
    @assert iszero(change_base_ring(Kp,K.pol)(embedding_map(gen(K))))
    #@info lift_map(embedding_map(gen(K) + 1))

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
# the default value of predicate is `x->false`
function unramified_completion(K::AnticNumberField, p::fmpz, predicate=x->false, prec=10;
                               skip_map_inverse=false)

    C = qAdicConj(K, Int(p))
    R = roots(C.C, prec)    
    
    for rt in R
        (Kp, inj) = unramified_completion(K, rt, prec, skip_map_inverse=true)
        if predicate(Kp,inj)
            return unramified_completion(K, rt, prec, skip_map_inverse=skip_map_inverse)
        end
    end
    error("Predicate is false for every unramified completion.")
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
        
        R, mR = ResidueField(parent(gen_img))

        # Construct the array of powers of the primitive element.
        pa = [one(R), mR(gen_img)]
        d = degree(R)
        while length(pa) < d
            push!(pa, pa[end]*pa[2])
        end

        # Solve a linear system to figure out how to express the root of the
        # Conway Polynomial defining the completion in terms of the image of the
        # primitive element of the number field $K$.
        m = matrix(GF(p), d, d, [coeff(pa[i], j-1) for j=1:d for i=1:d])
        o = matrix(GF(p), d, 1, [coeff(gen(R), j-1) for j=1:d])
        s = solve(m, o)
        @hassert :qAdic 1 m*s == o

        # Construct the Conway root approximation in the number field.
        a = K()
        for i=1:d
            _num_setcoeff!(a, i-1, lift(s[i,1]))
        end

        ####
        # Construct a lift of the inverse of the derivative of the Conway root in the number field.
        #
        f = defining_polynomial(parent(gen_img), FlintZZ)
        fso = inv(derivative(f)(gen(R)))
        o = matrix(GF(p), d, 1, [coeff(fso, j-1) for j=1:d])
        s = solve(m, o)
        b = K()
        for i=1:d
            _num_setcoeff!(b, i-1, lift(s[i,1]))
        end

        # End block of Claus' code.
        ####

        # Something incomprehensable happens when uncommented...
        #g = deepcopy(f)
        #@info "Before call:" f (f===g)        
        #RootSharpenCtx_constructor(K, g, mR(gen_img), x->mR(embedding_map(x)), p, 1)
        #@info "After return statement: " f typeof(f) f===g parent(f) f(0)

        # Lift the data from the residue field back to the number field.
        backward_sharpening_ctx = RootSharpenCtx{nf_elem}(f, a, b, p, 1)        
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
    C = qAdicConj(K, Int(p))    
    R = roots(C.C, prec)    
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
