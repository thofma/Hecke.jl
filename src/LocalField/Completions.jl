export sharpen!, completion
    
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

#########################################################################################
#
#   Sharpening
#
#########################################################################################

# Mock code to support changing precision on objects.
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
    return
end

@doc Markdown.doc"""
    sharpen!(Kp::EisensteinField, P::NfAbsOrdIdl, completion_maps, new_prec)

Given a local field `Kp`, assumed to be constructed as a completion, a place `P`, the 
map data for the completion, and a new precision `new_prec`, mutate `Kp` and the maps to/from
the completion so that `Kp` has element precision `new_prec`.

NOTE: This method will sharpen the base field of `Kp`, which will affect anything with a 
reference to it. The precision can only be increased by `sharpen!`.
"""
function sharpen!(Kp::EisensteinField, P::NfAbsOrdIdl, completion_maps, new_prec)

    # TODO: The sharpening methods can be improved a lot with a decent caching strategy.
    @assert P.norm == prime(base_field(Kp))

    inj = completion_maps.f
    lif = completion_maps.g
    K   = domain(completion_maps)
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

    function construct_defining_polynomial()
        N = underdetermined_solve_first(local_basis_lift, matrix([coordinates(pi^e)]))
        RX,X = PolynomialRing(Kp_unram,"X")
        return X^e + sum(X^i*delta_p^j * N[i*f + j + 1] for j=0:f-1 for i=0:e-1)
    end

    gnew = construct_defining_polynomial()

    # Sharpen the base field and defining polynomial.
    sharpen_base!(Kp, new_prec)
    sharpen!(Kp, gnew, new_prec)

    ####
    # Sharpen the inclusion map
    #
    # TODO: Things that should be cached:
    # -- coefficients defining the image of the number field generator.

    # Update delta_p to be the new generator.
    delta_p = unram_gen(Kp_unram)
    
    function image_of_nf_gen(a)
        avec = matrix(FlintZZ, length(coeffs(a)), 1, coeffs(a))        
        N = underdetermined_solve_first(local_basis_lift, avec)

        return sum(gen(Kp)^i*delta_p^j * N[i*f + j + 1] for j=0:f-1 for i=0:e-1)
    end
    img_nf_gen = image_of_nf_gen(gen(K))
    
    # Reconstruct the forward map, embedding $K$ into its completion.
    function inj(a::nf_elem)
        return sum(coeffs(a)[j+1] * img_nf_gen^j for j=0:degree(K)-1)
    end
    
    # Update the completion maps 
    completion_maps.f = inj
    return
end

@doc Markdown.doc"""
    sharpen!(K::FlintLocalField, new_prec)
Change the `prec_max` field of `K`. Effectively, this increases the precision of new elements
created in `K`.
"""
function sharpen!(K::FlintPadicField, new_prec)
    K.prec_max = new_prec
    return
end

function sharpen!(K::FlintQadicField, new_prec)
    K.prec_max = new_prec
    return
end

@doc Markdown.doc"""
    sharpen_base!(K::EisensteinField, new_prec)
Apply `sharpen!` to the base field of `K`.
"""
function sharpen_base!(K::EisensteinField, new_prec)
    Q = base_ring(K)
    @assert typeof(Q) <: FlintLocalField
    sharpen!(Q, new_prec)
    return
end


#####
# Sharpen via polynomial (RootSharpenCtx)

#=
The point of this interface is to allow the sharpening of the completion map to a field 
by fixing the defining polynomials and sharpening the root. 
=#

# Reminicent of the "qAdicConj" context, but more general.
mutable struct RootSharpenCtx
    polynomial             # Should be an exact polynomial
    #derivative_polynomial # cached derivative of polynomial. Not clear if this should be cached.
    field                  # field of definition of root
    root                   # the root of a polynomial
    precision              # current precision of the root

    function RootSharpenCtx(polynomial, root)
        ctx = new()
        ctx.polynomial = change_base_ring(FlintZZ, polynomial)
        ctx.field = parent(root)
        ctx.root  = root 
        ctx.precision = precision(root)
        return ctx
    end
end

function sharpen!(maps, ctx::RootSharpenCtx, n)

    # TODO: also sharpen lifting map properly.

    inj = maps.f
    
    f  = ctx.polynomial
    ctx.precision > n  && error("Cannot sharpen to lower precision.")
    ctx.precision == n && return
    ctx.precision = n
    
    # sharpen field defining polynomials trivially
    K = ctx.field
    sharpen_base!(K,n)
    setprecision!(K.pol, n)
    K.prec_max = n
    
    # Then newton lift the roots
    # Hope it is continuous.
    test = newton_lift!(f, ctx.root)

    display(test)
    display(precision(ctx.root))
    
    # Now we need to sharpen the maps...
    img_nf_gen = ctx.root
    display(precision(img_nf_gen))
    
    # Construct the forward map, embedding $K$ into its completion.
    # The map is determined by the image of the number field generators.
    function inj(a::nf_elem)
        return sum(coeffs(a)[j+1] * img_nf_gen^j for j=0:degree(parent(a))-1)
    end

    # TODO: Add sharpening of lifting map so that things are compatible.

    maps.f = inj
    
    return
end

function setprecision!(a::eisf_elem, N)
    for c in coeffs(a)
        setprecision!(c, N)
    end
    return
end

                       

function setprecision!(f::AbstractAlgebra.Generic.Poly{<:NALocalFieldElem}, N::Int)
  for i=1:length(f)
    setprecision!(f.coeffs[i], N)
  end
  return
end


#########################################################################################
#
#   Completions
#
#########################################################################################

#=
Commentary on precisions:

See the org file.
=#

# TODO: Add branching based on optimization parameter.
# TODO: Add various sharpening contexts.
function completion(K::NumField{T} where T, P::NfOrdIdl; prec=10, skip_map_inverse=false)
    if ramification_index(P) == 1
        return unramified_completion(K, P, skip_map_inverse=skip_map_inverse)
    else
        return ramified_completion(K, P, prec=prec, skip_map_inverse=skip_map_inverse)
    end
end

function ramified_completion(K::NumField{T} where T, P::NfOrdIdl; prec=10, skip_map_inverse=false)

    # Determine a polynomial over Kp_unram which annihilates pi.

    # The method used here is to find a solution to `g(b) mod P^prec`, where
    # the residue image of `b` is a (Conway) generator for the residue field.

    # This is definitely not the best algorithm. In the unramified, non-index-divisor
    # case, computing powers of `P` is trivial. However, in the other (likely important)
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
    function conway_gen_lift()
        BO = basis(max_order)

        A = matrix(coeffs.(res.(BO)))
        b = matrix(coeffs(gen(k)))

        y = underdetermined_solve_first(A,b)

        # This is the lift of the generator of the Qadic subfield of the completion.
        return sum([a*b for (a,b) in zip(BO,lift(y))])
    end

    delta = conway_gen_lift()
    display(delta)    
    delta_p = unram_gen(Kp_unram)

    # Construct the integer matrix encoding coordinates with respect to pi, delta modulo P^N.
    # Basis elements for the local field and the ideal P^prec
    BKp = [pi^i*delta^j for j=0:f-1 for i=0:e-1]
    BPn = basis(P^prec)
    local_basis_lift = hcat(matrix(coordinates.(BKp)), matrix(coordinates.(BPn)))

    function construct_defining_polynomial()
        N = underdetermined_solve_first(local_basis_lift, -matrix([coordinates(pi^e)]))
        RX,X = PolynomialRing(Kp_unram,"X")
        
        return X^e + sum(X^i*delta_p^j * N[i*f + j + 1] for j=0:f-1 for i=0:e-1 )
    end

    ##################################################
    # Build the completion structure.
    g = construct_defining_polynomial()
    display(g)
    Kp, Y = EisensteinField(g,"_\$")

    ##################################################
    # Compute the maps
    
    function image_of_nf_gen(a)
        avec = matrix(FlintZZ, length(coeffs(a)), 1, coeffs(a))        
        N = underdetermined_solve_first(local_basis_lift, avec)

        return sum(Y^i*delta_p^j * N[i*f + j + 1] for j=0:f-1 for i=0:e-1)
    end

    img_nf_gen = image_of_nf_gen(a)
    display("Printing nf gen image: $img_nf_gen")
    
    # Construct the forward map, embedding $K$ into its completion.
    # The map is determined by the image of the number field generators.
    function inj(a::nf_elem)
        return sum(coeffs(a)[j+1] * img_nf_gen^j for j=0:d-1)
    end

    # Construct the lifting map, from the completion back to $K$. The map is determined by
    # the lifts of the generators of the ramified/unramified parts of the eisenstein extension.
    function lif(x::eisf_elem)
        iszero(x) && return zero(K)
        qadic_coeffs = coeffs(x)
        return sum(pi^i * delta^j * K(sym_lift(coeffs(qadic_coeffs[i])[j+1]))
                   for j=0:f-1 for i=0:length(qadic_coeffs)-1 )        
    end

    # TODO: Cache the sharpening data in some way.

    #TODO: Move to proper tests
    # Sanity check the returns
    @assert iszero(change_base_ring(Kp,K.pol)(inj(gen(K))))
    @assert lif(inj(gen(K) + 1)) == gen(K) + 1
    return Kp, MapFromFunc(inj, lif, K, Kp)
end

function lift_root(f::fmpz_poly, a::nf_elem, o::nf_elem, p::fmpz, n::Int)
  #f(a) = 0 mod p, o*f'(a) = 1 mod p, want f(a) = 0 mod p^n
  k = 1
  while k < n
    p *= p
    k *= 2

    pa = [one(a)]
    while length(pa) <= degree(f)
      push!(pa, pa[end]*a)
      mod_sym!(pa[end], p)
    end
    fa  = sum(coeff(f, i-1) * pa[i] for i=1:length(pa))
    fsa = sum(coeff(f, i) * i * pa[i] for i=1:length(pa)-1)  
    o = o*(2-fsa*o)
    a = a - fa*o
    mod_sym!(o, p)
    mod_sym!(a, p)
  end
  return a
end


@doc Markdown.doc"""
    completion(K::AnticNumberField, P::NfOrdIdl) -> FlintQadicField, Map{AnticNumberField -> FlintQadicField}
The completion of $K$ wrt to the topology induced by the valuation at $P$. $P$ needs
to be unramifed.
The map giving the embedding of $K$ into the completion, admits a pointwise pre-image to obtain a lift.
Note, that the map is not well defined by this data: $K$ will have $\deg P$ many embeddings.
"""
function unramified_completion(K::AnticNumberField, P::NfOrdIdl; prec=10, skip_map_inverse=false)
    #non-unique!! will have deg(P) many
    p = minimum(P)
    pi = P.gen_two.elem_in_nf
    predicate = (Kp,inj) -> valuation(inj(pi)) > 0
    
    return unramified_completion(K, p, predicate; prec=prec, skip_map_inverse=skip_map_inverse)
end

# Find the first unramified completion over `p` such that `predicate(Kp,inj)` is `true`.
function unramified_completion(K::AnticNumberField, p::fmpz, predicate;
                               prec=10, skip_map_inverse=false)

    C = qAdicConj(K, Int(p))
    R = roots(C.C, prec)
    display(R)
    
    for rt in R
        (Kp, inj) = unramified_completion(K, rt, prec=prec, skip_map_inverse=true)
        if predicate(Kp,inj)
            return unramified_completion(K, rt, prec=prec, skip_map_inverse=skip_map_inverse)
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
    @assert 0<i<= degree(K)
    return unramified_completions(K, fmpz(p))[i]
end

completion(K::AnticNumberField, p::Integer, i::Int) = completion(K, FlintZZ(p), i)


# Returns the unramified completions of $K$ over the prime $p$.
function unramified_completions(K::AnticNumberField, p::fmpz; prec=10)
    # Since in the unramified case we complete via factorizations, we first
    # construct the roots data needed to define/sharpen the extension.
    C = qAdicConj(K, Int(p))

    #### Insertion of old "conjugates(gen(K), C, all = true, flat = false)[i]" logic #####
    # This seems to be the line where the roots are actually computed.
    R = roots(C.C, prec)

    display(R)
    
    return [unramified_completion(K, rt, prec=prec) for rt in R]
end

function unramified_completions(K::AnticNumberField, p::Integer; prec=10)
    unramified_completions(K::AnticNumberField, FlintZZ(p); prec=10)
end

# Give the unramified completion where gen(K) is mapped to `gen_img`. It is assumed that
# gen_img satisfied `change_base_ring(Kp, K.pol)(gen_img) == 0`.
function unramified_completion(K::AnticNumberField, gen_img::qadic; prec=10, skip_map_inverse=false)

    p = prime(parent(gen_img))
    
    #### Resume insertion of old "conjugates(gen(K), C, all = true, flat = false)[i]" logic #####
    Zx = PolynomialRing(FlintZZ, cached = false)[1]

    # The element `a` is replaced by a polynomial. It is assumed that the variable
    # in the polynomial is identified with the generator of the number field.    
    function inj(a)
        @assert parent(a) == K
        d = denominator(a)
        f = Zx(d*a)
        return inv(parent(gen_img)(d))*f(gen_img)
    end    
    ### End insertion.


    if !skip_map_inverse
        
        # function inj(a::nf_elem)
        #   return conjugates(a, C, precision(parent(ca)))[i]
        # end
        # gen(K) -> conj(a, p)[i] -> a = sum a_i o^i
        # need o = sum o_i a^i
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

        # Construct the Conway root in the number field.
        a = K()
        for i=1:d
            _num_setcoeff!(a, i-1, lift(s[i,1]))
        end

        # Construct the derivative of the Conway root in the number field.
        f = defining_polynomial(parent(gen_img), FlintZZ)
        fso = inv(derivative(f)(gen(R)))
        o = matrix(GF(p), d, 1, [coeff(fso, j-1) for j=1:d])
        s = solve(m, o)
        b = K()
        for i=1:d
            _num_setcoeff!(b, i-1, lift(s[i,1]))
        end

        # Lift the data from the residue field back to Qp.
        c = lift_root(f, a, b, p, 10)
        pc = fmpz(10)
        lif = function(x::qadic) 
            if iszero(x)
                return K(0)
            end
            if precision(x) > pc
                #XXX this changes (c, pc) inplace as a cache
                #probably should be done with a new map type that can
                #store c, pc on the map.
                d = lift_root(f, a, b, p, precision(x))

                # Manipulate the values c, pc by the implicit pointers stored inside this function.
                # Unfortunately this cannot be done at the julia level...
                ccall((:nf_elem_set, :libantic), Nothing,
                      (Ref{nf_elem}, Ref{nf_elem}, Ref{AnticNumberField}), c, d, K)
                ccall((:fmpz_set_si, :libflint), Nothing, (Ref{fmpz}, Cint), pc, precision(x))

            elseif precision(x) < pc
                d = mod_sym(c, p^precision(x))
            else
                d = c
            end
            n = x.length
            r = K(lift(coeff(x, n-1)))
            while n > 1
                n -= 1
                r = r*d + lift(coeff(x, n-1))
            end
            return r#*K(p)^valuation(x)
        end
    else
        lif(x::qadic) = error("Completion lift map definition was skipped during initialization.")
    end
    
    return parent(gen_img), MapFromFunc(inj, lif, K, parent(gen_img))
end

