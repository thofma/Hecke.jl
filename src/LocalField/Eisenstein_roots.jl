

# The root finding algorithm in this file is based off of Panayi's algorithm,
# a description of which can be found here:
#=
\bib{MR1836924}{article}{
   author={Pauli, Sebastian},
   author={Roblot, Xavier-Fran\c{c}ois},
   title={On the computation of all extensions of a $p$-adic field of a
   given degree},
   journal={Math. Comp.},
   volume={70},
   date={2001},
   number={236},
   pages={1641--1659},
   issn={0025-5718},
   review={\MR{1836924}},
   doi={10.1090/S0025-5718-01-01306-0},
}
=#

@doc Markdown.doc"""
    number_of_roots(K, f)
Given an eisenstein extension `K` and a polynomial $f \in K[x]$, return the number of roots of `f` defined over `K`.
"""
function number_of_roots(f::Hecke.Generic.Poly{<:NALocalFieldElem})

    K = base_ring(f)
    k, mp_struct = ResidueField(K)

    # Unpack the map structure to get the maps to/from the residue field.
    res  = mp_struct.f
    lift = mp_struct.g
    
    x = gen(parent(f))
    pi = uniformizer(K)
    C = [fprimitive_part(f)]
    m = 0

    while !isempty(C)
        c = pop!(C)        
        cp = map_coeffs(res, c)
        Rfp = parent(cp)
        rts = roots(cp)
        
        for rt in rts
            
            h = fprimitive_part( c(pi*x + lift(rt)) )
            hp = map_coeffs(res, h)
            
            if degree(hp) == 1
                m += 1
            elseif degree(hp) > 1
                push!(C, h)        
            end
        end

        if length(C) >= degree(f)
            error("Number of computed factors has exceeded the degree.")
        end
    end
    return m
end

function number_of_roots(f::Hecke.Generic.Poly{<:NALocalFieldElem}, K::NALocalField)
    return number_of_roots(change_base_ring(K,f))
end


###############################################################################
#
#   Newton Lifiting methods.
#
###############################################################################


function newton_lift(f::Hecke.Generic.Poly{T}, r::T, num_input_correct_digits=1::Integer) where T<:NALocalFieldElem
    rt = deepcopy(r)
    return newton_lift!(f, rt, num_input_correct_digits)
end

@doc Markdown.doc"""
    newton_lift!(f::Hecke.Generic.Poly{T}, r::T, num_input_correct_digits=1) where T<:NALocalFieldElem
Mutates `r` via newton iteration (Hensel lifting) such that `f(r)==zero(parent(r))`. The root `r` is a *forward solution* to the problem, given at the maximum possible precision. The third argument specifies the number of presently known digits of the root.

The output of `newton_lift!` is the condition number of the root, indicating the size of the neighbourhood `U` around `r` such that $f(U) \subseteq zero(parent(r))$. It is the valuation of the derivative of `f` at the root.
"""
function newton_lift!(f::Hecke.Generic.Poly{T}, r::T, num_input_correct_digits=1::Integer) where T<:NALocalFieldElem

    # The algorithm is a standard double lifting algorithm where the root and
    # the value of 1/dfK(r) are lifted simultaneously.
    
    K = parent(r)
    base_ring(parent(f)) != K && error("Base fields not compatible for newton_lift.")  
    N = precision(K)

    @assert num_input_correct_digits > 0
    @assert precision(r) >= num_input_correct_digits

    # Initialize the derivative of the function at `r`.
    fK  = deepcopy(f)
    dfK = derivative(f)
    df_at_r_inverse = dfK(r)
    
    @assert !iszero(df_at_r_inverse)    
    df_at_r_inverse = inv(df_at_r_inverse)
    condition_number = valuation(df_at_r_inverse)

    if valuation(fK(r)) + 2*valuation(df_at_r_inverse) < 0
        error("Newton iteration does not converge at $r at given precision.")
    end

    # Allocate some memory.
    two = K(2)
    expr_container = K()
    current_precision = num_input_correct_digits
        
    while true
        
        current_precision =  2*current_precision
        current_precision <= 0 && error("Integer overflow error in precision quantity.") 
        
        setprecision!(r, current_precision)
        setprecision!(df_at_r_inverse, current_precision)

        test = deepcopy(df_at_r_inverse)
        
        mul!(expr_container, fK(r), df_at_r_inverse)
        sub!(r, r, expr_container)

        if current_precision > N
            break
        end
        
        # Update the value of the derivative. Value of df_at_r_inverse equvalent to
        #     df_at_r_inverse*(2-dfK(r)*df_at_r_inverse)
        # after exression.
        mul!(expr_container, dfK(r), df_at_r_inverse)
        sub!(expr_container, two, expr_container)        
        mul!(df_at_r_inverse, df_at_r_inverse, expr_container)

        # Catch FLINT related bugs.
        @assert test*(2-dfK(r)*test) == df_at_r_inverse
    end

    return r, condition_number
end

function newton_lift!(f::fmpz_poly, r::NALocalFieldElem, num_input_correct_digits=1::Integer)
    K = parent(r)
    newton_lift!(change_base_ring(K, f), r, num_input_correct_digits)
end

function newton_lift(f::fmpz_poly, r::NALocalFieldElem, num_input_correct_digits=1::Integer)
    K = parent(r)
    return newton_lift(change_base_ring(K, f), r, num_input_correct_digits)
end

###############################################################################
#
#   Root finding methods.
#
###############################################################################

@doc Markdown.doc"""
    integral_roots(f::Hecke.Generic.Poly{<:Hecke.NALocalFieldElem})
Return an array of tuples `(root, multiplicity, condition_number)`, where `iszero(f(root))`
for each root.
"""
function integral_roots(f::Hecke.Generic.Poly{<:Hecke.NALocalFieldElem})

    iszero(f) && throw(DomainError(f, "Cannot compute roots of the zero polynomial."))
    
    K = base_ring(parent(f))
    k, mp_struct = ResidueField(K)

    # Unpack the map structure to get the maps to/from the residue field.
    res  = mp_struct.f
    lift = mp_struct.g

    x  = gen(parent(f))
    pi = uniformizer(K)
    roots_type = elem_type(K)
    
    fprim = fprimitive_part(f)
    fp = map_coeffs(res, fprim) # type instability here.

    rts = roots(fp)
    
    if length(rts)==0
        # There are no roots in the padic unit disk        
        return roots_type[]
        
    elseif degree(fp) == 1
        # There is exactly one root, which can be Hensel lifted
        rr = lift(rts[1])
        rt = newton_lift(fprim,rr)
        return [(rt[1], 1, rt[2])]

    elseif iszero(coeff(fprim, 0))
        
        # TODO: Prove the following lemma:
        # `f` has a root of multiplicity >= m if and only if some recursive call `g` is
        # divisible by `x^m`. Moreover, the first recursive call for which this happens
        # is the correct multiplicity.

        rt_mul = findfirst(!iszero, coefficients(f))::Int - 1
        cond_num = precision(K) // rt_mul
        f_new = polynomial([coeff(f,i) for i=(rt_mul+1):degree(f)])
        
        return vcat([(zero(K), rt_mul, cond_num)], integral_roots(f_new))
    else
        # There are multiple roots in the unit disk. Zoom in on each.
        roots_out = roots_type[]
        for beta in rts
            beta_lift = lift(beta)
            new_f = fprim(pi*x + beta_lift)
                        
            roots_near_beta = integral_roots(new_f)
            roots_out = vcat(roots_out, [(pi*r[1] + beta_lift, 1, r[2]) for r in roots_near_beta])
        end
        
        return roots_out
    end
    error("Etwas hat scheif gelaufen.")
end

import Hecke.roots
function roots(f::Hecke.Generic.Poly{<:Hecke.NALocalFieldElem})
    K = base_ring(parent(f))
    pi = uniformizer(K)
    x = gen(parent(f))
    
    Ov_roots   = integral_roots(f,K)
    outside_Ov_roots = integral_roots(reverse(f)(pi*x), K)
    filter!(r->r!=K(0), outside_Ov_roots)
    return vcat(Ov_roots, [inv(rt) for rt in outside_Ov_roots])
end

function roots(f, K::Hecke.Field)
    return roots(change_base_ring(K,f))
end

function integral_roots(f, K::Hecke.Field)
    return integral_roots(change_base_ring(K,f))
end

function any_root(f::fmpz_poly, Q::FlintQadicField)
    # NOTE: Both a Hensel factorization and a newton iteration are required to refine the roots,
    #       since the Hensel context only works for polynomials over ZZ.
    k, mk = ResidueField(Q)
    rts = roots(f, k)
    isempty(rts) && throw(DomainError((f,Q), "Polynomial has no roots in $Q."))
    
    return newton_lift(f, preimage(mk, rts[1]))
end
