
#TODO: Update citation.

# The root finding algorithm in this file is based off of Panayi's algorithm,
# a description of which can be found here:  "krasner.pdf".

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

############################################################

my_setprecision!(f,N) = f


# Should use a precision access function rather than a "__.N".

#TODO: See if newton lift needs to be modified in characteristic `p`.
function newton_lift(f::Hecke.Generic.Poly{T}, r::T, num_input_correct_digits=1::Integer) where T<:NALocalFieldElem
    rt = deepcopy(r)
    cond = newton_lift!(f, rt, num_input_correct_digits)
    return rt, cond
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
        display(current_precision)
        
        current_precision =  2*current_precision
        current_precision <= 0 && error("Integer overflow error in precision quantity.") 
        
        setprecision!(r, current_precision)
        setprecision!(df_at_r_inverse, current_precision)

        test = deepcopy(df_at_r_inverse)
        display(df_at_r_inverse)
        
        # NOTE: The correct functioning of this algorithm depends on setprecision!
        # not obliterating the extra digits automatically.
        my_setprecision!(fK, current_precision)
        my_setprecision!(dfK, current_precision)

        mul!(expr_container, fK(r), df_at_r_inverse)
        sub!(r, r, expr_container)

        display(fK(r))
        
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

    return condition_number
end

function newton_lift!(f::fmpz_poly, r::NALocalFieldElem, num_input_correct_digits=1::Integer)
    K = parent(r)
    newton_lift!(change_base_ring(K, f), r, num_input_correct_digits)
end

function newton_lift(f::fmpz_poly, r::NALocalFieldElem, num_input_correct_digits=1::Integer)
    K = parent(r)
    return newton_lift(change_base_ring(K, f), r, num_input_correct_digits)
end


#=
function newton_lift(f::fmpz_poly, r::NALocalFieldElem)
  Q = parent(r)
  n = Q.prec_max
  i = n
  chain = [n]
  while i>2
    i = div(i+1, 2)
    push!(chain, i)
  end
  fs = derivative(f)
  qf = change_base_ring(Q, f, cached = false)
  qfs = change_base_ring(Q, fs, cached = false)
  o = Q(r)
  o.N = 1
  s = qf(r)
    
  setprecision!(qfs, 1)
  o = inv(qfs(o))
  @assert r.N == 1
  for p = reverse(chain)
    r.N = p
    o.N = p
    Q.prec_max = r.N
    setprecision!(qf, r.N)
    setprecision!(qfs, r.N)
    r = r - qf(r)*o
    if precision(r) >= n
      Q.prec_max = n
      return r
    end
    o = o*(2-qfs(r)*o)
  end
end
=#

# TODO: XXX: f is assumed to be "square-free".
function integral_roots(f::Hecke.Generic.Poly{<:Hecke.NALocalFieldElem})

    K = base_ring(parent(f))
    k, mp_struct = ResidueField(K)

    # Unpack the map structure to get the maps to/from the residue field.
    res  = mp_struct.f
    lift = mp_struct.g

    x = gen(parent(f))
    pi = uniformizer(K)
    roots_type = elem_type(K)
    
    fprim = fprimitive_part(f)
    fp = map_coeffs(res, fprim)

    rts = roots(fp)
    
    if length(rts)==0
        # There are no roots in the padic unit disk        
        return roots_type[]
        
    elseif degree(fp) == 1
        # There is exactly one root, which can be Hensel lifted
        rr = lift(rts[1])
        return [newton_lift(fprim,rr)]

    else
        # There are multiple roots in the unit disk. Zoom in on each.
        roots_out = roots_type[]
        for beta in rts
            beta_lift = lift(beta)
            roots_near_beta = integral_roots( fprim(pi*x + beta_lift) )
            roots_out = vcat(roots_out, [pi*r + beta_lift for r in roots_near_beta] )
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
