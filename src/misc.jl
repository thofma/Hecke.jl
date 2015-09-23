import Base: isprime, dot, convert, isless, log
export basis, basis_mat, simplify_content, element_reduce_mod, inv_basis_mat,
       pseudo_inverse, denominator, submat, index, degree, sub,
       next_prime, element_is_in_order, valuation, is_smooth, is_smooth_init,
       discriminant, dot, hnf, _hnf, modular_hnf, representation_mat,
       signature, howell_form!, howell_form, _hnf_modular, isless


function basis_rels(b::Array{nf_elem, 1}, c; bd::fmpz = fmpz(10^35), no_p::Int = 4, no_rel::Int = 10000, no_coeff::Int = 4 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = fmpz(1)
  for i=1:no_rel
    zero!(a)
    for j=1:no_coeff
      cf = rand([-1, 1])
      p  = rand(1:nb)
      if cf==1
        Nemo.add!(a, a, b[p])
      else
        Nemo.sub!(a, a, b[p])
      end
    end
    n = norm_div(a, one, no_p)
    if cmpabs(num(n), bd) <= 0 
      if class_group_add_relation(c, a, n, one)
        a = b[1].parent()
      end
    end
  end
end


function rels_stat(b::Array{hecke.nf_elem, 1}; no_p = 4, no_rel::Int = 10000, no_coeff::Int = 4 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = fmpz(1)

  stat = Dict{Int, Int}()
  for i=1:no_rel
    zero!(a)
    for j=1:no_coeff
      p  = rand(1:nb)
      Nemo.add!(a, a, b[p])
    end
    n = norm_div(a, one, no_p)
    k - Int(round(log(abs(n))))
    if isdefined(stat, k)
      stat[k] += 1
    else
      stat[k] = 1
    end
  end
  return stat
end

