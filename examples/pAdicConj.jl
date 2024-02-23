module pAdicConj


#goto qAdicConj...

using Hecke

#= kept for the comments

function mult_syzygies_units(a::Vector{FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}})
  p = next_prime(2^10) #experimentally, the runtime is dominated by
         # log which in case is dominated by the a^(p^n-1) in the 1st step
         # thus try p smaller..., ideally also try n smaller...
         # also, see comments at _log
  u = FacElem{AbsSimpleNumFieldElem, AbsSimpleNumField}[]
  la = [conjugates_pAdic_log(e, p, 300) for e = a] #can loose precision
    # needs to be traced
    # precision needs to be updated.
  n = ncols(la[1])
  Qp = base_ring(la[1])
  lu = matrix(Qp, 0, n, [])
  for i=1:length(la)
    if iszero(la[i])
      println("torsino at $i\n")
      continue
    end
    lv = vcat(lu, la[i])
    k = Hecke._left_kernel_basis(lv)
    @assert length(k) < 2
    if length(k) == 0
      println("new at $i")
      push!(u, a[i])
      lu = vcat(lu, la[i])
    else # length == 1 extend the module
      r = [lift_reco(FlintQQ, x, reco = true) for x = k[1]]
      #lift can fail if precision wrong.
      #or at least result is (can be) garbage
      #= bound on relation
        u has s independent units (independence is failproof p-adically)
        v is new and (probably, up to verification of the relation) dependent
        Then <u, v> = <e_1, .., e_s> where the e_'s are unknown.
        we have u = U(e_1, ..., e_n) for U in Z^(s x s)
                v = V(e_1, ..., e_n) vor V in Z^(1 x s)
        Over Q: v = x(u_1, ..., u_s) thus
            V(e_1, ..., e_s) = xU(e_1, ..., e_s)
        and, since the e_i are independent
            V = xU
        Cramer's rule
            x_i = det(U_1, ..., U_i-1, V, ... U_s) / det(U)
        and we need bounds for the determinants.
        As an example, det U
        det U = <e_1, ..., e_s> : <u_1, ..., u_s>
        and using universal lower bounds on the size of units (Dobrowski)
        and the successive minimal, we can get a lower bound on the
        regulator of <e_i>. Hadramat gives an upper bound on reg(<u_i>)
        (regulator in the sense of lattice disciminant)

        Think: can we use the p-adic regulator to help???
               possibly increase precision until we either have
               indepence or a relation
               ignore bounds?
      =#
      d = reduce(lcm, map(denominator, r))
      gamma = [FlintZZ(x*d) for x = r]
      #technically, this relations needs to be verified.
      #=
        we have a relation mod p^k, which means
          e = prod gamma[i]*u[i]
        has all logarithms == 0 mod p^k
        which should mean Norm(e) = product of the local norms
                                  = prod of exp(trace(components))
        For p large enough (larger than precision),
        val(exp(x)) = val(1-x) I think
        so
                                  >= p^(k* # primes) = p^l
        Now, either e is torsion (ie. logs identically 0) or
        not, but then arithmetic means:
        N(e) <= (T_2(e)^(1/2)/n)^n
        implies a non-trivial lower bound on the T_2:
        T_2(e) >= (np^(l/n))^2 =: B
        If T_2(e) < B, then e is torsion. B is MUCH larger than
        Dobrowski. Hence this can be evaluated with low precision.

        Not done.
      =#
      @assert reduce(gcd, gamma) == 1 # should be a primitive relation
      _, U = hnf_with_transform(matrix(FlintZZ, length(r), 1, gamma))
      U = inv(U)
      U = sub(U, 1:nrows(U), 2:ncols(U))
      #new basis is the cols of U
      push!(u, a[i])
      u = Hecke._transform(u, U)
      lu = U'*lv
    end
  end
  return u
end

=#

function non_torsion_lower_bound(R::AbsSimpleNumFieldOrder, B::Int = 2*degree(R))
  L = Hecke.enum_ctx_from_ideal(1*R, zero_matrix(FlintZZ, 0, 0))
  n = degree(R)
  i = B
  while true
    #lat enum is wrong. Or maybe rounding funnily:
    # try on wildanger_field(13, 17) and observe the vectors found...
    # in particular 1 is not (reliably) found
    @show s = Hecke.enum_ctx_short_elements(L, i*L.d)
    #remove torsion
    if nrows(s) > 5
      M = minimum([t2(R(collect(sub(s, i:i, 1:n)))) for i=1:nrows(s)])
      j = n-2
      return (n-j)/4*acosh((M-j)/(n-j))^2
    end
    @show i += 1
  end
end

function unit_lower_bound(R::AbsSimpleNumFieldOrder, B::Int = 2*degree(R))
  L = Hecke.enum_ctx_from_ideal(1*R, zero_matrix(FlintZZ, 0, 0))
  n = degree(R)
  i = B
  while true
    s = Hecke.enum_ctx_short_elements(L, i*L.d)
    #remove torsion!!! now that \pm 1 is actually found
    e = [R(collect(sub(s, i:i, 1:n))) for i=1:nrows(s)]
    u = [x for x in e if is_unit(x)]
    if nrows(s) > 5
      if length(u) == 0
        R = parent(t2(e[1]))
        @show M = R(i)
      else
        @show M = minimum([t2(x) for x = u])
      end
      j = n-2
      return (n-j)/4*acosh((M-j)/(n-j))^2, u
    end
    @show i += 1
  end
end


function regulator_lower_bound(R::AbsSimpleNumFieldOrder, B::Int = 2*degree(R))
  Ms, _ = unit_lower_bound(R, B)
  r1, r2 = signature(R)
  r = r1+r2-1
  n = degree(R)
  return Ms^r * 2^r2 /n / Hecke.hermite_constant(r)
end

end
