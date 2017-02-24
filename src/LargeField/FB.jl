#Aim: have map operate on FB
#

function induce_image(A::NfMaxOrdIdl, S::Map)
  O = order(A)
  K = O.nf
  B = ideal(order(A), A.gen_one, O(S(K(A.gen_two)))) # set is prime, norm, ...
  # whatever is known, transfer it...possibly using S as well...
  return B
end

@doc """
  compose_mod(x::nmod_poly, y::nmod_poly, z::nmod_poly) -> nmod_poly

  Compute x(y) mod z
""" ->
function compose_mod(x::nmod_poly, y::nmod_poly, z::nmod_poly)
  check_parent(x,y)
  check_parent(x,z)
  r = parent(x)()
  ccall((:nmod_poly_compose_mod, :libflint), Void,
          (Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{nmod_poly}), &r, &x, &y, &z)
  return r
end

@doc """
  taylor_shift(x::nmod_poly, r::UInt) -> nmod_poly

  Compute x(t-c)
""" ->
function taylor_shift(x::nmod_poly, c::UInt)
  r = parent(x)()
  ccall((:nmod_poly_taylor_shift, :libflint), Void,
          (Ptr{nmod_poly}, Ptr{nmod_poly}, UInt), &r, &x, c)
  return r
end

function induce(FB::Hecke.NfFactorBase, A::Map) 
  K = domain(A)
  f = A(gen(K)) # esentially a polynomial in the primitive element

  O = order(FB.ideals[1])
  prm = Array{Tuple{Int, Int}, 1}()

  for p in FB.fb_int.base
    FP = FB.fb[p]
    if length(FP.lp) < 3 || is_index_divisor(O, p) || p > 2^60
      lp = [x[2] for x = FP.lp]
      for (i, P) in FP.lp 
        Q = induce_image(P, A)
        id = findfirst(lp, Q)
        push!(prm, (i, FP.lp[id][1]))
      end
    else
      px = PolynomialRing(ResidueRing(FlintZZ, p), "x")[1]
      fpx = px(f)
      gpx = px(K.pol)
      #idea/ reason
      # if p is no index divisor, then a second generator is just
      #   an irreducible factor of gpx (Kummer/ Dedekind)
      # an ideal is divisible by P iff the canonical 2nd generator of the prime ideal
      # divides the 2nd generator of the target (CRT)
      # so 
      lp = [gcd(px(K(P[2].gen_two)), gpx) for P = FP.lp]
      # this makes lp canonical (should be doing nothing actually)

      for (i,P) in FP.lp
        hp = px(K(P.gen_two))
        if degree(hp)==1
          im = fpx + coeff(hp, 0)
        else
          im = compose_mod(hp, fpx, gpx)
          # the image, directly mod p...
        end  
        im = Hecke.gcd!(im, gpx, im)
        # canonical
        push!(prm, (i, FP.lp[findfirst(lp, im)][1]))
        # and find it!
      end
    end
  end
  sort!(prm, lt=(a,b) -> a[1] < b[1])
  G = PermutationGroup(length(prm))
  return G([x[2] for x = prm])
end

#= implementation from Butler's Fundamntal Algorithm for Permutation Groups
  Algo 4: Dimino
  Tested for cyclic groups - unfortunately only.
  I still need to generate other input
=#  
#function orbit_in_FB(op::Array{Tuple{Map, Nemo.perm}, 1}, a::nf_elem, s::SmatRow)
function orbit_in_FB(op::Array, a::nf_elem, s::SmatRow)
  function op_smat(n::SmatRow, p::Nemo.perm)
    return typeof(n)([(p[i], v) for (i,v) = n])
  end

  Ss = Dict{typeof(s), nf_elem}()
  Ss[s] = a
  # start with the cyclic group be op[1]
  n = op_smat(s, op[1][2])
  b = a
  while n != s
    b = op[1][1](b)
    Ss[n] = b
    n = op_smat(n, op[1][2])
  end

  for i=2:length(op) 
    n = op_smat(s, op[i][2])
    if haskey(Ss, n)
      continue
    end
    old = collect(Ss)
    for (n, b) in old # one redundant - step
      Ss[op_smat(n, op[i][2])] = op[i][1](b)
    end
    while true
      done = true
      for j = 1:length(op)
        nn = op_smat(n, op[j][2])
        if haskey(Ss, nn)
          continue;
        end
        done = false
        n = nn
        for (n,b) in old
          Ss[op_smat(n, op[j][2])] = op[j][1](b)
        end
      end
      if done
        break
      end
    end
  end
  return Ss
end

