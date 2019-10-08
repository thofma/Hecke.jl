#Aim: have map operate on FB

@doc Markdown.doc"""
    compose_mod(x::nmod_poly, y::nmod_poly, z::nmod_poly) -> nmod_poly

  Compute x(y) mod z
"""
function compose_mod(x::nmod_poly, y::nmod_poly, z::nmod_poly)
  check_parent(x,y)
  check_parent(x,z)
  r = parent(x)()
  ccall((:nmod_poly_compose_mod, :libflint), Nothing,
          (Ref{nmod_poly}, Ref{nmod_poly}, Ref{nmod_poly}, Ref{nmod_poly}), r, x, y, z)
  return r
end

function compose_mod(x::gfp_poly, y::gfp_poly, z::gfp_poly)
  check_parent(x,y)
  check_parent(x,z)
  r = parent(x)()
  ccall((:nmod_poly_compose_mod, :libflint), Nothing,
          (Ref{gfp_poly}, Ref{gfp_poly}, Ref{gfp_poly}, Ref{gfp_poly}), r, x, y, z)
  return r
end


@doc Markdown.doc"""
    taylor_shift(x::nmod_poly, c::UInt) -> nmod_poly

  Compute x(t-c)
"""
function taylor_shift(x::nmod_poly, c::UInt)
  r = parent(x)()
  ccall((:nmod_poly_taylor_shift, :libflint), Nothing,
          (Ref{nmod_poly}, Ref{nmod_poly}, UInt), r, x, c)
  return r
end

function induce(FB::Hecke.NfFactorBase, A::Map)
  K = domain(A)
  f = A(gen(K)) # essentially a polynomial in the primitive element

  O = order(FB.ideals[1])
  prm = Array{Tuple{Int, Int}, 1}()

  if f == gen(K)
    return PermutationGroup(length(FB.ideals))()
  end

  for p in FB.fb_int.base
    FP = FB.fb[p]
    if length(FP.lp) < 3 || isindex_divisor(O, p) || p > 2^60
      lp = [x[2] for x = FP.lp]
      for (i, P) in FP.lp
        Q = induce_image(A, P)
        id = findfirst(isequal(Q), lp)
        @assert id !== nothing
        push!(prm, (i, FP.lp[id][1]))
      end
      #anti_ = [anti_uniformizer(x[2]) for x in FP.lp]
      #for (i, P) in FP.lp
      #  b = A(P.gen_two.elem_in_nf)
      #  id = -1
      #  for j in 1:length(FP.lp)
      #    if elem_in_nf(b * anti_[j]) in O
      #      id = j
      #      break
      #    end
      #  end
      #  #Q = induce_image(P, A)
      #  #id = findfirst(isequal(Q), lp)
      #  push!(prm, (i, FP.lp[id][1]))
      #end
    else
      px = PolynomialRing(GF(Int(p), cached=false), "x", cached=false)[1]
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
        push!(prm, (i, FP.lp[findfirst(isequal(im), lp)][1]))
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
#function orbit_in_FB(op::Array{Tuple{Map, Generic.Perm}, 1}, a::nf_elem, s::SRow)
function orbit_in_FB(op::Array, a::nf_elem, s::SRow)
  function op_smat(n::SRow, p::Generic.Perm)
    r = [(p[i], v) for (i,v) = n]
    sort!(r, lt = (a,b)->a[1]<b[1])
    return typeof(n)(r)
  end

  Ss = Dict{nf_elem, typeof(s)}()
#  Ss = Dict{typeof(s), nf_elem}()
  Ss[a] = s
  # start with the cyclic group be op[1]
  n = s
  b = op[1][1](a)
  while b != a
    n = op_smat(n, op[1][2])
    Ss[b] = n
    b = op[1][1](b)
  end

  for i=2:length(op)
    bb = op[i][1](a)
    if haskey(Ss, bb)
      continue
    end
    old = collect(Ss)
    for (bb, n) in old # one redundant - step
      Ss[op[i][1](bb)] = op_smat(n, op[i][2])
    end
    while true
      done = true
      for j = 1:length(op)
        bb = op[j][1](b)
        if haskey(Ss, bb)
          continue;
        end
        done = false
        b = bb
        for (bbb, n) in old
          # TODO: What is going on with the b's?
          Ss[op[j][1](bbb)] = op_smat(n, op[j][2])
        end
      end
      if done
        break
      end
    end
  end
  return Ss
end

function generated_subgroup(op::Array) #pairs: permutations and Map
  elt = Array{Any, 1}()
  push!(elt, (x->x, parent(op[1][2])()))
  ord = 1
  g = op[1]
  while g[2] != parent(op[1][2])()
    let c_g = g
      push!(elt, c_g)
#      g = (x->op[1][1](c_g[1](x)), op[1][2]*c_g[2])
      g = (x->op[1][1](c_g[1](x)), c_g[2]*op[1][2])
    end
  end
  ord = length(elt)

  for i=2:length(op)
    c_i = i
    if op[i][2] in [x[2] for x=elt]
      continue
    end
    pord = ord
    push!(elt, op[i])
    for j=2:pord
      c_j = j
#      push!(elt, (x->elt[c_j][1](op[c_i][1](x)), elt[c_j][2]*op[c_i][2]))
      push!(elt, (x->elt[c_j][1](op[c_i][1](x)), op[c_i][2]*elt[c_j][2]))
    end
    ord = length(elt)
    rpos = pord + 1
    while true
      for s in op
        let c_rpos = rpos, c_s = s
#          g = (x->elt[c_rpos][1](c_s[1](x)), elt[c_rpos][2]*c_s[2])
          g = (x->elt[c_rpos][1](c_s[1](x)), c_s[2]*elt[c_rpos][2])
          if g[2] in [x[2] for x=elt]
            continue
          end
        end
        let c_g = g
          push!(elt, c_g)
          for j = 2:pord
            c_j = j
#            push!(elt, (x->elt[c_j][1](c_g[1](x)), elt[c_j][2]*c_g[2]))
            push!(elt, (x->elt[c_j][1](c_g[1](x)), c_g[2]*elt[c_j][2]))
          end
        end
        ord = length(elt)
      end
      rpos += pord
      if rpos > length(elt)
        break
      end
    end
  end
  return elt
end
