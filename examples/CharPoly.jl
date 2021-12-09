module CharPolyMod
using Hecke

#TODO: a (spin_base) as a sparse matrix
#      see if the reduction at old pivots is actually neccessary
#      try to use a dense matrix for spin_base and use rows. Initialise a full matrix
#        and avoid any allocations - in particular for gfp_elem
#      in "the" example a full reduction might be good.
function append_rref!(a::Vector{Vector{T}}, piv::Vector{Int}, e::Vector{T}) where {T}
  rel = Vector{T}()
  tmp = zero(parent(e[1]))
  for i=1:length(piv)
    x = reduce!(e[piv[i]])

    x = -x*inv(a[i][piv[i]])
    push!(rel, x)
    if !iszero(x)
      for j=1:length(e)
        tmp = mul_red!(tmp, x, a[i][j], false)
        e[j] = add!(e[j], e[j], tmp)
      end
    end
  end
  i=1
  while i<= length(e) && iszero(e[i]) 
    i += 1
  end
  for i=1:length(e)
    e[i] = reduce!(e[i])
  end
  if i <= length(e)
#    for j=1:length(a)
#      if !iszero(a[j][i])
#        x = inv(e[i]*a[j][i])
#        for k=1:length(e)
#          a[j][k] = a[j][k] - x*e[k]
#        end
#      end
#    end
    push!(a, copy(e))
    push!(piv, i)
  end
  return rel
end

function charpoly_fac_elem(A::SMat{<:FieldElem})
  n = ncols(A)
  @assert n == nrows(A)
  dims_free = Set{Int}(1:n)
  piv = Int[]
  k = base_ring(A)
  kt, t = PolynomialRing(k, cached = false)
  cp = typeof(t)[]

  spin_base = Vector{Vector{elem_type(k)}}()

  while length(dims_free) > 0
    @show length(dims_free)
    i = pop!(dims_free)
    e = zeros(k, n)
    ee = zeros(k, n)
    e[i] = one(k)
    lp = length(piv)
    f = [one(kt)]
    push!(spin_base, copy(e))
    push!(piv, i)
    while true
      Hecke.mul!(ee, A, e)
      e, ee = ee, e
      nc = length(spin_base)
      rel = append_rref!(spin_base, piv, e)
      re = map(kt, rel[lp+1:end])
      re[end] += t
      push!(f, sum(f.*re))
      if length(spin_base) == nc
#        @show f
#        @show length(piv), length(dims_free)
        for i in piv[lp+2:end]
          pop!(dims_free, i)
        end
        for i in lp+1:length(piv)
          spin_base[i] .*= inv(spin_base[i][piv[i]])
        end
        push!(cp, f[end])
        if length(piv) > 10000
          return cp, spin_base
        end
        break
      else
#        e = copy(spin_base[end])
      end
    end
  end
  m = MSet(cp)
  return FacElem(kt, m.dict)
end

Hecke.charpoly(A::SMat{nf_elem}) = evaluate(charpoly_fac_elem(A))
#=
#works as the charpoly_fac_elem actually returns the minpolys
#for the sigma cyclic spaces
Hecke.minpoly(A::SMat{nf_elem}) = reduce(lcm, keys(charpoly_fac_elem(A).fac))

does not work:
a 1
0 a
could return t-a => 2 as there is a cyclic subspace of dim 1
and, once we factor this out, the second is also dim 1.
For this to work, we cannot factor out the older subspaces
=#

Hecke.iszero_entry(M::MatElem, i::Int, j::Int) = iszero(M[i,j])

#uses Berlekamp-Massey instead of lin-alg to get the minpoly for
#the sigma cyclic spaces. Seems to not be too good on the
#huge example, but according to lit. is fine.
function minpoly_bm(A::SMat{nf_elem})
  k = base_ring(A)
  zk = maximal_order(k)
  local mF
  done = false
  for p = PrimesSet(2^40, -1)
    lp = prime_decomposition(zk, p)
    for P = lp
      if degree(P[1]) == 1 && P[2] == 1
        F, mF = ResidueField(zk, P[1])
        mF = Hecke.extend_easy(mF, k)
        done = true
        break
      end
    end
    if done
      break
    end
  end

  F = codomain(mF)
  bas_p = matrix(F, 0, ncols(A), elem_type(F)[])

  used_bas = []
  kt, t = PolynomialRing(k, cached = false)
  
  e = zeros(k, nrows(A))
  f = zeros(k, nrows(A))
  fp = []

  for i=1:nrows(A)
    if i in used_bas
      continue
    end
    @show :doing, i
    for j = 1:length(e)
      e[j] = zero(k)
    end
    e[i] = one(k)
    bm = [one(k)]
    used = [bm]
    start = nrows(bas_p)
    bas_p = vcat(bas_p, matrix(F, 1, ncols(A), map(mF, e)))
    while true
      Hecke.mul!(f, A, e)
      e, f = f, e
      push!(bm, sum(e))
      bas_p = vcat(bas_p, matrix(F, 1, ncols(A), map(mF, e)))
      fl, g = berlekamp_massey(bm, parent = kt)
      if fl && degree(g)*2 +2 < length(bm)
        @show g
        push!(fp, g)
        bas_p = bas_p[1:start+degree(g), :]
        rk = rref!(bas_p)
        @show rk, nrows(bas_p)
        @assert rk == nrows(bas_p)
        bas_p = bas_p[1:rk, :]
        v = [findfirst(x->!Hecke.iszero_entry(bas_p, i, x), 1:ncols(bas_p)) for i=1:nrows(bas_p)]
        @show used_bas, v
        @assert issubset(used_bas, v)
        used_bas = v
        if length(used_bas) > 500
          return fp, bas_p
        end
        break
      end
    end
  end
  return fp
end
        
#function Hecke.charpoly(A::SMat{nf_elem})
#end

end #CharPolyMod
