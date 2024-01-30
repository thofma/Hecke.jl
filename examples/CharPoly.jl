module CharPolyMod
using Hecke

#TODO: a (spin_base) as a sparse matrix
#      see if the reduction at old pivots is actually necessary
#      try to use a dense matrix for spin_base and use rows. Initialise a full matrix
#        and avoid any allocations - in particular for fpFieldElem
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

function Hecke.charpoly(A::SMat{<:FieldElem})
  n = ncols(A)
  @assert n == nrows(A)
  dims_free = Set{Int}(1:n)
  piv = Int[]
  k = base_ring(A)
  kt, t = polynomial_ring(k, cached = false)
  cp = typeof(t)[]

  spin_base = Vector{Vector{elem_type(k)}}()

  while length(dims_free) > 0
    @show length(dims_free)
    i = minimum(dims_free)
    pop!(dims_free, i)
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
  return cp
end

#function Hecke.charpoly(A::SMat{AbsSimpleNumFieldElem})
#end

end #CharPolyMod
