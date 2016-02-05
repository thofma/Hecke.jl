################################################################################
#
#  AbGrp.jl : Finitely generated abelian groups
#
################################################################################

function show(io::IO, A::AbGrp)
  print(io, "Abelian group\n")

  if A.inf_num > 0
    print(io, "Z")
  end

  for i in 1:A.inf_num - 1
    print(io, " x Z")
  end

  if A.fin_num > 0 && A.inf_num > 0
    print(io, " x ")
  end

  if A.fin_num > 0
    print(io, "Z/$(A.diagonal[A.inf_num + 1])")
  end

  for i in 2:A.fin_num 
    print(io, " x Z/$(A.diagonal[A.inf_num + i])")
  end
end

function show(io::IO, a::AbGrpElem)
  print(io, "Element of\n$(a.parent)\n with components\n$(a.coord)")
end

function parent(x::AbGrpElem)
  return x.parent
end

function call(A::AbGrp, x::Array{fmpz, 1})
  # need sanity checks
  y = deepcopy(x)
  for i in A.inf_num + 1:length(y)
    y[i] = mod(x[i], A.diagonal[i])
  end
  z = AbGrpElem(A, y)
  return z
end

function call(A::AbGrp, x::Array{Int, 1})
  # need sanity checks
  z = A(map(fmpz, x))
  return z
end

function getindex(A::AbGrp, i::Int)
  z = Array(fmpz, length(A.diagonal))
  for j in 1:length(A.diagonal)
    z[j] = fmpz()
  end
  z[i] = fmpz(1)
  return AbGrpElem(A, z)
end

function +(x::AbGrpElem, y::AbGrpElem)
  parent(x) != parent(y) && error("Parents must coincide")
  z = Array(fmpz, length(x.coord))
  for i in 1:length(z)
    z[i] = x.coord[i] + y.coord[i]
  end
  return parent(x)(z) # this gives the reduced element
end
