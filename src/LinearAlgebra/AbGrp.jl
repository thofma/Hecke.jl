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

function getindex(x::AbGrpElem, i::Int)
  return x.coord[i]
end

function +(x::AbGrpElem, y::AbGrpElem)
  parent(x) != parent(y) && error("Parents must coincide")
  z = Array(fmpz, length(x.coord))
  for i in 1:length(z)
    z[i] = x.coord[i] + y.coord[i]
  end
  return parent(x)(z) # this gives the reduced element
end

function *(x::Integer, y::AbGrpElem)
  z = parent(x)()
  for i in 1:length(z)
    z.coord[i] = x*y.coord[i]
  end
  return z
end

*(x::AbGrpElem, y::Integer) = y*x

function *(x::fmpz, y::AbGrpElem)
  z = parent(x)()
  for i in 1:length(z)
    z.coord[i] = x*y.coord[i]
  end
  return z
end

*(x::AbGrpElem, y::fmpz) = y*x

type AbToNfOrdUnitGrp{T, S} <: Map{AbGrp, FactoredElemMon{T}}
  header::MapHeader{AbGrp, FactoredElemMon{nf_elem}}
  ind_unit::Array{FactoredElem{T}, 1}
  tor_unit::S

  # this only works if there exists at least one independent unit
  # That is, ind_unit should not have length 1
  function AbToNfOrdUnitGrp(O::NfMaximalOrder, ind_unit::Array{FactoredElem{T}, 1}, tor_unit::S, tor_ord::Int)
    A = AbGrp(vcat([ 0 for i in 1:length(ind_unit) ],[ tor_ord ]))
    z = new()
    z.ind_unit = ind_unit
    z.tor_unit = tor_unit

    function _image(a::AbGrpElem)
      y = parent(z.ind_unit[1])()

      for i in 1:length(z.ind_unit)
        if a[i] == 0
          continue
        end
        y = y*z.ind_unit[i]^a[i]
      end

      if a[length(A.diagonal)] != 0
        y = y*tor_unit^a[length(A.diagonal)]
      end

      return y
    end

    z.header = MapHeader(A, parent(z.ind_unit[1]), _image)

    return z
  end
end

function AbToNfOrdUnitGrp{T, S}(O::NfMaximalOrder, ind_unit::Array{FactoredElem{T}, 1}, tor_unit::S, tor_ord::Int)
  length(ind_unit) == 0 && error("Not implemented yet")
  return AbToNfOrdUnitGrp{T, S}(O, ind_unit, tor_unit, tor_ord)
end

elem_type(::Type{NfMaximalOrder}) = NfOrderElem

elem_type{T}(::Type{FactoredElemMon{T}}) = FactoredElem{T}
