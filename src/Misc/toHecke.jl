################################################################################
#
#  Conversion to Nemo/Hecke for storage
#
################################################################################

function to_hecke(f::IOStream, a::Dict{T, S}; name::String="R") where {T, S}
  print(f, name, " = Dict{$T,$S}(\n")
  k = collect(keys(a))
  for i=1:length(k)-1
    print(f, k[i], " => ", a[k[i]], ", \n")
  end
  print(f, k[end], " => ", a[k[end]], ");\n")
end


function to_hecke(s::String, a::Dict; name::String="R", mode::String ="w")
  f = open(s, mode)
  to_hecke(f, a, name = name)
  close(f)
end

function to_hecke(f::IOStream, a::Vector{T}; name::String="R") where T
  print(f, name, " = [\n")
  for i=1:(length(a)-1)
    print(f, a[i], ",\n")
  end
  print(f, a[end], "];\n")
end

function to_hecke(s::String, a::Vector{T}; name::String="R", mode::String ="w") where T
  f = open(s, mode)
  to_hecke(f, a, name = name)
  close(f)
end


################################################################################
# ZZMatrix -> nemo file
# use as include(...)
################################################################################
function to_hecke(io::IOStream, A::ZZMatrix; name = "A")
  println(io, name, " = matrix(ZZ, ", nrows(A), ", ", ncols(A), "ZZRingElem[")
  for i = 1:nrows(A)
    for j = 1:ncols(A)
      print(io, A[i,j])
      if j < ncols(A)
        print(io, ", ")
      end
    end
    if i<nrows(A)
      println(io, ", ")
    end
  end
  println(io, "]);")
  println(io, "println(\"Loaded ", name, "\")")
end

function to_hecke(s::String, A::ZZMatrix)
  f = open(s, "w")
  to_hecke(f, A)
  close(f)
end

