################################################################################
#
#  Conversion to Nemo/Hecke for storage
#
################################################################################

function toNemo(f::IOStream, a::Dict{T, S}; name::String="R") where {T, S}
  print(f, name, " = Dict{$T,$S}(\n")
  k = collect(keys(a))
  for i=1:length(k)-1
    print(f, k[i], " => ", a[k[i]], ", \n")
  end
  print(f, k[end], " => ", a[k[end]], ");\n")
end


function toNemo(s::String, a::Dict; name::String="R", mode::String ="w") 
  f = open(s, mode)
  toNemo(f, a, name = name)
  close(f)
end

function toNemo(f::IOStream, a::Array{T, 1}; name::String="R") where T
  print(f, name, " = [\n")
  for i=1:(length(a)-1)
    print(f, a[i], ",\n")
  end
  print(f, a[end], "];\n")
end

function toNemo(s::String, a::Array{T, 1}; name::String="R", mode::String ="w") where T
  f = open(s, mode)
  toNemo(f, a, name = name)
  close(f)
end

