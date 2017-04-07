################################################################################
#
#  Conversion to Nemo/hecke for storage
#
################################################################################

function toNemo{T}(f::IOStream, a::Array{T, 1}; name::String="R")
  print(f, name, " = [\n")
  for i=1:(length(a)-1)
    print(f, a[i], ",\n")
  end
  print(f, a[end], "];\n")
end

function toNemo{T}(s::String, a::Array{T, 1}; name::String="R", mode::String ="w")
  f = open(s, mode)
  toNemo(f, a, name = name)
  close(f)
end

