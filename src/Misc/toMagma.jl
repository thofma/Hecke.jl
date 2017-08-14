function toMagma(f::IOStream, a::Array{T, 1}; name::String="R") where T
  print(f, name, " := [\n")
  for i=1:(length(a)-1)
    try
      toMagma(f, a[i]);
    catch b
      print(f, a[i])
    end
    print(f, ",\n")
  end
  try
    toMagma(f, a[end])
  catch b
    print(f, a[end])
  end
  print(f, "];\n")
end

function toMagma(f::IOStream, t::Tuple)
  print(f, "<")
  for i=1:length(t)
    try
      toMagma(f, t[i])
    catch e
      print(f, t[i])
    end
    if i<length(t)
      print(f, ", ")
    else
      print(f, ">\n")
    end
  end
end  

function toMagma(s::String, a::Array{T, 1}; name::String="R", mode::String ="w") where T
  f = open(s, mode)
  toMagma(f, a, name = name)
  close(f)
end
  

