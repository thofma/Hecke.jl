function to_magma(f::IOStream, a::Vector{T}; name::String="R") where T
  print(f, name, " := [\n")
  for i=1:(length(a)-1)
    try
      to_magma(f, a[i]);
    catch b
      print(f, a[i])
    end
    print(f, ",\n")
  end
  try
    to_magma(f, a[end])
  catch b
    print(f, a[end])
  end
  print(f, "];\n")
end

function to_magma(f::IOStream, t::Tuple)
  print(f, "<")
  for i=1:length(t)
    try
      to_magma(f, t[i])
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

function to_magma(s::String, a::Vector{T}; name::String="R", mode::String ="w") where T
  f = open(s, mode)
  to_magma(f, a, name = name)
  close(f)
end


################################################################################
# ZZMatrix -> magma file
# use as read(...)
################################################################################
function to_magma(io::IOStream, A::ZZMatrix; name = "A")
  println(io, name, " := Matrix(Integers(), ", nrows(A), ", ", ncols(A), ", [")
  for i = 1:nrows(A)
    for j = 1:ncols(A)
      print(io, A[i,j])
      if j < ncols(A)
        print(io, ", ")
      end
    end
    if i<nrows(A)
      println(io, ",")
    end
  end
  println(io, "]);")
  println(io, "\"Loaded ", name, "\";")
end

function to_magma(s::String, A::ZZMatrix)
  f = open(s, "w")
  to_magma(f, A)
  close(f)
end

################################################################################
# SMat -> magma file
# use as read(...)
################################################################################
function to_magma(io::IOStream, A::SMat; name = "A")
  println(io, name, " := SparseMatrix(Integers(), ", nrows(A), ", ", ncols(A), ", [")
  for i = 1:nrows(A)
    length(A.rows[i]) == 0 && continue
    for xx = 1:length(A.rows[i].pos)
      print(io, "<", i, ", ", A.rows[i].pos[xx], ", ", A.rows[i].values[xx], ">")
      if xx < length(A.rows[i].pos) || i<nrows(A)
        print(io, ", ")
      end
    end
    println(io, "")
  end
  println(io, "]);")
  println(io, "\"Loaded ", name, "\";")
end

function to_magma(s::String, A::SMat)
  f = open(s, "w")
  to_magma(f, A)
  close(f)
end

################################################################################
# MPoly -> magma file
# use as read(...)
################################################################################
function to_magma(io::IOStream, R::AbstractAlgebra.MPolyRing; base_name::String = "S", name::String = "R")
  print(io, "$name<")
  S = symbols(R)
  for i = 1:length(S)-1
    print(io, "$(S[i]),")
  end
  print(io, "$(S[end])> := PolynomialRing($base_name, $(length(S)));\n")
end

function to_magma(p::String, R::AbstractAlgebra.MPolyRing; base_name::String = "S", name::String = "R", make::String = "w")
  f = open(p, mode)
  Hecke.to_magma(f, R, base_name = base_name, name = name)
  close(f)
end

function to_magma(io::IOStream, f::Generic.MPolyRingElem)
  S = symbols(parent(f))
  for i=1:length(f)
    if i>1
      print(io, "+")
    end
    s = "$(coeff(f, i))"
    s = replace(s, "//" => "/")
    print(io, "($s)")
    e = exponent_vector(f, i)
    if iszero(e)
      continue
    end
    print(io, "*")
    fi = true
    for j=1:length(S)
      if e[j] > 0
        if !fi
          print(io, "*")
        else
          fi = false
        end
        print(io, "$(S[j])^$(e[j])")
      end
    end
  end
end

function to_magma(io::IOStream, k::AbsSimpleNumField; name::String = "S", gen_name::String="_a")
  print(io, "$name<$gen_name> := NumberField($(k.pol));\n")
end

function to_magma(io::IOStream, s::Symbol, v::Any)
  print(io, "$s := ")
  Hecke.to_magma(io, v)
  print(io, ";\n")
end

