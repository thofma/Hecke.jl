################################################################################
# fmpz_mat -> nemo file
# use as include(...)
################################################################################
function toNemo(io::IOStream, A::fmpz_mat; name = "A")
  println(io, name, " = MatrixSpace(FlintZZ, ", nrows(A), ", ", ncols(A), ")([")
  for i = 1:nrows(A)
    for j = 1:ncols(A)
      print(io, A[i,j])
      if j < ncols(A)
        print(io, " ")
      end
    end
    if i<nrows(A)
      println(io, ";")
    end
  end
  println(io, "]);")
  println(io, "println(\"Loaded ", name, "\")")
end

function toNemo(s::String, A::fmpz_mat)
  f = open(s, "w")
  toNemo(f, A)
  close(f)
end

################################################################################
# fmpz_mat -> magma file
# use as read(...)
################################################################################
function toMagma(io::IOStream, A::fmpz_mat; name = "A")
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

function toMagma(s::String, A::fmpz_mat)
  f = open(s, "w")
  toMagma(f, A)
  close(f)
end

################################################################################
# SMat -> magma file
# use as read(...)
################################################################################
function toMagma(io::IOStream, A::SMat; name = "A")
  println(io, name, " := SparseMatrix(Integers(), ", nrows(A), ", ", ncols(A), ", [")
  for i = 1:nrows(A)
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

function toMagma(s::String, A::SMat)
  f = open(s, "w")
  toMagma(f, A)
  close(f)
end

################################################################################
# MPoly -> magma file
# use as read(...)
################################################################################
function toMagma(io::IOStream, R::AbstractAlgebra.MPolyRing; base_name::String = "S", name::String = "R")
  print(io, "$name<")
  S = symbols(R)
  for i = 1:length(S)-1
    print(io, "$(S[i]),")
  end
  print(io, "$(S[end])> := PolynomialRing($base_name, $(length(S)));\n")
end

function toMagma(p::String, R::AbstractAlgebra.MPolyRing; base_name::String = "S", name::String = "R", make::String = "w")
  f = open(p, mode)
  Hecke.toMagma(f, R, base_name = base_name, name = name)
  close(f)
end

function toMagma(io::IOStream, f::Generic.MPolyElem)
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

function toMagma(io::IOStream, k::AnticNumberField; name::String = "S", gen_name::String="_a")
  print(io, "$name<$gen_name> := NumberField($(k.pol));\n")
end

function toMagma(io::IOStream, s::Symbol, v::Any)
  print(io, "$s := ")
  Hecke.toMagma(io, v)
  print(io, ";\n")
end

