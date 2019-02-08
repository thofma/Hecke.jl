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

