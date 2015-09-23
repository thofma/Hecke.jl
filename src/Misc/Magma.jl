################################################################################
# fmpz_mat -> nemo file
# use as include(...)
################################################################################
function toNemo(io::IOStream, A::fmpz_mat; name = "A")
  println(io, name, " = MatrixSpace(ZZ, ", rows(A), ", ", cols(A), ")([")
  for i = 1:rows(A)
    for j = 1:cols(A)
      print(io, A[i,j])
      if j < cols(A)
        print(io, " ")
      end
    end
    if i<rows(A)
      println(io, ";")
    end
  end
  println(io, "]);")
  println(io, "println(\"Loaded ", name, "\")")
end

function toNemo(s::ASCIIString, A::fmpz_mat)
  f = open(s, "w")
  toNemo(f, A)
  close(f)
end

################################################################################
# fmpz_mat -> magma file
# use as read(...)
################################################################################
function toMagma(io::IOStream, A::fmpz_mat; name = "A")
  println(io, name, " := Matrix(Integers(), ", rows(A), ", ", cols(A), ", [")
  for i = 1:rows(A)
    for j = 1:cols(A)
      print(io, A[i,j])
      if j < cols(A)
        print(io, ", ")
      end
    end
    if i<rows(A)
      println(io, ",")
    end
  end
  println(io, "]);")
  println(io, "\"Loaded ", name, "\";")
end

function toMagma(s::ASCIIString, A::fmpz_mat)
  f = open(s, "w")
  toMagma(f, A)
  close(f)
end

################################################################################
# Smat -> magma file
# use as read(...)
################################################################################
function toMagma(io::IOStream, A::Smat; name = "A")
  println(io, name, " := SparseMatrix(Integers(), ", rows(A), ", ", cols(A), ", [")
  for i = 1:rows(A)
    for xx = 1:length(A.rows[i].entry) 
      x = A.rows[i].entry[xx]
      print(io, "<", i, ", ", x.col, ", ", x.val, ">")
      if xx < length(A.rows[i].entry) || i<rows(A)
        print(io, ", ")
      end
    end
    println(io, "")
  end
  println(io, "]);")
  println(io, "\"Loaded ", name, "\";")
end

function toMagma(s::ASCIIString, A::Smat)
  f = open(s, "w")
  toMagma(f, A)
  close(f)
end

