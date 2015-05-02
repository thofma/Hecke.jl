################################################################################
#
#  misc.jl : At some point this should migrate to Nemo
#
################################################################################

# compute basis for the right kernel space by calling flint
# look at flint documentation of nmod_mat_nullspace

function _right_kernel(x::nmod_mat)
  z = MatrixSpace(base_ring(x), cols(x), max(rows(x),cols(x)))()
  n = ccall((:nmod_mat_nullspace, :libflint), Clong, (Ptr{nmod_mat}, Ptr{nmod_mat}), &z, &x)
  return z,n
end

# compute basis for the left kernel space
# output is array of arrays, which span the kernel

function kernel(a::nmod_mat)
  x = transpose(a)
  z,n = _right_kernel(x)
  z = transpose(z)
  println(z)
  ar = typeof(Array(Residue{fmpz}, cols(z)))[]
  for i in 1:n 
    t = Array(Residue{fmpz}, cols(z))
    for j in 1:cols(z)
      t[j] = z[i,j]
    end
    push!(ar,t)
  end
  println(ar)
  return ar
end
