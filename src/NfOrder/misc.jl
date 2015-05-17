################################################################################
#
#  misc.jl : At some point this should migrate to Nemo
#
################################################################################

export kernel_mod

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
  #println(z)
  ar = typeof(Array(Residue{fmpz}, cols(z)))[]
  for i in 1:n 
    t = Array(Residue{fmpz}, cols(z))
    for j in 1:cols(z)
      t[j] = z[i,j]
    end
    push!(ar,t)
  end
  #println(ar)
  return ar
end

function kernel_mod(a::fmpz_mat, m::fmpz)
  b = deepcopy(a)
  for i in 1:rows(b)
    for j in 1:cols(b)
      b[i,j] = b[i,j] % m
    end
  end

  # fmpz_mat_rref_mod assumes that input is reduced modulo m
  r = ccall((:fmpz_mat_rref_mod, :libflint), Int, (Ptr{Void}, Ptr{fmpz_mat}, Ptr{fmpz}), C_NULL, &b, &m)
  pivots = Array(Int, r)
  nonpivots = Array(Int, cols(b) - r)
  X = zero(MatrixSpace(ZZ,cols(b),cols(b)))

  if r == 0
    return one(MatrixSpace(ZZ, cols(b), cols(b)))
  elseif !((cols(b) - r) == 0)
    i = 1
    j = 1
    k = 1
    for i in 1:r
      while b[i,j] == 0
        nonpivots[k] = j
        k += 1
        j += 1
      end
      pivots[i] = j
      j += 1
    end
    while k <= cols(b) - r
      nonpivots[k] = j
      k += 1
      j += 1
    end

    for i in 1:cols(b) - r
      for j in 1:r
        X[pivots[j],i] = - ZZ(b[j,nonpivots[i]])
      end
      X[nonpivots[i],i] = ZZ(1)
    end
  end
  return X, r
end
  
