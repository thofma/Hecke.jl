function _raw_setindex(A::zzModMatrix, i::Int, j::Int, x::UInt)
  ccall((:nmod_mat_set_entry, libflint), Nothing, (Ref{zzModMatrix}, Int, Int, UInt), A, i - 1, j - 1, x)
end


###############################################################################
#
#  Howell form for Generic.Mat{ZZRingElem}
#
###############################################################################

function howell_form(A::Generic.Mat{Nemo.ZZModRingElem})
  local B::ZZMatrix
  if nrows(A) < ncols(A)
    B = vcat(lift(A), zero_matrix(FlintZZ, ncols(A)-nrows(A), ncols(A)))
  else
    B = lift(A)
  end
  R = base_ring(A)
  ccall((:fmpz_mat_howell_form_mod, libflint), Nothing,
              (Ref{ZZMatrix}, Ref{ZZRingElem}), B, modulus(R))
  return change_base_ring(B, R)
end

#
#  for the in-place function, the number of rows must be at least equal to the number of columns
#
function howell_form!(A::Generic.Mat{Nemo.ZZModRingElem})

  R = base_ring(A)
  A1 = lift(A)
  ccall((:fmpz_mat_howell_form_mod, libflint), Nothing,
                (Ref{ZZMatrix}, Ref{ZZRingElem}), A1, modulus(R))
  for i in 1:nrows(A)
    for j in 1:ncols(A)
      A[i, j] = A1[i, j]
    end
  end
  return A
end

function triangularize!(A::Generic.Mat{Nemo.ZZModRingElem})
  R=base_ring(A)
  n=R.modulus

  #
  #  Get an upper triangular matrix
  #

  for j=1:ncols(A)
    for i=j+1:ncols(A)
      g,s,t,u,v = _xxgcd(A[j,j].data,A[i,j].data,n)
      for k in 1:ncols(A)
        t1 = s* A[j,k] + t* A[i,k]
        t2 = u* A[j,k] + v* A[i,k]
        A[j,k] = t1
        A[i,k] = t2
      end
    end
  end
end

function triangularize(A::Generic.Mat{Nemo.ZZModRingElem})
  B= triangularize!(deepcopy(A))
  return B
end
