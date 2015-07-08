export arb_mat

type arb_mat
  entries::Ptr{Void}
  r::Int
  c::Int
  rows::Ptr{Void}
  parent

  function arb_mat()
    return new()
  end

  function arb_mat(r::Int, c::Int)
    z = new()
    ccall((:arb_mat_init, :libarb), Void,
          (Ptr{arb_mat}, Int, Int), &z, r, c)
    finalizer(z, _arb_mat_clear_fn)
    return z
  end

  function arb_mat(a::fmpz_mat)
    z = new()
    ccall((:arb_mat_init, :libarb), Void, (Ptr{arb_mat}, Int, Int), &z, a.r, a.c)
    ccall((:arb_mat_set_fmpz_mat, :libarb), Void, (Ptr{arb_mat}, Ptr{fmpz_mat}), &z, &a)
    finalizer(z, _arb_mat_clear_fn)
    return z
  end
end

function _arb_mat_clear_fn(x::arb_mat)
  ccall((:arb_mat_clear, :libarb), Void, (Ptr{arb_mat}, ), &x)
end

function getindex(x::arb_mat, r::Int, c::Int)
  v = arb_t()
  z = ccall((:arb_mat_entry, :libarb), Ptr{Void}, (Ptr{arb_mat}, Int, Int), &x, r - 1, c - 1)
  ccall((:arb_set, :libarb), Void, (Ptr{Void}, Ptr{Void}), v.data, z)
  return v
end

function setindex!(x::arb_mat, y::arb_t, r::Int, c::Int)
  z = ccall((:arb_mat_entry, :libarb), Ptr{Void}, (Ptr{arb_mat}, Int, Int), &x, r - 1, c - 1)
  ccall((:arb_set, :libarb), Void, (Ptr{Void}, Ptr{Void}), z, y.data)
end

function show(io::IO, a::arb_mat)
   rows = a.r
   cols = a.c
   for i = 1:rows
      print(io, "[")
      for j = 1:cols
         print(io, a[i, j])
         if j != cols
            print(io, " ")
         end
      end
      print(io, "]")
      if i != rows
         println(io, "")
      end
   end
end

