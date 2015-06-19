export mag

type MagnSet
end  

MagSet = MagnSet()


type mag
  exp::Int # fmpz
  man::UInt64

  function mag()
    z = new()
    ccall((:mag_init, :libarb), Void, (Ptr{mag}, ), &z)
    finalizer(z, _mag_clear_fn)
    return z
  end
  
  function mag(x::UInt)
    z = new()
    ccall((:mag_init, :libarb), Void, (Ptr{mag}, ), &z)
    ccall((:mag_set_ui, :libarb), Void, (Ptr{mag}, UInt), &z, x)
    finalizer(z, _mag_clear_fn)
    return z
  end
end

parent(::mag) = MagSet

function _mag_clear_fn(x::mag)
  ccall((:mag_clear, :libarb), Void, (Ptr{mag}, ), &x)
end

