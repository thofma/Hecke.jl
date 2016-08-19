type nmod_struct
  n::UInt    # mp_limb_t
  ninv::UInt # mp_limb_t
  norm::UInt # mp_limb_t
end

type ZZmodUInt <: Ring
  mod::nmod_struct

  function ZZmodUInt(n::UInt)
    z = new()
    ccall((:nmod_init, :libflint), Void, (Ptr{nmod_struct}, UInt), &z.mod, n)
    return z
  end
end

immutable UIntMod <: RingElem
  m::UInt
  parent::ZZModUInt

  function UIntMod(R::ZZmodUInt, m::UInt)
    z = m % R.n
    z.parent = R
    return z
  end
end

for (fn, fc) in ((:+, "nmod_add"), (:*, "nmod_mul"), (:-, "nmod_sub"),
      (://, "nmod_div"))
  @eval begin
    function ($fn)(x::UInt, y::UInt)
      z = ccall(($fc, :libflint), Void,
            (UInt, UInt, Ptr{nmod_struct}), x, y, x.parent.mod)
      z.parent = x.parent
      return z
    end
  end
end

