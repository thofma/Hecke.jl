struct ZZIdl
  gen::fmpz

  function ZZIdl(x::fmpz)
    if x < 0
      return new(abs(x))
    else
      return new(x)
    end
  end
end

struct ZZFracIdl
  gen::fmpq
  
  function ZZFracIdl(x::fmpq)
    if x < 0
      return new(abs(x))
    else
      return new(x)
    end
  end
end

# constructors

ideal(::FlintIntegerRing, x::fmpz) = ZZIdl(x)

ideal(::FlintIntegerRing, x::Integer) = ZZIdl(fmpz(x))

fractional_ideal(::FlintIntegerRing, x::fmpq) = ZZFracIdl(x)

fractional_ideal(::FlintIntegerRing, x::RingElement) = ZZFracIdl(fmpq(x))

# printing 

#TODO

# arithmetic

function +(I::ZZIdl, J::ZZIdl)
  return ZZIdl(gcd(I.gen, I.gen))
end

# TODO
