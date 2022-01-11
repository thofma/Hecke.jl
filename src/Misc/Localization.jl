###############################################################################
#
#   Random Functions
#
###############################################################################

# mainly for testing
function rand(L::Loc{T}, num_scale = (1:1000), den_scale=(1:1000)) where {T <: fmpz}
   num = rand(num_scale)
   den = rand(den_scale)
   while gcd(den,prime(L)) != 1
      den = rand(den_scale)
   end
   return L(num//den)
end

Nemo.promote_rule(::Type{LocElem{T}}, ::Type{T}) where {T} = LocElem{T}

