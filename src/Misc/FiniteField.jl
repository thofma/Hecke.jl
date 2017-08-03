##
## rand for Flint-Finite fields
##
## fq_nmod has no base ring
function rand(R::FqNmodFiniteField)
  #gen is not a generator for the group!
  r = R(0)
  for i=0:degree(R)
    r *= gen(R)
    r += rand(1:characteristic(R))
  end

  return r
end

function rand(R::FqFiniteField)
  #gen is not a generator for the group!
  r = R(0)
  for i=0:degree(R)
    r *= gen(R)
    r += rand(1:characteristic(R))
  end

  return r
end

################################################################################
#
#  Iterators for finite fields
#
################################################################################

# FqNmodFiniteField

Base.start(F::FqNmodFiniteField) = zeros(UInt, degree(F))

function Base.next(F::FqNmodFiniteField, i::Array{UInt, 1})
  d = F()
  ccall((:fq_nmod_init2, :libflint), Void, 
        (Ptr{fq_nmod}, Ptr{FqNmodFiniteField}), &d, &F)
  for j in 1:length(i)
         ccall((:nmod_poly_set_coeff_ui, :libflint), Void,
              (Ptr{fq_nmod}, Int, UInt), &d, j - 1, i[j])
  end

  i[1] = i[1] + 1
  for j in 1:(length(i) - 1)
    if i[j] == F.n
      i[j] = 0
      i[j + 1] = i[j + 1] + 1
    end
  end
  return d, i
end

Base.length(F::FqNmodFiniteField) = BigInt(F.n)^degree(F)

function Base.done(F::FqNmodFiniteField, i::Array{UInt, 1})
  for j in 1:length(i) - 1
    if i[j] != 0
      return false
    end
  end
  if i[end] != F.n
    return false
  end
  return true
end

Base.eltype(::FqNmodFiniteField) = fq_nmod

# FqFiniteField

Base.start(F::FqFiniteField) = zeros(FlintZZ, degree(F))

function Base.next(F::FqFiniteField, i::Array{fmpz, 1})
  d = F()
  ccall((:fq_init2, :libflint), Void, 
        (Ptr{fq}, Ptr{FqFiniteField}), &d, &F)
  for j in 1:length(i)
         ccall((:fmpz_mod_poly_set_coeff_fmpz, :libflint), Void,
               (Ptr{fq}, Int, Ptr{fmpz}), &d, j - 1, &(i[j]))
  end

  i[1] = i[1] + 1
  for j in 1:(length(i) - 1)
    if i[j] == characteristic(F)
      i[j] = 0
      i[j + 1] = i[j + 1] + 1
    end
  end
  return d, i
end

Base.length(F::FqFiniteField) = BigInt(characteristic(F))^degree(F)

function Base.done(F::FqFiniteField, i::Array{fmpz, 1})
  for j in 1:length(i) - 1
    if i[j] != 0
      return false
    end
  end
  if i[end] != characteristic(F)
    return false
  end
  return true
end

Base.eltype(::FqFiniteField) = fq
