export index_p_subgroups

function index_p_subgroups(A::GrpAbFinGen, p::Integer)
  return index_p_subgroups(A, fmpz(p))
end

type IndexPSubgroups
  p::Int
  n::UInt
  st::Int
  mp::Map
  c::fmpz_mat
  mthd::Function

  function IndexPSubgroups(A::GrpAbFinGen, p::fmpz, mthd::Function = sub)
    r = new()
    if order(A) % p != 0
      r.n = 0
      return r
    end
    s, ms = snf(A)  # ms: A -> s
    @assert s.issnf
    r.p = Int(p)
    r.mp = ms
    i=1
    while s.snf[i] % p != 0
      i += 1
    end
    r.st = i
    r.n = UInt(div(fmpz(p)^(length(s.snf)-i+1) - 1, fmpz(p)-1))
    r.c = MatrixSpace(FlintZZ, length(s.snf), length(s.snf))()
    r.mthd = mthd
    return r
  end
end

function index_p_subgroups(A::GrpAbFinGen, p::fmpz, mthd::Function = sub)
  @assert isprime(p)
  return IndexPSubgroups(A, p, mthd)

  #a subgroup of index p corresponds to a HNF with exactly one p on the
  #diagonal - and the other entries arbitrary reduced.
  #so it should be 1 + p + p^2 + + p^(n-1) = ((p^n)-1)/(p-1) many
end

function index_to_group(s::IndexPSubgroups, i::UInt)
  j = 1
  x = 1
  while i>=x
    i -= x
    x *= s.p
    j += 1
  end
  c = s.c
  zero!(c)
  for k=1:rows(c)
    if s.st+j-1 != k
      c[k, k] = 1
    end
  end
#  println("i: $i  j: $j")
  k = 1
  while i != 0
    c[k+s.st-1, s.st + j-1] = i%s.p
    i = div(i, s.p)
    k += 1
  end
  c[s.st + j-1, s.st + j-1] = s.p
  gen = [s.mp\(codomain(s.mp)(sub(c, l:l, 1:cols(c)))) for l=1:rows(c)]
  return s.mthd(domain(s.mp), gen)
end

function Base.start(s::IndexPSubgroups)
  return UInt(0)
end

function Base.next(s::IndexPSubgroups, i::UInt)
  return index_to_group(s, i), i+1
end

function Base.length(s::IndexPSubgroups)
  return s.n
end

function Base.done(s::IndexPSubgroups, i::UInt)
  return i>=s.n
end


#=
example:
 julia> sg = index_p_subgroups(GrpAbFinGen([3,3,3,3]), 3)
 julia> index_to_group(sg, UInt(6));
=#
