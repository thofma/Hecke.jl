# Checks whether x[1]^z[1] * ... x[n]^z[n]*y^[n+1] is a torsion unit
# This can be improved
function _check_relation_mod_torsion(x::Vector{FacElem{nf_elem, AnticNumberField}}, y::FacElem{nf_elem, AnticNumberField}, z::Vector{fmpz}, p::Int = 16)
  (length(x) + 1 != length(z)) && error("Lengths of arrays does not fit")
  r = x[1]^z[1]

  for i in 2:length(x)
    r = r*x[i]^z[i]
  end

  w = r*y^z[length(z)]

  b, _ = is_torsion_unit(w, false, p)
#  b, _ = is_torsion_unit(w)
  return b
end

function _find_rational_relation!(rel::Vector{fmpz}, v::arb_mat, bound::fmpz)
  #push!(_debug, (deepcopy(rel), deepcopy(v), deepcopy(bound)))
  @vprint :UnitGroup 2 "Finding rational approximation in $v\n"
  r = length(rel) - 1

  z = Array{fmpq}(undef, r)

  # Compute an upper bound in the denominator of an entry in the relation
  # using Cramer's rule and lower regulator bounds

  # Now comes the rational approximation phase

  # First a trivial check:
  # If the relation contains only integers, it does not yield any information

  i = 0

  is_integer = true

  while is_integer && i < r
    i = i + 1
    b, o = unique_integer(v[1, i])
    if b
      rel[i] = o
    end
    is_integer = is_integer && b
  end

  if is_integer
    rel[r + 1] = -1
    @vprint :UnitGroup 2 "Found rational relation: $rel.\n"
    return true
  end

  for i in 1:r
    if radius(v[1, i]) > 1
      # This is a strange case I cannot handle at the moment
      return false
    end

    app = simplest_inside(v[1, i], bound)

    if app[1]
      z[i] = app[2]
    else
      @vprint :UnitGroup 2 "Something went wrong with the approximation.\n"
      return false
    end
  end

  dlcm = denominator(z[1])

  for i in 2:length(z)
    dlcm = lcm(dlcm, denominator(z[i]))
  end

  if dlcm > bound
    return false
  end

  for i in 1:r
    rel[i] = numerator(z[i]*dlcm)
  end

  rel[r + 1] = -dlcm

  # Check that relation is primitive
  g = rel[1]

  for i in 2:length(rel)
    g = gcd(g, rel[i])
    if g == 1
      break
    end
  end

  @assert g == 1

  @vprint :UnitGroup 2 "Found rational relation: $rel.\n"
  return true
end

# Given r elements x_1,...,x_r, where r is the unit rank, and y an additional unit,
# compute a basis z_1,...z_r such that <x_1,...x_r,y,T> = <z_1,...,z_r,T>,
# where T are the torsion units

function _find_relation(x::Vector{S}, y::T, p::Int = 64) where {S, T}

  K = _base_ring(x[1])

  deg = degree(K)
  r1, r2 = signature(K)
  rr = r1 + r2
  r = rr - 1 # unit rank

  R = ArbField(p, cached = false)

  zz = Array{fmpz}(undef, r + 1)

  @vprint :UnitGroup 1 "Computing conjugates log matrix ... \n"
  A = _conj_log_mat_cutoff(x, p)

  Ar = base_ring(A)

  b = ArbMatSpace(Ar, 1, r)()

  conlog = conjugates_arb_log(y, p)

  for i in 1:r
    b[1, i] = conlog[i]
  end

  B = parent(A)()


  # I should do this using lu decomposition and caching
  # The inversion could go wrong,
  # Then we again have to increase the precision

  inv_succesful = false

  try
    @vprint :UnitGroup 1 "Inverting matrix ... \n"
    B = inv(A)
    inv_succesful = true
  catch e
    @vprint :UnitGroup 1 "Cannot invert matrix ... \n"
    rethrow(e)
  end

  v = b*B

  z = Array{fmpq}(undef, r)

  rreg = det(A)

  bound = _denominator_bound_in_relation(rreg, K)

  # Compute an upper bound in the denominator of an entry in the relation
  # using Cramer's rule and lower regulator bounds


  rel = Array{fmpz}(undef, r + 1)
  for i in 1:r+1
    rel[i] = zero(FlintZZ)
  end

  while !inv_succesful || !_find_rational_relation!(rel, v, bound)
    p =  2*p

    inv_succesful = false

    A = _conj_log_mat_cutoff(x, p)

    Ar = base_ring(A)

    b = ArbMatSpace(Ar, 1, r)()

    conlog = conjugates_arb_log(y, p)

    for i in 1:r
      b[1, i] = conlog[i]
    end

    if !inv_succesful
      try
        @vprint :UnitGroup 1 "Inverting matrix ... \n"
        B = inv(A)
        inv_succesful = true
      catch
        @vprint :UnitGroup 1 "Cannot invert matrix. Increasing precision to $(2*p)\n"
      end
    end

    v = b*B
  end

  # Check if it is a relation modulo torsion units!
  @vprint :UnitGroup 1 "Checking relation $rel \n"

  if !_check_relation_mod_torsion(x, y, rel)
    #error("Dirty approximation did not work")
    return _find_relation(x, y, 2*p)
    #rel[r + 1 ] = 0
    #return rel
  end

  @vprint :UnitGroup 1 "Found a valid relation!\n"
  return rel
end

function _denominator_bound_in_relation(rreg::arb, K::AnticNumberField)
  # Compute an upper bound in the denominator of an entry in the relation
  # using Cramer's rule and lower regulator bounds

  arb_bound = rreg * inv(lower_regulator_bound(K))

  # I want to get an upper bound as an fmpz
  return abs_upper_bound(fmpz, arb_bound)
end

function simplest_inside(x::arb, B::fmpz)
  q = simplest_inside(x)
  if denominator(q) < B
    return true, q
  else
    return false, q
  end
end

