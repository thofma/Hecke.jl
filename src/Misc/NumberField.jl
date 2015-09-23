################################################################################
# given a basis (an array of elements), get a linear combination with
# random integral coefficients
################################################################################

function rand(b::Array{nf_elem,1}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")

  s = zero(b[1].parent)
  t = zero(b[1].parent)

  for i = 1:length(b)
    mul!(t, b[i], rand(r))
    add!(s, t, s)
  end
  return s
end

function rand!(c::nf_elem, b::Array{nf_elem,1}, r::UnitRange)
  length(b) == 0 && error("Array must not be empty")

  mul!(c, b[1], rand(r))
  t = zero(b[1].parent)

  for i = 2:length(b)
    mul!(t, b[i], rand(r))
    add!(c, t, c)
  end
  nothing
end

################################################################################
#
#  fmpq_poly with denominator 1 to fmpz_poly
#
################################################################################

function Base.call(a::FmpzPolyRing, b::fmpq_poly)
  (den(b) != 1) && error("denominator has to be 1")
  z = a()
  ccall((:fmpq_poly_get_numerator, :libflint), Void,
              (Ptr{fmpz_poly}, Ptr{fmpq_poly}), &z, &b)
  return z
end

function basis(K::AnticNumberField)
  n = degree(K)
  g = gen(K);
  d = Array(typeof(g), n)
  b = K(1)
  for i = 1:n-1
    d[i] = b
    b *= g
  end
  d[n] = b
  return d
end

function representation_mat(a::nf_elem)
  @assert den(a) == 1
  dummy = fmpz(0)
  n = degree(a.parent)
  M = MatrixSpace(FlintZZ, n,n)()::fmpz_mat
  t = gen(a.parent)
  b = a
  for i = 1:n-1
    elem_to_mat_row!(M, i, dummy, b)
    b *= t
  end
  elem_to_mat_row!(M, n, dummy, b)
  return M
end 

function set_den!(a::nf_elem, d::fmpz)
  ccall((:nf_elem_set_den, :libflint), 
        Void, 
       (Ptr{Nemo.nf_elem}, Ptr{Nemo.fmpz}, Ptr{Nemo.AnticNumberField}), 
       &a, &d, &parent(a))
end

function basis_rels(b::Array{nf_elem, 1}, c; bd::fmpz = fmpz(10^35), no_p::Int = 4, no_rel::Int = 10000, no_coeff::Int = 4 )
  a = b[1].parent()
  t = b[1].parent()
  nb = length(b)
  one = fmpz(1)
  for i=1:no_rel
    zero!(a)
    for j=1:no_coeff
      cf = rand([-1, 1])
      p  = rand(1:nb)
      if cf==1
        Nemo.add!(a, a, b[p])
      else
        Nemo.sub!(a, a, b[p])
      end
    end
    n = norm_div(a, one, no_p)
    if cmpabs(num(n), bd) <= 0 
      if class_group_add_relation(c, a, n, one)
        a = b[1].parent()
      end
    end
  end
end

