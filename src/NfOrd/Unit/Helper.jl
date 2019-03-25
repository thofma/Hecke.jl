function _transform(x::Array{nf_elem}, y::fmpz_mat)
  n = length(x)
  @assert n == nrows(y)
  m = ncols(y)
  z = Array{nf_elem}(m)
  for i in 1:m
    z[i] = x[1]^y[1, i]
    for j in 2:n
      z[i] = z[i]*x[j]^y[j, i]
    end
  end
  return z
end

function _make_row_primitive(x::fmpz_mat, j::Int)
  y = x[j, 1]
  for i in 1:ncols(x)
    y = gcd(y, x[j, i])
  end
  if y > 1
    for i in 1:ncols(x)
      x[j, i] = div(x[j, i], y)
    end
  end
end

function _make_row_primitive!(x::Array{fmpz, 1})
  y = x[1]
  for i in 2:length(x)
    y = gcd(y, x[i])
    if y == 1
      return x
    end
  end
  if y > 1
    for i in 1:ncols(x)
      x[i] = div(x[i], y)
    end
  end
end

function _primitive_element(F::Union{FqNmodFiniteField, FqFiniteField})
  #println("Computing primitive element of $F")
  #println("Have to factor $(order(F) - 1)")
  oF = order(F) - 1
  fac = factor(oF)
  exps = Vector{fmpz}()
  for (l, ll) in fac
    push!(exps, div(oF, l))
  end

  while true
    a = rand(F)
    if iszero(a)
      continue
    end
    is_primitive = true
    for e in exps
      if isone(a^e)
        is_primitive = false
        break
      end
    end
    if is_primitive
      return a
    end
  end
end
