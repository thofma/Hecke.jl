################################################################################
#
#          RieSrf/ThetaFlint.jl : Functions for computing theta functions
#
#
################################################################################

################################################################################
#
#  Theta functions with characteristics and derivatives
#
################################################################################

#This is an interface to the Theta code by Jean Kieffer and Noam Elkies

export theta, theta_dz, thetas, theta_jets, theta_dzs, theta_dtaus, siegel_reduction, 
siegel_transform, cholesky_decomposition

@doc raw"""
    theta(z::Vector{AcbFieldElem}, tau::AcbMatrix, theta_characteristic)
     -> AcbFieldElem

Computes theta(a, b)(z, tau) where theta(a, b) is the Riemann theta function
(of level 2) of characteristic 
(a,b). If one wants to compute multiple theta characteristics, it is more efficient
to use `thetas`.

Clarification of input:
Let [a,b] be a tuple with a, b in {0,1}^g be a representative of the 
characteristic. The variable `theta_characteristic` can be given as either:

- An integer whose bit representation (most significant bit first) is equal to [a,b]
- A single array which is the concatenation of a and b
- A pair of arrays a and b
For example, for `g = 2`, letting `theta_characteristic` be either
`11`, `[1,0,1,1]` or `[[1,0],[1,1]]` would all give the same output.
"""
function theta(z::Vector{AcbFieldElem}, tau::AcbMatrix, ab_int::Int = 0)
  g = nrows(tau)
  zd = length(z)
  if g != zd
    error("Dimension mismatch. tau is of dimension $g, but z is of dimension $zd")
  end
  
  CC = base_ring(tau)
  prec = precision(CC)

  th = acb_vec(1)
  zzs = acb_vec(z)

  ccall((:acb_theta_one, Hecke.libflint), Nothing, (Ptr{acb_struct},
  Ptr{acb_struct}, Ref{AcbMatrix},UInt, Int), th, zzs, tau, ab_int, prec)

  res = array(CC, th, 1)
  acb_vec_clear(th, 1)
  acb_vec_clear(zzs, g)
  return res
end

function theta(z::Vector{AcbFieldElem},  tau::AcbMatrix, theta_ab::Vector{Int})
  ab = parse_theta_characteristic(theta_ab)
  return theta(z,  tau, ab)
end

function theta(z::Vector{AcbFieldElem},  tau::AcbMatrix, ab_vec::Vector{Vector{Int}})
  ab = parse_theta_characteristic(ab_vec)
  return theta(z,  tau, ab)
end

@doc raw"""
    thetas(z::Vector{AcbFieldElem}, tau::AcbMatrix; squared::Bool = false)
     -> Dict{Vector{Int},AcbFieldElem}

Computes theta(a,b)(z, tau) for all possible tuples [a,b] with a, b
in {0,1}^g. Output is returned as a dictionary with key entries Vectors
in {0,1}^(2g) and as values the corresponding theta values.

For example, if `D = thetas(z, tau)` for `z` in C^2 and `tau` a 2 by 2 matrix 
then `D[0,1,1,1]` will correspond to `theta([0,1],[1,1])(z, tau)`.

If the optional parameter `squared` is set to `true`, the algorithm will be
faster, but will return the squares of the theta values instead.
"""
function thetas(z::Vector{AcbFieldElem},  tau::AcbMatrix; squared::Bool = false)
  g = nrows(tau)
  zd = length(z)
  if (g != zd)
    error("Dimension mismatch. tau is of dimension $g, but z is of dimension $zd")
  end
  
  CC = base_ring(tau)
  prec = precision(CC)

  num_of_thetas = 2^(2*g)

  th = acb_vec(num_of_thetas)
  zzs = acb_vec(z)

  ccall((:acb_theta_all, libflint), Nothing, (Ptr{acb_struct},
  Ptr{acb_struct}, Ref{AcbMatrix}, Cint, Int), th, zzs, tau, squared, prec)

  theta_values = array(CC, th,   num_of_thetas)
  theta_indices = theta_characteristics_indices(g)
  result = Dict([(theta_indices[i], theta_values[i]) for i in (1:num_of_thetas)])

  acb_vec_clear(th, num_of_thetas)
  acb_vec_clear(zzs, g)
  return result
end


@doc raw"""
    theta_dz(z::Vector{AcbFieldElem}, tau::AcbMatrix, theta_characteristic,
    dz::Vector{Int}) -> AcbFieldElem

Computes the partial derivative with respect to the multi-index given by `dz`
of theta(a,b)(`z`, `tau`) where theta(a,b) is the Riemann theta function 
(of level 2) of characteristic (a,b). If one wants to compute multiple partial
derivatives for different theta characteristics, it is more efficient to use
`theta_dzs`.

Clarification of input:
Let [a,b] be a tuple with a, b in {0,1}^g be a representative of the 
characteristic. The variable `theta_characteristic` can be given as either:
- An integer whose bit representation (most significant bit first)
  is equal to [a,b]
- A single array which is the concatenation of a and b
- A pair of arrays a and b

For example, for `g = 2`, letting `theta_characteristic` be either
`11, `[1,0,1,1]` or `[[1,0],[1,1]]` would all give the same output.

The variable `dz` can be used to indicate which partial derivative you are computing.

For example, for `g = 2`, `dz = [2,3]` would mean computing 
d^5(theta_(a,b))/(dz_1^2 *dz_2^3).
"""
function theta_dz(z::Vector{AcbFieldElem},  tau::AcbMatrix, theta_characteristic::Vector{Int}, dz::Vector{Int})
  g = nrows(tau)
  if (g != length(dz))
    error("dz should have length $g")
  end
  d = sum(dz)
  D = theta_dzs(z, tau, d)
  return D[theta_characteristic...][dz...]
end

function theta_dz(z::Vector{AcbFieldElem},  tau::AcbMatrix, 
  theta_characteristic::Vector{Vector{Int}}, dz::Vector{Int})
  return theta_dz(z, tau, reduce(vcat, theta_characteristic), dz)
end

function theta_dz(z::Vector{AcbFieldElem},  tau::AcbMatrix, 
  theta_characteristic::Int, dz::Vector{Int})
  g = nrows(tau)
  @req 0 <= theta_characteristic <= 2^(g-1) "theta_characteristic has to be either an integer between 0 or 2^(g-1),"
  char_index = reverse(digits(theta_characteristic, base=2, pad=2*g))
  return theta_dz(z, tau, char_index, dz)
end

@doc raw"""
    theta_dtaus(z::Vector{AcbFieldElem}, tau::AcbMatrix) 
    -> Dict{Vector{Int},AcbFieldElem}

Computes the partial derivatives of theta(a,b)(`z`, `tau`) with respect to the
entries of `tau` for all possible tuples [a,b] with a, b in {0,1}^g.
Output is returned as a dictionary with key entries Vectors in {0,1}^(2g)
and as values matrices whose (i,j)-th entry corresponds to the derivative 
with respect to `tau[i,j]`.

For example, if `D = theta_dtaus(z, tau)` for `z` in C^2 and `tau` a 2 by 2 matrix 
then `D[0,1,1,1][1,2]` will correspond to the derivative of 
theta([0,1],[1,1])(z, tau) with respect to `tau[1,2]`.
"""
function theta_dtaus(z::Vector{AcbFieldElem},  tau::AcbMatrix)
  g = nrows(tau)
  dz = zeros(Int, g)
  D = theta_dzs(z, tau, 2)
  
  CC = base_ring(tau)
  piCC = CC(pi)
  I = onei(CC)

  theta_indices = theta_characteristics_indices(g)
  result = Dict(zip(theta_indices, [zero_matrix(CC,g, g) for i in (1:2^(2*g))] ))

  for i in (1:g)
    for j in (1:g)
      dz = zeros(Int, g)
      dz[i] = 1
      dz[j] = 1
      if i == j
        delta = 1
      else
        delta = 0
      end 
      factor = 1/(2*piCC*I*(1+delta))

      for theta_characteristic in theta_indices
        result[theta_characteristic...][i,j] = 
        D[theta_characteristic...][dz...] * factor
      end
    end
  end
  return result
end

@doc raw"""
    theta_jets(z::Vector{AcbFieldElem}, tau::AcbMatrix, d::Int) -> 
     Dict{NTuple, Dict{Tuple, AcbFieldElem}}

Computes the coefficients of the Taylor series expansion up to order `d`
of theta(a,b)(z, tau) where theta(a,b) is the Riemann theta function 
(of level 2) of characteristic (a,b). 

The output will be given as a dictionary of dictionaries.
The key set of the first dictionary will consist of the 
theta_characteristics.

Clarification of keys:
Let [a,b] be a tuple with a, b in {0,1}^g be a representative of the characteristic. The variable `theta_characteristic` can be 
given as either:
- An integer whose bit representation (most significant bit first) is equal to [a,b]
- A single array which is the concatenation of a and b
- A pair of arrays a and b
For example, for `g = 2`, letting `theta_characteristic` be either
`11`, `[1,0,1,1]` or `[[1,0],[1,1]]` would all give the same output.

The key set of the second dictionary will consist of the 
integer arrays determining a term in the Taylor expansion.

For example, if `D = theta_jets(z, tau, 3)` for `z` in C^2 and `tau` a 2 by 2 matrix 
then `D` will contain all coefficients for all theta characteristics
up to order 3, and

`D[0,1,1,1][1,2]` will correspond to the term of theta([0,1],[1,1])(`z`, `tau`)
related to `z_1^1 * z_2^2`.

Note that the output of `theta_jets` and `theta_derivatives` is very similar.
The elements of `theta_jets` are normalized in the way one would normalize
coefficients of a Taylor expansion, i.e. the coefficient of the monomial with
multidegree (k0, k_{g-1}) will be 
1/k0! * ... * 1/k_{g-1}! * d^k/(dz_1^k0 ... dz_{g-1}^k_{g-1}).
"""
function theta_jets(z::Vector{AcbFieldElem},  tau::AcbMatrix, order_of_derivatives::Int;)
  g = nrows(tau)
  zd = length(z)
  if (g != zd)
    error("Dimension mismatch. tau is of dimension $g, but z is of dimension $zd")
  end

  #Get total number of derivatives
  n = ccall((:acb_theta_jet_nb, libflint), Int, (Int, Int), order_of_derivatives, g)
  tups = zeros(Int, n*g)
  tupss = pointer(tups)
  #Get the tuples representing the partial derivatives. 
  GC.@preserve tups ccall((:acb_theta_jet_tuples, libflint), Nothing, (Ptr{Int}, Int,Int),
  tupss, order_of_derivatives, g)
  
  if g ==1 
    index_tuples = tups
  else 
    index_tuples = [tuple(tups[g*i+1:g*i+g]...) for i in (0:n-1)]
  end

  num_of_thetas = 2^(2*g)
  output_size = num_of_thetas * n
  
  CC = base_ring(tau)
  prec = precision(CC)

  th = acb_vec(output_size)
  zzs = acb_vec(z)

  sqr = 0
  number_of_z = 1

  theta_characteristic = 0
  all = 1

  ccall((:acb_theta_jet, libflint), Nothing, (Ptr{acb_struct},
  Ptr{acb_struct}, Int, Ref{AcbMatrix}, Int, UInt, Cint, Cint, Int), th, zzs, number_of_z, tau, 
  order_of_derivatives, theta_characteristic, all, sqr, prec)

  res = array(CC, th, output_size)
  theta_indices = theta_characteristics_indices(g)
  result_tuples = [Dict(zip(index_tuples, res[n*i+1:n*i+n])) for i in (0:num_of_thetas-1)]


  #Return a dictionary where the keys consist of tuples indexing the partial derivatives
  #and the values are dictionaries consisting of the 2^g theta derivatives.
  result = Dict([(theta_indices[i], result_tuples[i]) for i in (1:num_of_thetas)])

  acb_vec_clear(th, output_size)
  acb_vec_clear(zzs, g)
  return result
end

@doc raw"""
    theta_dzs(z::Vector{AcbFieldElem}, tau::AcbMatrix, d::Int) -> 
     Dict{NTuple, Dict{Tuple, AcbFieldElem}}

Computes all of the partial derivatives of theta(a,b)(z, tau) up to order d
where theta(a,b) is the Riemann theta function (of level 2) of 
characteristic (a,b). 

The output will be given as a dictionary of dictionaries.

The key set of the first dictionary will consist of the 
theta_characteristics.

Clarification of keys:
Let [a,b] be a tuple with a, b in {0,1}^g be a representative of the 
characteristic. The variable `theta_characteristic` can be given as either:
- An integer whose bit representation (most significant bit first)
  is equal to [a,b]
- A single array which is the concatenation of a and b
- A pair of arrays a and b
For example, for `g = 2`, letting `theta_characteristic` be either
11, [1,0,1,1] or [[1,0],[1,1]] would all give the same output.

The key set of the second dictionary will consist of the 
integer arrays determining the partial derivative.

For example, if `D = theta_dzs(z, tau, 3)` for `z` in C^2 and `tau` a 2 by 2 matrix 
then `D` will contain all the partial derivatives for all theta characteristics
up to order 3.

D[0,1,1,1][1,2] will correspond to d^3/(dz_1*dz_2^2)theta([0,1],[1,1])(z, tau).

Note that the output of `theta_jets` and `theta_dzs` is very similar.
The elements of `theta_jets` are normalized in the way you would normalize
coefficients of a Taylor expansion, i.e. the coefficient of the monomial with
multidegree (k0, k_{g-1}) will be 
1/k0! * ... * 1/k_{g-1}! * d^k/(dz_1^k0 ... dz_{g-1}^k_{g-1}).
"""
function theta_dzs(z::Vector{AcbFieldElem},  tau::AcbMatrix, order_of_derivatives::Int)
  result = theta_jets(z, tau, order_of_derivatives)
  for char in keys(result)
    for dz in keys(result[char])
      factor = prod(map(factorial, dz))
      result[char][dz]*=factor
    end
  end
  return result
end

function parse_theta_characteristic(theta_characteristic::Vector{Int})
  for i in theta_characteristic
    if (i!=0 && i!=1)
      error("theta_characteristic has to be either an integer between 0 or 2^(g-1),
       a vector in {0,1}^2g or a tuple (a,b) with a, b in {0,1}^g.")
    end
  end
  return evalpoly(2, reverse(theta_characteristic))
end

function parse_theta_characteristic(theta_characteristic::Vector{Vector{Int}})
  if length(theta_characteristic) != 2
    error("theta_characteristic has to be either an integer between 0 or 2^(g-1),
    a vector in {0,1}^2g or a tuple (a,b) with a, b in {0,1}^g.")
  end
  return parse_theta_characteristic(reduce(vcat,theta_characteristic))
end

function theta_characteristics_indices(g::Int)
   indices = []
   for i in (0:2^(2*g)-1)
     push!(indices,tuple(reverse(digits(i, base=2, pad=2*g))...))
   end
   return indices
end

@doc raw"""
    siegel_reduction(tau::AcbMatrix) -> AcbMatrix

Compute the Siegel reduction of the period matrix `tau`, i.e.
writing `siegel_reduction(tau) = X + i*Y`. We will have |X_mn| <= 1/2
for all n, m and the lattice generated by Y will be LLL reduced.
"""
function siegel_reduction(tau::AcbMatrix)
  g = number_of_rows(tau)
  T = zero_matrix(ZZ, 2*g, 2*g)
  prec = precision(base_ring(tau))
  ccall((:acb_siegel_reduce, libflint), Nothing, (Ref{ZZMatrix}, Ref{AcbMatrix}
  ,Int), T, tau ,prec)

  return T, siegel_transform(T, tau)
end

@doc raw"""
    siegel_transform(T::ZZMatrix, tau::AcbMatrix) -> AcbMatrix

Let `T = [[A,B],[C,D]]` be a 2g x 2g matrix subdivided into four g x g
matrices `A`, `B`, `C` and `D`.

Return `(A*tau + B) * inv(C*tau + D)`.
"""
function siegel_transform(T::ZZMatrix,tau::AcbMatrix)
  g = number_of_rows(tau)
  @req number_of_columns(tau) == g "Tau needs to be a square matrix."
  @req number_of_rows(T) == number_of_columns(T) == 2*g "If tau is a g by g matrix then T needs to be a 2g by 2g matrix."
  A = T[1:g, 1:g]
  B = T[1:g, g+1:2*g]
  C = T[g+1:2*g, 1:g]
  D = T[g+1:2*g, g+1:2*g]
  return (A*tau + B) * inv(C*tau+D)
end

function cholesky_decomposition(x::ArbMatrix)
  z = similar(x, nrows(x), ncols(x))
  p = precision(base_ring(x))
  fl = ccall((:arb_mat_cho, libflint), Cint, (Ref{ArbMatrix}, Ref{ArbMatrix}, Int), z, x, p)
  @assert fl != 0
  return z
end
