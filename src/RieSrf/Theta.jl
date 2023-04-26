################################################################################
#
#          RieSrf/Theta.jl : Functions for computing theta functions
#
# (C) 2023 Jeroen Hanselman
#
################################################################################


export theta, siegel_reduction

################################################################################
#
#  Theta functions with characteristics and derivatives
#
################################################################################

#Based on Computing Theta Functions with Julia by Daniele Agostini and Lynn Chua

@doc raw"""
    theta(z::Vector{acb},  tau::acb_mat}; char::Vector{Vector{Int}}, 
    dz::Vector{Vector{Int}}, dtau::Vector{Vector{Int}}, prec::Int) -> acb

Compute the value of the theta(tau, z) with characteristic char with 
precision the minimum of prec, the precision of z and the precision of 
tau. Optionally one can set dz to be a list of elements of a standard basis
to compute the derivative of the Theta function with characteristic char at 
the point z in the specified directions. (E.g. in genus 3 setting
 dz = [[1,0,0], [0,0,1]] would compute dtheta(z, tau)/(dx1 dx3).
Similarly, one can set dtau to be a list of integers tuples to take the 
derivative with respect to the period matrix tau. (E.g. dtau = [[1,2]]
would compute dtheta(z, tau)/dtau_{1,3}) 
"""
function theta(z::Vector{acb}, tau::Vector{acb}; char::Vector{Vector{Int}} = [zeros(Int, 1), zeros(Int, 1)], dz::Vector{Vector{Int}}=Vector{Int}[], dtau::Vector{Vector{Int}}= Vector{Int}[], prec::Int = 0)
  return _theta(z, matrix(tau), char, dz, dtau, prec)
end

function theta(z::Vector{acb}, tau::acb_mat; char::Vector{Vector{Int}} = [zeros(Int, nrows(tau)), zeros(Int, nrows(tau))], dz::Vector{Vector{Int}}=Vector{Int}[], dtau::Vector{Vector{Int}}= Vector{Int}[], prec::Int = 0)
  return _theta(z, tau, char, dz, dtau, prec)
end

function _theta(z::Vector{acb}, tau::acb_mat, char::Vector{Vector{Int}}, dz::Vector{Vector{Int}}, dtau::Vector{Vector{Int}}, prec::Int = 0)

  g = nrows(tau)
    
  if length(char[1])!= g || length(char[2])!= g
    error("Characteristic needs to be of length g")
  end
  
  #tau = X + i*Y
  X = real(tau)
  Y = imag(tau)
  
  #Find T upper-triangular with transpose(T)*T = Y
  T = transpose(cholesky_decomposition(Y))

  
  if length(z)!= g
    error("z needs to be an element of C^g")
  end
  
  if prec > 0
    prec = min(prec, precision(parent(z[1])), precision(parent(tau[1, 1])))
  else
    prec = min(precision(parent(z[1])), precision(parent(tau[1, 1])))
  end
  
  n = floor(prec*log(2)/log(10))
  
  Cc = AcbField(prec)
  Rc = ArbField(prec)
  piR = const_pi(Rc)
  i = onei(Cc)
  
  
  
  eps = Rc(10^(-n)) #Should depend on precision

  #In Agostini and Chua's code rho = is taken to be the square of the norm of the shortest vector times sqrt(pi)) for some reason.
  #This could affect the error bounds
  
  rho = norm(shortest_vectors(transpose(T))[1]*sqrt(piR))
  
  factor = one(Cc)
  for ij in dtau
    if ij[1] == ij[2]
      factor //= (4 * piR * i)
    else
      factor //= (2 * piR * i)
    end
    deriv = [zeros(g), zeros(g)]
    deriv[1][ij[1]] = 1
    deriv[2][ij[2]] = 1
    dz = vcat(dz, deriv)
  end
  
  N = Int(sum(map(t-> sum(t; init = 0), dz); init = 0))
  
  R0 = (sqrt(g + 2*N + sqrt(g^2 + 8*N)) + rho)//2
  
  T_inv_norm = norm(inv(T))
  
  #We compute the radius of the ellipsoid over which we take the sum needed to bound the error in the sum by eps (See Theorem 3.1 in Agostini, Chua) 
  R_function = function(x::arb, eps::arb)
    Rc = parent(x)
    return (2*piR)^N * g//2 * (2//rho)^g * sum([binomial(N, j) * inv(pi^(j//2))* T_inv_norm^j * sqrt(g)^(N - j) * gamma(Rc((g + j)//2), (x - rho//2)^2) for j in (0:N)]; init = zero(Rc)) - eps
  end
  
  #We want to find the max(R0, x) where x is the solution to R_function(x, eps) = 0
  #Taking x bigger will only improve the error bound, but we want x to be as small as possible
  #to speed up later computations. We therefore look for an x for which R_function(x, eps) is small 
  #and negative.
  #As R_function is monotonic descending we first determine an R1 for which R_function(R1, eps) <0
  #and then subdivide intervals until we find a solution that satisfies our requirements
  
  R1 = R0
  err = Rc(10^(-n))
  
  #Find an R1 such that R_function becomes negative
  while R_function(R1, eps) > 0
    R1 = R1 + R0
  end
  
  if R1 != R0
    while 0 < R_function(R0, eps) || R_function(R0, eps) < -err 
      Rmid = (R0 + R1)/2
      middle = R_function(Rmid, eps)
      if middle < 0 
        R1 = Rmid
      else
        R0 = Rmid
      end
    end
  end
  
  radius_ellipsoid = R1
  error_epsilon = R_function(R1, zero(Rc))
  
  ellipsoid_points = Hecke.enumerate_using_gram(Y, R1^2//piR)
  for i in (1:g)
    Lat1 = Vector{ZZRingElem}[]
    pad = zeros(ZZRingElem, g)
    pad[i] = 1
    for l in ellipsoid_points
      push!(Lat1, l + pad)
      push!(Lat1, l - pad)
    end
    ellipsoid_points = union(ellipsoid_points, Lat1)
  end
  

  
  #We seem to find more points than Agostini as we also consider lattices centered at points of the form [0,1,-1], etc.
  #This could also affect error bounds
 
  #We compute the Theta function
  x = real(z)
  y = imag(z)
  
  invYy = inv(Y) * y
  exponential_part = exp(piR*(transpose(y) * invYy)) 
  
  eta = map(Rc, (map(t -> round(ZZRingElem, t), invYy) - map(ZZ, char[1])//2))
  
  pointset = map(t -> map(Rc, t) - eta, ellipsoid_points)
  
  oscillatory_part = (2*piR*i)^N*sum([
  prod(transpose(d)*v for d in dz; init = one(Rc)) * 
  exp(piR*i*((transpose(v) * (X * v)) + 2*transpose(v) * (x + map(ZZ, char[2])//2))) * exp(-piR* (transpose(v + invYy) * (Y * (v + invYy)))) for v in pointset]; init = zero(Cc))
  
  result = factor*exponential_part*oscillatory_part
  
  error_term = exponential_part*error_epsilon
  
  ccall((:acb_add_error_arb, libarb), Cvoid,
      (Ref{acb}, Ref{arb}), result, error_term)
  
  return result
end

@doc raw"""
    siegel_reduction(tau::acb_mat) -> acb_mat
    
Compute the Siegel reduction of the period matrix tau, i.e.
writing siegel_reduction(tau) = X +iY. We will have |X_mn| <= 1/2
for all n, m and the shortest vector of the lattice generated by
Y will have squared length smaller than sqrt(3)/2.
"""
function siegel_reduction(tau::acb_mat)
  g = nrows(tau)
  
  Rc = base_ring(real(tau))
  Cc = base_ring(tau)
  
  Aq = [zero_matrix(Rc, 1, 1) zero_matrix(Rc, 1, g-1);zero_matrix(Rc, g-1, 1) identity_matrix(Rc, g-1)]
  Bq = [-identity_matrix(Rc, 1) zero_matrix(Rc, 1, g-1);zero_matrix(Rc, g-1, 1) zero_matrix(Rc, g-1, g-1)]
  Cq = -Bq
  Dq = Aq
  
  quasi_inversion = [Aq Bq; Cq Dq]
  
  Gamma = identity_matrix(Rc, 2*g)
  e = zero(Rc)
  
  while e <= 1
    Y = imag(tau)
    Y = (Y + transpose(Y)) // Rc(2) #ensure matrix remains symmetric
    
    T = cholesky_decomposition(imag(tau))

    T, U = lll_with_transform(T)
    
    
    Tt = transpose(T)
    
    
    short = 1
    for i in (1 : g)
      if norm(Tt[:, short]) > norm(Tt[:, i])
        short = i
      end
    end
    
    if short!= 1
      S = swap_cols(identity_matrix(Rc, g), 1, short)
      T = S * T
      U = S * U
    end
    
    Tt = transpose(T)
    Y = T*Tt
  
    Gamma = [U zero_matrix(Rc, g, g); zero_matrix(Rc, g, g) inv(transpose(U))] * Gamma;
    tau = U * real(tau) * transpose(U) + onei(Cc) * Y
  
    B = change_base_ring(Rc, map(t -> round(ZZRingElem, t), real(tau)))
    tau -=  change_base_ring(Cc, B)
    Gamma = [identity_matrix(Rc, g) (-B); zero_matrix(Rc, g, g) identity_matrix(Rc, g)]*Gamma 
    e = abs(tau[1,1])
    if e > 1
      return tau, Gamma
    else
      Gamma = quasi_inversion * Gamma
      tau = (Aq * tau + Bq) * inv(Cq * tau + Dq)
    end
  end
end

*(x::acb, y::arb_mat) = x * _acb_mat(y)
*(x::arb_mat, y::acb) = y * x
*(x::arb_mat, y::acb_mat) = _acb_mat(x) * y
*(x::acb_mat, y::arb_mat) = x * _acb_mat(y)
+(x::arb_mat, y::acb_mat) = _acb_mat(x) + y
+(x::acb_mat, y::arb_mat) = y + x
-(x::arb_mat, y::acb_mat) = x + (-y)
-(x::acb_mat, y::arb_mat) = x + (-y)
//(x::arb_mat, y::arb) = map(t -> t//y, x)


function _acb_mat(A::arb_mat)
  p = precision(base_ring(A))
  Cc = AcbField(p)
  return change_base_ring(Cc, A)
end

function real(tau::acb_mat)
  return map(real, tau)
end

function imag(tau::acb_mat)
  return map(imag, tau)
end

function cholesky_decomposition(x::arb_mat)
  z = similar(x, nrows(x), ncols(x))
  p = precision(base_ring(x))
  fl = ccall((:arb_mat_cho, Hecke.libarb), Cint, (Ref{arb_mat}, Ref{arb_mat}, Int), z, x, p)
  @assert fl != 0
  return z
end

function lll(M::arb_mat; ctx = lll_ctx(0.99, 0.51))
  return lll_with_transform(M::arb_mat; ctx = lll_ctx(0.99, 0.51))[1]
end

function lll_with_transform(M::arb_mat; ctx = lll_ctx(0.99, 0.51))
  R = base_ring(M)
  
  #Find number of bits of precision of coefficients of M and subtract 4 to divide by 16 and ensure the numbers are small enough to round
  p = -(ceil(Int,log(maximum(radius, M))/log(2))+4)
  n = nrows(M)
  d = zero_matrix(FlintZZ, n, n)
  round_scale!(d, M, p)
  d, T = lll_with_transform(d, ctx)
  T = change_base_ring(R, T)
  return T*M, T
end


function shortest_vectors(M::arb_mat)
  R = base_ring(M)
  p = -(ceil(Int,log(maximum(radius, M))/log(2))+4)
  n = nrows(M)
  d = zero_matrix(ZZ, n, n)
  round_scale!(d, M, p)
  L = Zlattice(d)
  U = shortest_vectors(L)
  return map(matrix, [map(R, u)*M for u in U])
end

function norm(v::arb_mat)
  return sqrt(sum([a^2 for a in v]))
end

