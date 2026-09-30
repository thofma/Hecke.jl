

#The sign flip that occurs when adding characteristics
#together.
function _sign_flip(char::Vector{QQFieldElem})
  g = div(length(char), 2)
  v = [floor(QQFieldElem, c) for c in char]
  zer = zero_matrix(QQ, g, g)
  id = identity_matrix(QQ, g)
  J = [zer id; zer zer]
  result = (-1)^(Int(2*((transpose(char * J) * v))))
  return result
end

#Resolve the sign flip in the theta characteristic
function theta_HI(D, char)
  newchar = mod.(Int.(2*char), Ref(2))
  return D[newchar...]*_sign_flip(char)
end

#Takes the half characteristic inner product of an element with itseld, i.e
#If m = [e d] then the inner product is 
# (e, d)
function half_char_inner_prod(n::Vector{QQFieldElem})
  g = div(length(n),2)
  return Int(4*(transpose(n[1:g]) * n[g+1:2*g]))
end

#Takes the inner product of two half characteristics, i.e
#If m1 = [e1 d1] and m2 = [e2 d2] then the inner product is 
# (e1, d2)
function half_char_inner_prod(n::Vector{QQFieldElem}, m::Vector{QQFieldElem})
  g = div(length(n),2)
  return Int(4*(transpose(n[1:g]) * m[g+1:2*g]))
end

function half_char_inner_prod(n::Vector{FqFieldElem}, m::Vector{FqFieldElem})
  g = div(length(n),2)
  return Int(lift(ZZ,((transpose(n[1:g]) * m[g+1:2*g]))))
end

#Return the theta constants as a list where theta_list[1] corresponds to 
#(0,0,...,1) and theta_list[2^(2*g)] corresponds to (0,0,...0)
function theta_list(thetas, g)
  theta_indices = Hecke.theta_characteristics_indices(g)
  theta_list = [thetas[theta_indices[i + 1]] for i in (1:2^(2*g)-1)]
  push!(theta_list, thetas[theta_indices[1]])
  return theta_list
end

#Compute the arf_notmal form of the theta characteristic.
function transform_to_arf_form(char)
  g = div(length(char),2)
  M = identity_matrix(GF(2), 2*g)
  J = collect(1:g)
  while length(J) != 0
    j = popfirst!(J)
    if char[j] == 0 && char[g+j] == 1
      M[j, g+j] = 1
    elseif char[j] == 1 && char[g+j] == 0
      M[g+j, j] = 1
    elseif char[j] == 1 && char[g+j] == 1
      I = findall(i -> char[i] == 1 && char[i+g] == 1, J)
      k = J[I[1]]
      filter!(x -> x != k, J)

      M[j, g + j] = 1
      M[k, j] = 1
      M[k, k] = 0
      M[k, g+j] = 1
      M[k, g+k] = 1
      M[g+j, k] = 1
      M[g+j, g+k] = 1
      M[g+k, k] = 1
    end
  end
  return M
end

#Compute the Gram matrix of the quadratic form associated to the 
#theta characteristic
function char_to_QF(char)
  g = div(length(char),2)
	id = identity_matrix(GF(2), g)
  zer = zero_matrix(GF(2), g, g)
  diag = diagonal_matrix(GF(2), char)
	J = [zer id ; zer zer]
  return J + diag
end 

#Compute the symplectic transformation that maps
#one even theta characteristic to another.
function map_even_characteristic(char1, char2)
  M1 = transform_to_arf_form(char1)
  M2 = transform_to_arf_form(char2)
  return M1 * inv(M2)
end

#Applies symplectic transformation M to char.
function apply_transformation_to_char(M, char)
  im_QF = transpose(M) * char_to_QF(char) * M
  return  diagonal(im_QF)
end

#Compute the orthogonal group with respect to the standard symplectic form.
function ortho_group(g)
	id = identity_matrix(GF(2), g)
  zer = zero_matrix(GF(2), g, g)
	J = [zer id ; zer zer]

  return isometry_group(quadratic_form(J))
end


