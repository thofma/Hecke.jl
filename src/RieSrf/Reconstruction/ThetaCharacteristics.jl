

# All theta constants theta[a, b](0, tau), keyed by tuples (a..., b...) in {0,1}^(2g)
function theta_constants(tau::AcbMatrix)
  CC = base_ring(tau)
  g = nrows(tau)
  return Hecke.thetas([zero(CC) for _ in 1:g], tau)
end

_is_even(ch) = iseven(sum(ch[i] * ch[i + div(length(ch), 2)] for i in 1:div(length(ch), 2)))

function number_of_odd_thetas(g)
  return 2^(g-1)*(2^g - 1) 
end

function number_of_even_thetas(g)
  return 2^(g-1)*(2^g + 1) 
end

# All odd theta characteristics
function odd_theta_characteristics(g::Int)
  Fg = Iterators.product(repeat([[0,1]], g)...)
  odd_chars = []
  for v1 in Fg    
    for v2 in Fg
      w1 = [i for i in v1]
      w2 = [i for i in v2]
      if mod(transpose(w1)*w2,2) == 1
        char = (w1..., w2...)
        push!(odd_chars, char)
      end
    end
  end
  return odd_chars
end

# All even theta characteristics
function even_theta_characteristics(g::Int)
  Fg = Iterators.product(repeat([[0,1]], g)...)
  even_chars = []
  for v1 in Fg    
    for v2 in Fg
      w1 = [i for i in v1]
      w2 = [i for i in v2]
      if mod(transpose(w1)*w2,2) == 0
        push!(even_chars, (w1..., w2...))
      end
    end
  end
  return even_chars
end

# Even characteristics whose theta constant vanishes (relative to the largest
# one): |theta| < 2^(-prec/2) max |theta|.
function _vanishing_even_theta_constants(thetas::Dict{NTuple{N, Int64}, AcbFieldElem}, prec::Int) where N
  big = maximum(_log2abs(v) for v in values(thetas))
  return [ch for (ch, v) in thetas if _is_even(ch) && _log2abs(v) < big - prec/2]
end

#Characteristic to index map.
#Conventions:
#     (0,0,0,1) -> 1
#     (0,1,0,1) -> 5
#and  (0,0,0,0) -> 16
function char_to_index(char::Vector{QQFieldElem})
  return char_to_index(map(x-> mod(x, 2), Int.(2*char)))
end

function char_to_index(char::Vector{Int})
  s = foldl((acc, x) -> (acc << 1) | x, char)
  if iszero(s)
    g = div(length(char), 2)
    return 2^(2*g)
  else
    return s
  end
end


function lift_prym_indices(g::Int)
  odds = odd_theta_characteristics(g-1)
  lifted = odd_theta_characteristics(g)
  result = []
  for char in odds
    delta_new1 = (0, char[1:g-1]..., 0, char[g:2*(g-1)]...)
    delta_new2 = (0, char[1:g-1]..., 1, char[g:2*(g-1)]...)
    i1 = findfirst(x-> x == delta_new1, lifted)
    i2 = findfirst(x -> x == delta_new2, lifted)
    push!(result, (i1,i2))
  end
  result
end


function quadratic_form_from_theta_char(char)
  g = div(length(char1),2)
	id = identity_matrix(GF(2), g)
  zer = zero_matrix(GF(2), g, g)
  diag = diagonal_matrix(GF(2), char)
	J = [zer id ; zer zer]
  return J + diag
end 


#Compute the arf normal form of a theta characteristic
function arf_normal_form(char)
  g = div(length(char1),2)
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
      I[1] = k 
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


function special_fundamental_system(azygetic::Vector)
  zero_block = zero_matrix(GF(2), 4,4)
	id = identity_matrix(GF(2), 4)
	J = [zero_block id id zero_block]
	J1 =[zero_block id zero_block zero_block]

	triangle = zero_matrix(GF(2), 4,4)
	for i in (1:4)
		for j in (i:4)
			triangle[i,j] = 1
		end
	end

	M = vcat(id, triangle)

  zero_1 = zero_matrix(GF(2), 4,1)
	zero_2 = zero_matrix(GF(2), 4,2)

	N = vcat(hcat(id, zero_2), hcat(zero_1, hcat(triangle, zero_1)))
	G = (matrix(GF(2), 6, 6, [1 for i in (1:36)]) + identity_matrix(GF(2), 6))
	N2 = N*G
	S = map_azygetic([transpose(M)[i,:] for i in (1:4)], azygetic)

	A, B, C, D = _split_in_blocks(S)
	vec = hcat(diagonal(B * transpose(A)), diagonal(D * transpose(C)))
	return [n + vec for n in transpose(S*N)(1:6)], [n + vec for n in transpose(S*N2)(1:6)], S
end