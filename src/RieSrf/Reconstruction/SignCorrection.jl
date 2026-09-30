
#=Correcting signs for reconstructing a curve

R, (x,y) = polynomial_ring(QQ, [:x,:y])
#This case has a Prym in a non-generic locus.
#f = -34*x^2*y^7 + 50*x^2*y^6 - 3*x^2*y^5 - 5*x^2*y^4 + 28*x^2*y^3 - 11*x^2*y^2 + 41*x^2*y - 19*x^2 + 47*x*y^7 - 43*x*y^5 + 14*x*y^4 - 37*x*y^3 + 17*x*y^2 + 27*x*y + x + 6*y^7 + 29*y^6 + 29*y^5 - 25*y^4 + 14*y^3 - 22*y^2 + 30*y + 43
f = 17*x^3*y^4 + 10*x^3*y^2 - 7*x^3 + 20*x^2*y^4 + 10*x^2*y^3 - 10*x*y^4 - 7*x*y - 15*x - 7*y^3 + 6*y
@time RS = riemann_surface(f, 200, integration_method = "heuristic")
g = genus(RS)
tau = small_period_matrix(RS)
CC = complex_field(RS)
z = zeros(CC, g)
@time thetas = Hecke.thetas(z, tau)
=#

function find_fixed_even_chars(g)
  chars = sort(even_theta_characteristics(g))
  char_vecs = collect.(chars)

  nr_of_even_thetas = length(chars)

  #Make a basis for Sp(2g)
  dim_of_Sp2g = g*(2*g+1)

  V = vector_space(GF(2), dim_of_Sp2g)

  #Make a sign flips matrix with the first row being the global sign flip.
  sign_flips = [[GF(2)(1) for i in (1:nr_of_even_thetas)]]

  #For each element T_v in the basis 
  #and make a 
  for v in basis(V)
    T_v = upper_triangular_matrix(v.v[1,:])
    #And for every character c, compute the quadratic form matching the sign flip: 
    #q_v​(c​)= transpose(c) *​(T_v) * ​c​
    #We put all the signs flips into a vector.
    flip_vector = [(transpose(c*T_v)*c) for c in char_vecs]
    push!(sign_flips, flip_vector)
  end

  #Create the sign_flip matrix and put it into echelon form
  A = matrix(sign_flips)
  A_ech = echelon_form(A)

  #Find a maximally linearly independent set of characters. Fixing the signs of these characteristics
  #determines all the others up to a sign.
  pivots = [minimum(filter( i -> A_ech[j,i] == one(GF(2)), (1:nr_of_even_thetas))) for j in (1:dim_of_Sp2g)]
  pivots_compl= filter(x -> !(x in pivots), (1:nr_of_even_thetas))

  fixed_chars = [ char_vecs[i] for i in pivots]
  non_fixed_chars = [ char_vecs[i] for i in pivots_compl]

  return fixed_chars, non_fixed_chars
end

#We won't need all quadruples for the relations. 
function find_zero_sum_tetrads(chars::Vector{Vector{Int}})
  n = length(chars)
  masks = [bitmask(v) for v in chars]

  # Bucket all pairs by their sum.
  buckets = Dict{UInt128, Vector{Tuple{Int,Int}}}()
  for i in (1:n - 1)
    for j in (i + 1:n)
      s = masks[i] ⊻ masks[j]
      push!(get!(buckets, s, Tuple{Int,Int}[]), (i, j))
    end
  end

  tetrads = Set{NTuple{4,Int}}()
  for pairs in values(buckets)
    k = length(pairs)
    k < 2 && continue
    for a in (1:k - 1) 
      for b in (a + 1:k)
        (i1, j1), (i2, j2) = pairs[a], pairs[b]
        push!(tetrads, Tuple(sort([i1, j1, i2, j2])))
      end
    end
  end
  return [(chars[i], chars[j], chars[k], chars[l]) for (i, j, k, l) in tetrads]
end

function find_correcting_matrices(g, thetas)
  thetas_prym = prym_thetas(g, thetas)
  fixed_thetas, non_fixed_thetas = find_fixed_even_chars(g-1)

  #Remove the thetas that are identically zero in case our Prym is not generic.
  filter!(x -> !contains(thetas_prym[x], zero(RR)), non_fixed_thetas)

  terms = find_zero_sum_tetrads(fixed_thetas)

  id = identity_matrix(GF(2), g-1)
  zer = zero_matrix(GF(2), g-1, g-1)
  J = [zer id ; zer zer]
  G = isometry_group(quadratic_form(J))

  old_rank = 0
  target_rank = length(non_fixed_thetas)

  N = length(terms)
  M = zero_matrix(GF(2), target_rank + 25,  2^(2*(g-1)));
  b = zero_matrix(GF(2), target_rank + 25, 1);

  r = 1
  mats = []
  for i in (1:N)
    println("I")
    println(i)
    fixed_term = [sort(char_to_index.(terms[i]))...]
    relations_from_fixed_term = Set([])

    #Use random matrices until we find all of the relations we can get
    #by applying an orthogonal matrix.

    while length(relations_from_fixed_term) < length(even_theta_characteristics(g-2))
      M0 = matrix(rand(G))
      test, rel, M1 = relation_with_term(g-1, thetas_prym, terms[i], M0)
      if test 
        #Ensure the fixed term is in the relation
        rel_indices = map(x -> x[1], rel)
        index = something(findfirst(x-> x == fixed_term, rel_indices), 0)
        if index != 0
          #Flip the sign of the relation to ensure that the fixed term has 
          #one as its coeffficient.
          sign = rel[index][2]
          for k in (1:length(rel))
            rel[k] = (rel[k][1], rel[k][2]*sign)
          end
          #Add the relation to the set.
          size = length(relations_from_fixed_term)
          push!(relations_from_fixed_term, (sort(rel), M1))
        end
      end
    end

    for (rel, M1) in collect(relations_from_fixed_term)
      
      #A relation is encoded as
      #[([4, 44, 64, 104], 1), ([12, 36, 72, 96], 1), ([134, 174, 194, 234], 1), ([159, 183, 219, 243], -1)]
      #For each term we create a new equation which we later want to solve as Mx = b.
      # r is the index of the current equation we want to add.
      for k in (1:length(rel))
        mon, coeff = rel[k]

        #Set the variables
        for j in mon
          M[r, j] = GF(2)(1)
        end

        #Check rank
        Mbr = M[:,char_to_index.(non_fixed_thetas)];
        new_rank = rank(Mbr)

        #If the rank increases, we add the relation
        if old_rank < new_rank 
          println(new_rank)
          old_rank = new_rank
          b[r, 1] = GF(2)(div(coeff-1,2))
          r+=1 
          push!(mats, M1)
        else 
          #If not we set the values back to 0 and do not increase r.
          for j in mon
            M[r, j] = GF(2)(0)
          end
        end
      end
    end
    Mbr = M[:,char_to_index.(non_fixed_thetas)];
    if rank(Mbr) >= target_rank
      println(i)
      break
    end
  end
  return mats
end