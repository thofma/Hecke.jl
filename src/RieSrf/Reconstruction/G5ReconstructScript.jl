


function manual_kernel(M)
  T  = Complex{Float64x2}          # ~128 digits; Float64x4 ≈ 64 digits
  A  = T.(M)                   # your Complex{BigFloat} matrix, odd columns only
  A0 = ComplexF64.(A)              # or Complex{Float64x2} if Float64 is too coarse

  # 1. Rank and pivot choice (cheap)
  Fc = qr(A0, ColumnNorm())
  d  = abs.(diag(Fc.R));  r = count(>(1e-10 * d[1]), d)   # inspect the gap in d!

  F = qr(copy(A'))                       # n×m Householder QR, O(n·m²)
  n = ncols(A)
  E = zeros(T, n, n - r)
  for j in 1:n-r
      E[r+j, j] = one(T)
  end
  N = F.Q * E  
  return N
end


GF2 = GF(2)
odds = odd_theta_characteristics(g-1)

odd_prym_indices = char_to_index.(collect.(odd_theta_characteristics(g-1)))
odd_indices = char_to_index.(collect.(odd_theta_characteristics(g)))

rho1 = GF2.([1,0,0,0,0,0,0,0,0,0])
rho2 = GF2.([1,1,0,0,0,0,1,0,0,1])
rho3 = GF2.([0,1,0,1,0,0,1,1,0,0])
rho4 = GF2.([0,1,0,0,1,0,0,0,0,1])
rho5 = GF2.([1,1,1,1,1,1,1,1,1,1])
rho6 = GF2.([1,0,1,1,1,0,1,1,0,1])
rho7 = GF2.([1,0,1,0,1,1,0,1,0,1])
rho8 = GF2.([0,0,1,0,1,1,0,1,0,0])

R = [rho1, rho2, rho3, rho4, rho5, rho6, rho7, rho8]

bigM = Vector{AcbFieldElem}[]

for r in R
  M = construct_fay_matrix(g, thetas, r)
  bigM = [bigM ; M]
end

bigM_prym = Vector{AcbFieldElem}[]

rho1 = GF2.([1,0,0,0,0,0,0,0])
rho2 = GF2.([1,1,0,0,0,1,0,1])
rho3 = GF2.([0,1,1,0,0,1,1,0])
rho4 = GF2.([0,1,0,1,0,0,0,1])
rho5 = GF2.([1,1,1,1,1,1,1,1])
rho6 = GF2.([1,0,1,1,0,1,0,1])
rho7 = GF2.([1,0,0,1,1,1,0,1])
rho8 = GF2.([0,0,1,1,1,0,0,0])

R = [rho1, rho2, rho3, rho4, rho5, rho6, rho7, rho8]

prec = 150
setprecision(BigFloat, prec)

for r in R
  M_prym = construct_fay_matrix(g-1, thetas_prym, r)
  bigM_prym = [bigM_prym ; M_prym]
end

bigM_float = (x->Complex{Float64x2}(Complex{BigFloat}(x))).(collect(matrix(bigM)[:,odd_indices]))
K = manual_kernel(bigM_float;prec = :x2)[1]
K = permutedims(nullspace(bigM_float))


bigM_float_prym = Complex{BigFloat}.(collect(matrix(bigM_prym)[:,odd_prym_indices]))
K_prym = manual_kernel(bigM_float_prym;prec = :x2)[1]

I = lift_prym_indices(g)


HiHis = []
for i in (1:length(odds)) 
  i1, i2 = I[i]
  L = K[i1,:] * transpose(K[i2, :])
  LL = L + transpose(L)
  HiHi = reduce(vcat, [[LL[i,j] for i in (j:g)] for j in (1:g)])

  push!(HiHis, HiHi)
end

li_sqs = []
for i in (1:length(odds)) 
  L = K_prym[i,:] * transpose(K_prym[i, :])
  li_sq = reduce(vcat, [[L[i,j] for i in (j:g-1)] for j in (1:g-1)])
  push!(li_sqs, li_sq)
end

HiHis2 = mapreduce(permutedims, vcat, HiHis)
li_sqs2 = mapreduce(permutedims, vcat, li_sqs)
O = manual_kernel(permutedims(li_sqs2);prec = :x2)[1]
TT =  permutedims(O) * HiHis2
rank(TT)

svd(TT)


#Correcting signs (in the g = 4 case) for reconstructing a genus 5 curve.

R, (x,y) = polynomial_ring(QQ, [:x,:y])
f = 2*x^5*y^3 + 5*x^4*y^3 - 9*x^4*y^2 + 3*x^3*y - 4*x^2*y^2 - 3*x*y^3 + 1
@time RS = riemann_surface(f, 200, integration_method = "heuristic")
g = genus(RS)
tau = small_period_matrix(RS)
CC = complex_field(RS)
z = zeros(CC, g)
@time thetas = Hecke.thetas(z, tau)

thetas_prym = prym_thetas(g, thetas)
fixed_thetas, non_fixed_thetas = find_fixed_even_chars(g-1)
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
for i in (1:N)
  fixed_term = [sort(char_to_index.(terms[i]))...]
  relations_from_fixed_term = Set([])

  #Use random matrices until we find all of the relations we can get
  #by applying an orthogonal matrix.
  while length(relations_from_fixed_term) < 6
    M0 = matrix(rand(G))
    test, rel, _ = relation_with_term(g-1, thetas_prym, terms[i], M0)
    unique_rels = Set([])
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
        push!(relations_from_fixed_term, sort(rel))
      end
    end
  end

  for rel in collect(relations_from_fixed_term)

    #A relation is encoded as
    #[([4, 44, 64, 104], 1), ([12, 36, 72, 96], 1), ([134, 174, 194, 234], 1), ([159, 183, 219, 243], -1)]
    #For each term we create a new equation which we later want to solve as Mx = b.
    # r is the index of the current equation we want to add.
    for k in (1:4)
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
        println(mon)
        old_rank = new_rank
        b[r, 1] = GF(2)(div(coeff-1,2))
        r+=1 
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

Mbr = M[:,char_to_index.(non_fixed_thetas)];

v =  solve(Mbr, b, side = :right)

for j in (1:length(v))
  thetas_prym[non_fixed_thetas[j]...] *= ZZ(-1)^(lift(ZZ,v[j]))
end

for i in (1:N)
  println(relation_with_term(g-1, thetas_prym, terms[i], identity_matrix(GF(2), 2*(g-1))))
end





#Correcting signs (in the g = 5 case) for reconstructing a genus 6 curve.

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

thetas_prym = prym_thetas(g, thetas)
fixed_thetas, non_fixed_thetas = find_fixed_even_chars(g-1)

#Remove the thetas that are identically zero in case our Prym is not generic.
filter!(x -> !contains(thetas_prym(char), zero(RR)), non_fixed_thetas)

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
  misses = 0

  #while misses < 5
  while length(relations_from_fixed_term) < 36
    M0 = matrix(rand(G))
    test, rel, M1 = relation_with_term(g-1, thetas_prym, terms[i], M0, 9)
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
        push!(relations_from_fixed_term, sort(rel))
        if length(relations_from_fixed_term) == size 
          misses+=1
        else
          misses = 0
          push!(mats, M1)
        end
      end
    end
  end

  for rel in collect(relations_from_fixed_term)
    
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

Mbr = M[:,char_to_index.(non_fixed_thetas)];

v =  solve(Mbr, b, side = :right)

for j in (1:length(v))
  thetas_prym[non_fixed_thetas[j]...] *= ZZ(-1)^(lift(ZZ,v[j]))
end

for i in (1:N)
  println(relation_with_term(g-1, thetas_prym, terms[i], identity_matrix(GF(2), 2*(g-1))))
end

L = Set([])
L2 = Set([])
lengths = Set([])
last = 0
last2 = 0
while true
  gr = rand(G)
  test, rel = relation_with_term(g-1, thetas_prym, terms[1], matrix(gr), 21)
  if test 
    rell = map(x->x[1], rel)
    push!(L, rell)
    push!(lengths, length(rell))
    if length(L)>last
        last = length(L)
        println(last)
      end
    for mon in rell
      push!(L2, mon)
      if length(L2)>last2
        last2 = length(L2)
        println(last2)
      end
    end
  end
end


  theta_indices = Hecke.theta_characteristics_indices(g)
  theta_indices = [[theta_indices[i+1]...] for i in (1:2^(2*g)-1)]
  push!(theta_indices, zeros(Int, 2*g))

#=
Statistics:
g = 4

10 characteristics show up

15 relations with 4 terms 
6 equations with a fixed term

g = 5

36 characteristics that show up

336 relations with 6 terms 
56 of them with a fixed term

945 relations with 8 terms
210 of them with a fixed term
=#


R, (x,y) = polynomial_ring(QQ, [:x,:y])
#This case has a Prym in a non-generic locus.
#f = -34*x^2*y^7 + 50*x^2*y^6 - 3*x^2*y^5 - 5*x^2*y^4 + 28*x^2*y^3 - 11*x^2*y^2 + 41*x^2*y - 19*x^2 + 47*x*y^7 - 43*x*y^5 + 14*x*y^4 - 37*x*y^3 + 17*x*y^2 + 27*x*y + x + 6*y^7 + 29*y^6 + 29*y^5 - 25*y^4 + 14*y^3 - 22*y^2 + 30*y + 43
f = x^6 + x^3*y - x^2*y^3 - 3*x^2*y^2 - 2*x^2*y + 2*x*y^4 + 3*x*y^3 + x*y^2 - y^5 - y^4
@time RS = riemann_surface(f, 200, integration_method = "heuristic")
g = genus(RS)
tau = small_period_matrix(RS)
CC = complex_field(RS)
z = zeros(CC, g)
@time thetas = Hecke.thetas(z, tau)