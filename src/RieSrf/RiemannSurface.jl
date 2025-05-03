################################################################################
#
#          RieSrf/RiemannSurface.jl : Riemann surfaces
#
# (C) 2022 Jeroen Hanselman
#
################################################################################


export RiemannSurface, discriminant_points, embedding, genus, precision, fundamental_group_of_punctured_P1, monodromy_representation, monodromy_group, homology_basis

export max_radius, radius_factor, find_paths_to_end, sheet_ordering, embed_mpoly, analytic_continuation, minimal_spanning_tree

mutable struct RiemannSurface
  defining_polynomial::MPolyRingElem
  genus::Int
  tau::acb_mat
  prec::Int
  embedding::Union{PosInf, InfPlc}
  discriminant_points::Vector{acb}
  fundamental_group_of_P1::Tuple{Vector{CPath}, Vector{Vector{Int}}}
  function_field::AbstractAlgebra.Generic.FunctionField
  basis_of_differentials::Vector{Any}
  weak_error::arb
  error::arb
  extra_error::arb
  real_field::ArbField
  complex_field::AcbField
  complex_field2::AcbField
  computational_precision_complex_field::AcbField
  max_precision_complex_field::AcbField
  integration_schemes::Vector{IntegrationScheme}
  monodromy_representation::Vector{Tuple{Vector{CPath}, Perm{Int64}}}
  homology_basis::Tuple{Vector{Vector{Int64}}, ZZMatrix, ZZMatrix}
  degree::Vector{Int}
  evaluate_differential_factors_matrix::Any
  baker_basis::Bool
  differential_form_data::Any
  bounds::Vector{arb}

  function RiemannSurface(f::MPolyRingElem, v::T, prec = 100) where T<:Union{PosInf, InfPlc}
    K = base_ring(f)
    
    RS = new()
    RS.defining_polynomial = f
    RS.prec = prec
    RS.embedding = v
    
    k = base_ring(f)
    kx, x = rational_function_field(k, "x")
    kxy, y = polynomial_ring(kx, "y")
    f_new = f(x, y)
    F, a = function_field(f_new)
    diff_base = basis_of_differentials(F)
    RS.function_field = F
    RS.basis_of_differentials = diff_base
    g = length(diff_base)
    RS.genus = g



    inner_fac = inner_faces(f)
    if length(inner_fac) == g
      RS.baker_basis = true
      x, y = gens(parent(f))
      factor_set = [x, y, derivative(f, 2)]
      n = length(factor_set)
      min_x = minimum([t[1] for t in inner_fac])
      max_x = maximum([t[1] for t in inner_fac])
      min_y = minimum([t[2] for t in inner_fac])
      max_y = maximum([t[2] for t in inner_fac])
      min_pows = [min_x - 1, min_y - 1, -1]
	    range_pows = [max_x - 1, max_y - 1, -1] - min_pows

      factor_matrix = zero_matrix(Int, n, g)
      
      for i in (1:g)
        factor_matrix[1, i] = inner_fac[i][1] - 1
        factor_matrix[2, i] = inner_fac[i][2] - 1
        factor_matrix[3, i] = -1
      end 

    else
      RS.baker_basis = false
      factor_set = Set()
      factored_nums = []
      factored_denoms = []
      #Gather all the factors occurring in the basis of differential forms
      for i in 1:g
        num_diff_i_fac = factor(numerator(diff_base[i].f)).fac
        denom_diff_i_fac = factor(denominator(diff_base[i].f)).fac

        union!(factor_set, Set(keys(num_diff_i_fac)), Set(keys(denom_diff_i_fac)))

        push!(factored_nums, num_diff_i_fac)
        push!(factored_denoms, denom_diff_i_fac)
      end
    
      #Turn set into sequence so we can enumerate
      factor_set = collect(factor_set)
      number_of_factors = length(factor_set)
      n = length(factor_set)
      factor_matrix = zero_matrix(Int, n, g)
      for j in 1:g
        for i in 1:n
          if haskey(factored_nums[j], factor_set[i])
            factor_matrix[i,j] = get(factored_nums[j], factor_set[i], 0)
          end

          if haskey(factored_denoms[j], factor_set[i])
            factor_matrix[i,j] = -get(factored_denoms[j], factor_set[i], 0)
          end
        end
      end 

		  min_pows= [minimum( [factor_matrix[j, 1:g] for j in 1:n])]
	    range_pows= [maximum( [factor_matrix[j, 1:g] for j in 1:n])] - min_pows
    end

    function evaluate_differential_factors_matrix(factors, x0, ys)
      Kxy = parent(factors[1])
      Ky, y = polynomial_ring(base_ring(Kxy), "y")
      CC = base_ring(factors[1])
      m = length(ys)

      result = matrix(CC, m , g, [one(CC) for t in (1:m*g)])
      for l in 1:length(factors)
        f = factors[l]
        fx0 = f(x0, y)
        for s in 1:m
          fx0ys = CC(fx0(ys[s]))
          factor_at_xys = [fx0ys^min_pows[l] ]
          for k in (1:range_pows[l])
            push!(factor_at_xys, factor_at_xys[k]*fx0ys)
          end
          for k in 1:g
            #Let omega_i = g_i * dx where the omega form a basis of 
            #differentials. Then result[s][k] = g_k(x0, ys) where the
            #ys are the m preimages in the fiber f^(-1)(x0).
            result[s, k] *= factor_at_xys[factor_matrix[l, k] - min_pows[l]+1]
          end
        end
      end
      return result
      end

    RS.differential_form_data = (factor_set, factor_matrix, min_pows, range_pows)
    RS.evaluate_differential_factors_matrix = evaluate_differential_factors_matrix

    b10_prec = floor(Int, prec*log(2)/log(10))
    b10_extra_prec = b10_prec + 3 + max(degree(f, 1), degree(f, 2))
    extra_prec = floor(Int, (3 + max(degree(f, 1), degree(f, 2)) *log(2)/log(10)))
    RS.complex_field = AcbField(prec)
    Rc = ArbField(prec + extra_prec)
    RS.real_field = Rc
    
    
    
    RS.weak_error = Rc(10)^(-(2//3) *b10_prec)
    RS.error = Rc(10)^(-b10_prec - 1)
    RS.extra_error = Rc(10)^(-b10_extra_prec - 1)
    RS.bounds = []
    RS.degree = degrees(f)

    return RS
  end
end


################################################################################
#
#  Constants
#
################################################################################

function max_radius(RS::RiemannSurface)
  return ArbField(precision(RS))(1//4)
end

function radius_factor(RS::RiemannSurface)
  return ArbField(precision(RS))(2//5)
end


################################################################################
#
#  Getter functions
#
################################################################################


function defining_polynomial(RS::RiemannSurface)
  return RS.defining_polynomial
end

function defining_polynomial_univariate(RS::RiemannSurface)
  f = defining_polynomial(RS)
  K = base_ring(f)
  Kx, x = polynomial_ring(K, "x")
  Kxy, y = polynomial_ring(Kx, "y")
  
  return f(x, y)
end

function genus(RS::RiemannSurface)
  return RS.genus
end

function embedding(RS::RiemannSurface)
  return RS.embedding
end

function precision(RS::RiemannSurface)
  return RS.prec
end

function function_field(RS::RiemannSurface)
  return RS.function_field
end

function basis_of_differentials(RS::RiemannSurface)
  return RS.basis_of_differentials
end

function assure_has_discriminant_points(RS::RiemannSurface)
  if isdefined(RS, :discriminant_points)
    return nothing
  else
    f = defining_polynomial_univariate(RS)
    Kxy = parent(f)
    Kx = base_ring(f)
  
    v = embedding(RS)
    prec = precision(RS)
  
    disc_y_factors = acb_poly[]
    a0_factors = acb_poly[]
  
    for (f,e) in factor(discriminant(f))
      push!(disc_y_factors, embed_poly(f, v, prec))
    end
  
    for (f,e) in factor(leading_coefficient(f))
      push!(a0_factors, embed_poly(f, v, prec))
    end
  
    D1 = vcat(acb[],[roots(fac, initial_prec = prec) for fac in disc_y_factors]...)
    D2 = vcat(acb[],[roots(fac, initial_prec = prec) for fac in a0_factors]...)
    D_points = sort!(vcat(D1, D2), lt = sheet_ordering)
    RS.discriminant_points = D_points

    #TODO:Compute max precision dynamically based on size of |x| and |f(x)| for x in discriminant points
    RS.max_precision_complex_field = AcbField(700)

    return nothing
  end
end

function discriminant_points(RS::RiemannSurface, copy::Bool = true)
  assure_has_discriminant_points(RS)
  if copy
    return deepcopy(RS.discriminant_points)
  else
    return RS.discriminant_points
  end
end




################################################################################
#
#  Monodromy computation
#
################################################################################

function monodromy_representation(RS::RiemannSurface)
  if isdefined(RS, :monodromy_representation)
    return RS.monodromy_representation
  else
    return _monodromy_representation(RS)
  end
end

function _monodromy_representation(RS::RiemannSurface)
  paths, pi1_gens = fundamental_group_of_punctured_P1(RS, true)
  f = defining_polynomial(RS)
  m = degree(f, 2)
  
  s_m = SymmetricGroup(m)
  
  for i in (1:length(paths))
    path = paths[i]
    N = ceil(Int, length(path)) +1
    if path_type(path) in [1,2]
      N *= 4
    end
      
      
    Rc = ArbField(precision(RS))
     
    abscissae = [Rc(n//N) for n in (-N + 1: N - 1)] 
     
    An = analytic_continuation(RS, path, abscissae)
    
    path_perm = sortperm(An[end][2], lt = sheet_ordering)
    assign_permutation(path, inv(s_m(path_perm)))
  end
  
  mon_rep = Tuple{Vector{CPath}, Perm{Int64}}[]
  
  for gamma in pi1_gens
    chain = map(t -> ((t > 0) ? paths[t] : reverse(paths[-t])), gamma)
    gamma_perm = prod(map(permutation, chain))
    
    if gamma_perm != one(s_m)
      push!(mon_rep, (chain, gamma_perm))
     end
  end
  
  inf_chain = Vector{CPath}[]
  inf_perm = one(s_m)
  
  for g in mon_rep
    inf_chain = vcat(inf_chain, map(reverse, g[1]))
    inf_perm *= g[2]
  end
  
  push!(mon_rep, (reverse(inf_chain), inv(inf_perm)))
  RS.monodromy_representation = mon_rep
  return mon_rep
  
end

function monodromy_group(RS::RiemannSurface)
  mon_rep = monodromy_representation(RS)
  gens = map(t -> t[2], mon_rep)
  return closure(gens, *)
end

function fundamental_group_of_punctured_P1(RS::RiemannSurface, abel_jacobi::Bool = true)
  if isdefined(RS, :fundamental_group_of_P1)
    return RS.fundamental_group_of_P1
  else
    return _fundamental_group_of_punctured_P1(RS, abel_jacobi)
  end
end

#Follows algorithm 4.3.1 in Neurohr
function _fundamental_group_of_punctured_P1(RS::RiemannSurface, abel_jacobi::Bool = true)
  
  #Compute the exceptional values x_i
  D_points = discriminant_points(RS)
  d = length(D_points)
  Cc = parent(D_points[1])
  Rc = ArbField(precision(RS))
  
  #Step 1 compute a minimal spanning tree
  edges = minimal_spanning_tree(D_points)
  
  #Choose a suitable base point and connect it to the spanning tree

  #Multiple ways to choose the base point. 
  #This one is most suitable when computing abel-jacobi maps. 
  #Take some integer point to the left of the point with the smallest real part
    
  
  if abel_jacobi
    
    #Real part should already be minimal in D_points
    x0 = Cc(min(floor(ZZRingElem, real(D_points[1]) - 2*max_radius(RS)), -1))
    
    
    #Connect base point to closest point in D_points
    closest = 1
    distance = abs(x0 - D_points[1])
    for i in (2:length(D_points))
      new_distance = abs(x0 - D_points[i])
      if distance > new_distance
        closest = i
        distance = new_distance
      end
    end
    push!(D_points, x0)
    push!(edges, (d +1, closest))
  else
  #Here we take the one that is most suitable if one doesn't need to compute Abel-Jacobi maps according to Neurohr, i.e. we split the longest edge in the middle. 
  #(Last edge should be the longest in the way we compute minimal_spanning trees right now.)
    
    left = edges[end][1]
    right = edges[end][2]
    pop!(edges)
    x0 = (D_points[left] + D_points[right])//2
    push!(D_points, x0)
    push!(edges, (d + 1, left))
    push!(edges, (d + 1, right))
  end
  #Now we sort the points by angle and level

  path_edges = Int[]
  past_nodes = [d + 1]
  current_node = d + 1
  
  left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
  right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse,edges))
  
  leftright = vcat(left_edges, right_edges)
  
  current_angle = zero(Rc)
  
  angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
    return mod2pi(angle(D_points[t1[2]] - D_points[t1[1]]) - current_angle) < mod2pi(angle(D_points[t2[2]] - D_points[t2[1]]) - current_angle)
  end
      
  sort!(leftright, lt = angle_ordering)
  
  path_edges = vcat(path_edges, leftright)
  current_level = vcat(left_edges, right_edges)
  
  while length(path_edges) < length(edges)
    next_level = Int[]
    for edge in current_level
    
      previous_node = edge[1]
      current_node = edge[2]
      current_angle = angle(D_points[previous_node] - D_points[current_node])
      
      left_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), edges)
      right_edges = filter(t -> t[1] == current_node && !(t[2] in past_nodes), map(reverse, edges))
      leftright = vcat(left_edges, right_edges)
    
      angle_ordering = function(t1::Tuple{Int, Int}, t2::Tuple{Int, Int})
        return mod2pi(angle(D_points[t1[2]] - D_points[t1[1]]) - current_angle) < mod2pi(angle(D_points[t2[2]] - D_points[t2[1]]) - current_angle)
      end
      
      sort!(leftright, lt = angle_ordering)
      next_level = vcat(next_level, leftright)
      path_edges = vcat(path_edges, leftright)
      
      push!(past_nodes, current_node) 
    end
    
    current_level = next_level
  end
  
  #Construct paths to every end point starting at x0 using a Depth-First Search
  
  #Paths to all nodes
  paths = [[(d+1, d+1)]]
  
  ordered_disc_points = []
  find_paths_to_end([(d+1, d+1)], paths, path_edges, ordered_disc_points)
  ordered_disc_points = map(t -> D_points[t], ordered_disc_points)
  
  radii = [min(max_radius(RS), radius_factor(RS) * minimum(map(t -> abs(t - D_points[j]), vcat(D_points[1:j-1], D_points[j+1:end])))) for j in (1:d)]
  
  c_lines = CPath[]
  
  
  #Find the line pieces of the paths.
  for edge in path_edges
    a = D_points[edge[1]]
    b = D_points[edge[2]]
    ab_length = b - a
    
    #Base point is not a discriminant point, so we don't need to circle around it
    if edge[1] == d + 1
      new_start_point = a
    else
      #Intersect the line between a and b with the circle of radius r_a around a
      new_start_point = a + (radii[edge[1]])*ab_length//(abs(ab_length))
    end
    #Intersect the line between a and b with the circle of radius r_b around b
    new_end_point = b - (radii[edge[2]])*ab_length//(abs(ab_length))
    push!(c_lines, c_line(new_start_point, new_end_point))
  end
  
  paths = map(t -> t[2:end], paths[2:end])
  path_indices = map(path -> map(t -> findfirst(x -> x == t, path_edges), path), paths)

  c_arcs = CPath[]
  paths_with_arcs = Vector{Int}[]
  
  #We reconstruct the paths 
  for path in reverse(path_indices)
    
    i = path[end]
    loop = Int[]
    
    arc_start = arc_end = end_point(c_lines[i])
    center = D_points[path_edges[i][end]]
    
    #We need to loop around the end of the path, but we may
    #have already constructed parts of the loop when constructing previous paths
    #We therefore find these first and add them.
    
    n = length(c_arcs)
    for j in (1:n)
      arc = c_arcs[j]
      if contains(arc_end, end_point(arc)) && contains(end_point(arc), arc_end)
        push!(loop, j + d)
        arc_end = start_point(arc)
      end
    end
    
    push!(c_arcs, c_arc(arc_start, arc_end, center))
    push!(loop, d + n + 1)

    path_to_loop = Int[]

    #Now we attach the line piece
    push!(path_to_loop, i)
   
    #We add the inverse arcs as moving towards the points we want to encircle we move clockwise 
    for k in (length(path)-1:-1:1)  
    
      arc_buffer = Int[]
      old_line_piece = c_lines[path[k+1]]
      new_line_piece = c_lines[path[k]]
      arc_start = start_point(old_line_piece)
      arc_end = end_point(new_line_piece)
      center = D_points[path_edges[path[k]][end]]
   
     #Similar to before. Maybe make a function out of it
      n = length(c_arcs)
      for j in (1:n)
        arc = c_arcs[j]
        if contains(arc_end, end_point(arc)) && contains(end_point(arc), arc_end)
          push!(arc_buffer, -j - d)
          arc_end = start_point(arc)
        end
      end
     
      if arc_start != arc_end
        push!(c_arcs, c_arc(arc_start, arc_end, center))
        push!(arc_buffer, - d - n - 1)
      end
     
      path_to_loop = vcat(path_to_loop, reverse(arc_buffer))
      push!(path_to_loop, path[k])
    end
    push!(paths_with_arcs, vcat(reverse(path_to_loop), reverse(loop), -path_to_loop))
  end
  
  pi1 = vcat(c_lines, c_arcs), reverse(paths_with_arcs)
  RS.fundamental_group_of_P1 = pi1
  return vcat(c_lines, c_arcs), reverse(paths_with_arcs)
end

function find_paths_to_end(path, paths, edges, ordered_disc_points)
  end_path = path[end][2]
  temp_paths = paths
  for (start_edge, end_edge) in edges
    if start_edge == end_path
      push!(ordered_disc_points, end_edge)
      newpath = vcat(path, [(start_edge, end_edge)])
      push!(paths, newpath)
      find_paths_to_end(newpath, paths, edges, ordered_disc_points)
    end
  end 
end


#Could be optimized probably. Kruskal's algorithm
function minimal_spanning_tree(v::Vector{acb})

  edge_weights = []
  
  N = length(v)
  
  #Compute the weights for all the edges
  for i in (1:N)
    for j in (i+1: N)
      push!(edge_weights, (abs(v[i] - v[j]), (i, j)))
    end
  end
  
  sort!(edge_weights) 
  
  tree = Tuple{Int, Int}[]
  
  disjoint_trees = [Set([i]) for i in (1:N)]
  
  i = 1
  
  while length(tree) < N - 1
  
    (s1, s2) = edge_weights[i][2]
    
    s1_index = findfirst(t -> s1 in t, disjoint_trees)
    
    s1_tree = disjoint_trees[s1_index]
    
    if s2 in s1_tree
      #continue
    else
      s2_tree = popat!(disjoint_trees, findfirst(t -> s2 in t, disjoint_trees))
      push!(tree, (s1, s2))
      union!(s1_tree, s2_tree) 
    end
    i+= 1
  end
  
  return tree
end


################################################################################
#
#  Analytic Continuation
#
################################################################################

function analytic_continuation(RS::RiemannSurface, path::CPath, abscissae::Vector{arb}, start_ys::Vector{acb}=acb[])
  v = embedding(RS)
  prec = precision(RS)
  Rc = ArbField(prec)
  
  f = embed_mpoly(defining_polynomial(RS), v, prec)
  Cc = base_ring(f)
  
  f = change_base_ring(Cc, f, parent = parent(f))

  m = degree(f, 2)
  
  u = vcat([-one(Rc)], abscissae, [one(Rc)])
  N = length(u)
  
  x_vals = zeros(Cc, N)
  dx_vals = zeros(Cc, N)
  y_vals = [zeros(Cc, m) for i in (1:N)]

  z = zeros(Cc, m)

  x_vals[1] = evaluate(path, u[1])

  Kxy = parent(f)
  Ky, y = polynomial_ring(base_ring(Kxy), "y")
  
  if length(start_ys) == 0
    y_vals[1] = sort!(roots(f(x_vals[1], y), initial_prec = prec), lt = sheet_ordering)
  else
    y_vals[1] = start_ys
  end
  for l in (2:N)
    x_vals[l] = evaluate(path, u[l])
    z .= y_vals[l-1]
    y_vals[l] .= recursive_continuation(f, x_vals[l-1], x_vals[l], z)
  end
  return collect(zip(x_vals, y_vals))
end

function recursive_continuation(f, x1, x2, z)
  Kxy = parent(f)
  Ky, y = polynomial_ring(base_ring(Kxy), "y")
  Cc = base_ring(f)
  prec = precision(Cc)
  m = degree(f, 2)
  temp_vec = acb_vec(m)
  temp_vec_res = acb_vec(m)
  d = reduce(min, [abs(z[i] - z[j]) for (i, j) in filter(t-> t[1] != t[2], [a for a in Iterators.product((1:m), (1:m))])]) 
  W = [ f(x2, z[i]) // prod([z[i] - z[j] for j in vcat((1:i - 1), i+1:m)];init = one(Cc)) for i in (1:m)]
  w = reduce(max, map(t -> real(t)^2 +imag(t)^2, W))
  
  if w < d // (2*m)
    fillacb!(temp_vec, z)
    dd = ccall((:acb_poly_find_roots, libarb), Cint, (Ptr{acb_struct}, Ref{acb_poly}, Ptr{acb_struct}, Int, Int), temp_vec_res, f(x2, y), temp_vec, 0, prec)

    @assert dd == m
    z .= array(Cc, temp_vec_res, m)
    
    acb_vec_clear(temp_vec, m)
    acb_vec_clear(temp_vec_res, m)
    
    return z
  else
    midpoint = (x1 + x2)//2
    return recursive_continuation(f, midpoint, x2, recursive_continuation(f, x1, midpoint, z))
  end
  
end

################################################################################
#
#  Homology basis
#
################################################################################

function homology_basis(RS::RiemannSurface)
  if isdefined(RS, :homology_basis)
    return RS.homology_basis
  end
  return _homology_basis(RS)
end

function _homology_basis(RS::RiemannSurface)
  mon_rep = monodromy_representation(RS)
  gens = map(t -> t[2], mon_rep)
  s_n = parent(gens[1])
  n = s_n.n
  d = length(gens)
  
  ramification_points = Tuple{Int64, SubArray{Int64, 1, Vector{Int64}, Tuple{UnitRange{Int64}}, true}, Perm{Int64}}[]
  ramification_indices = Int[]
  
  for i in (1:d)
    for cyc in cycles(gens[i])
      push!(ramification_points, (i, cyc, s_n("("*string(cyc)[2:end-1]*")")))
      push!(ramification_indices, length(cyc) - 1)
    end
  end

  genus = -n + 1 + divexact(sum(ramification_indices;init = zero(Int)), 2)
  
  all_branches_terminated = false
  ram_pts_nr = length(ramification_points)
  vertices = Set([ram_pts_nr+1])
  edges_on_level = Vector{TretkoffEdge}[]
  terminated_edges = TretkoffEdge[]
  
  level = 1
  push!(edges_on_level, [])
  
  for i in (1:ram_pts_nr)
    if 1 in ramification_points[i][2]
      edge = TretkoffEdge(ram_pts_nr + 1, i, level, [ram_pts_nr + 1, i])
      push!(vertices, i)
      push!(edges_on_level[level], edge)
    end
  end
  while !all_branches_terminated
    level += 1
    push!(edges_on_level, [])
    
    s = 0
    
    for edge in edges_on_level[level - 1]
      if !is_terminated(edge)
        start_perm = ramification_points[end_point(edge)][3]
        perm = start_perm
        start_sheet = start_point(edge) - ram_pts_nr
        while !is_one(perm)
          new_sheet = perm[start_sheet] + ram_pts_nr
          if !(new_sheet in branch(edge))
            new_edge = TretkoffEdge(end_point(edge), new_sheet, level, vcat(branch(edge), new_sheet))
            s+=1
            set_position(new_edge, s)
            push!(edges_on_level[level], new_edge)
          end
          perm *= start_perm 
        end 
      end
    end
    
    sorted_edges = sort(edges_on_level[level], lt = (a,b) -> start_point(a) < start_point(b))
    for edge in sorted_edges
      if end_point(edge) in vertices
        terminate(edge)
        push!(terminated_edges, edge)
      else
        push!(vertices, end_point(edge))
      end
    end
    
    level += 1
    push!(edges_on_level, [])
    
    s = 0
    
    for edge in edges_on_level[level - 1]
      if !is_terminated(edge)
        l = end_point(edge) - ram_pts_nr
        k = mod(start_point(edge), ram_pts_nr) + 1
        
        for i in (1:ram_pts_nr)
          if (l in ramification_points[k][2]) && !(k in branch(edge))
            new_edge = TretkoffEdge(end_point(edge), k, level, vcat(branch(edge), k))
            s+=1
            set_position(new_edge, s)
            push!(edges_on_level[level], new_edge)
          end
          k = mod(k, ram_pts_nr) + 1
        end 
      end
    end
    
    sorted_edges = sort(edges_on_level[level], lt = (a,b) -> end_point(a) < end_point(b))
    for edge in sorted_edges
      if end_point(edge) in vertices
        terminate(edge)
        push!(terminated_edges, edge)
      else
        push!(vertices, end_point(edge))
      end
    end
    
    all_branches_terminated = true
    for edge in edges_on_level[level]
      if !is_terminated(edge)
        all_branches_terminated = false
      end
    end
    
  end
  
  terminated_edges_nr = (4*genus + 2*n - 2)
  PQ_size = divexact(terminated_edges_nr, 2)
  @req length(terminated_edges) == terminated_edges_nr "The number of terminated edges is wrong. There is a bug in the code."
  
  function compare_branches(e1::TretkoffEdge, e2::TretkoffEdge)
    l1 = edge_level(e1)
    l2 = edge_level(e2)
    if l1 == l2
      return get_position(e1) < get_position(e2)
    elseif l1 < l2
    
      e_temp = TretkoffEdge(branch(e2)[l1], branch(e2)[l1 + 1])
      i = findfirst(is_equal(e_temp), edges_on_level[l1])
      return compare_branches(e1, edges_on_level[l1][i])
    else
      return !compare_branches(e2, e1)
    end
  end
  
  sort!(terminated_edges, lt = compare_branches)
  
  reverse!(terminated_edges)
  
  P = TretkoffEdge[]
  QQ = TretkoffEdge[]
  Q = Vector{TretkoffEdge}(undef, PQ_size)
  l = 1
  
  for k in (1:terminated_edges_nr)
    edge = terminated_edges[k]
    set_position(edge, k)
    if PQ(edge)
      push!(P, edge)
      set_label(edge, l)
      l +=1
    else
      push!(QQ,edge)
    end
  end
  
  for edge in QQ
    l = findfirst(is_equal(reverse(edge)), P)
    set_label(edge, l)
    Q[l] = edge
  end
  
  cycles_list = Vector{Int}[]
  
  for i in (1:PQ_size)
    cycle = vcat(branch(P[i]), reverse(branch(Q[i])[1:end-2]))
    k = 1
    while k <= length(cycle) - 1
      cycle[k] -= ram_pts_nr
      cycle[k+1] = ramification_points[cycle[k+1]][1]
      k +=2
    end
    
    cycle[k] -= ram_pts_nr
    push!(cycles_list, cycle)
  end
  
  
  A = zero_matrix(Int, PQ_size, PQ_size)
  for i in (1:PQ_size)
    j = mod(get_position(P[i]), terminated_edges_nr) + 1
    while true
      next_edge = terminated_edges[j]
      if PQ(next_edge)
        A[get_label(next_edge), i] +=1
      else
        if get_label(next_edge) == i
          break
        else
          A[get_label(next_edge), i] -=1
        end
      end
      j = mod(j, terminated_edges_nr) + 1
    end
  end
  
  @req rank(A) == 2*genus "Computed matrix has the wrong rank. There is a bug in the code."
  K = matrix(ZZ, A)
  
  RS.homology_basis = cycles_list, K, symplectic_reduction(K)
  return RS.homology_basis
end

function symplectic_reduction(K::ZZMatrix)

  @req is_zero(K + transpose(K)) "Matrix needs to be skew-symmetric" 
  @req nrows(K) == ncols(K) "Matrix needs to be square"

  n = nrows(K)
  
  function find_one_above_pivot(K::ZZMatrix, pivot::Int)
    for i in (pivot:n)
      for j in (pivot:n)
        if K[i, j] == 1
          return [i, j]
        end
      end
    end
    return [0, 0]
  end
  
  A = deepcopy(K)
  B = one(parent(K))
  
  ind1 = []
  ind2 = []
  pivot = 1
  
  while pivot <= n
    next = find_one_above_pivot(A, pivot)
    if next == [0,0]
      push!(ind2, pivot)
      pivot +=1
      continue
    end
    Hecke.move_to_positive_pivot(next[2], next[1], pivot, A, B)
    zeros_only = true
    pivot_plus = pivot + 1
    for j in (pivot + 2:n)
      v = -A[pivot, j]
      if v != 0
        #The version with ! gave different results for some reason.
        #add_row!(A, v, pivot_plus, j)
        #add_column!(A, v, pivot_plus, j)
        #add_row!(B, v, pivot_plus, j)
        A = add_row(A, v, pivot_plus, j)
        A = add_column(A, v, pivot_plus, j)
        B = add_row(B, v, pivot_plus, j)
        zeros_only = false
      end
      v = A[pivot_plus, j]
      if v != 0
        A = add_row(A, v, pivot, j)
        A = add_column(A, v, pivot, j)
        B = add_row(B, v, pivot, j)
        #add_row!(A, v, pivot, j)
        #add_column!(A, v, pivot, j)
        #add_row!(B, v, pivot, j)
        zeros_only = false
      end
    end
    if zeros_only
      push!(ind1, [A[pivot_plus, pivot], pivot])
      pivot += 2
    end
  end
  sort!(ind1)
  reverse!(ind1)
  new_rows_ind = vcat([i[2] for i in ind1], [i[2] + 1 for i in ind1], ind2)
  return matrix(ZZ, vcat([B[Int(i), 1:n] for i in new_rows_ind]))
end

function move_to_positive_pivot(i::Int, j::Int, pivot::Int, A::ZZMatrix, B::ZZMatrix)
  pivot_plus = pivot + 1
  v = A[i, j] 
  is_pivot = false
  if [i,j] == [pivot_plus, pivot] && A[pivot_plus, pivot] != v
    is_pivot = true
    swap_rows!(B, pivot, pivot_plus)
    swap_rows!(A, pivot, pivot_plus)
    swap_cols!(A, pivot, pivot_plus)
  elseif [i,j] == [pivot, pivot_plus]
    swap_rows!(B, pivot, pivot_plus)
    swap_rows!(A, pivot, pivot_plus)
    swap_cols!(A, pivot, pivot_plus)
  elseif j != pivot && j != (pivot_plus) && i != pivot && i != (pivot_plus)
    swap_rows!(B, pivot, j)
    swap_rows!(B, pivot_plus, i)
    swap_rows!(A, pivot, j)
    swap_rows!(A, pivot_plus, i)
    swap_cols!(A, pivot, j)
    swap_cols!(A, pivot_plus, i)
  elseif j == pivot 
    swap_rows!(B, pivot_plus, i)
    swap_rows!(A, pivot_plus, i)
    swap_cols!(A, pivot_plus, i)
  elseif j == pivot_plus
    swap_rows!(B, pivot, i)
    swap_rows!(A, pivot, i)
    swap_cols!(A, pivot, i)
  elseif i == pivot 
    swap_rows!(B, pivot_plus, j)
    swap_rows!(A, pivot_plus, j)
    swap_cols!(A, pivot_plus, j)
  elseif i == pivot_plus
    swap_rows!(B, pivot, j)
    swap_rows!(A, pivot, j)
    swap_cols!(A, pivot, j)
  end
  if A[pivot_plus, pivot] != v && !is_pivot
    swap_rows!(B, pivot, pivot_plus)
    swap_rows!(A, pivot, pivot_plus)
    swap_cols!(A, pivot, pivot_plus)
  end
end


