################################################################################
#
#          RieSrf/RiemannSurface.jl : Riemann surfaces
#
# (C) 2022 Jeroen Hanselman
#
################################################################################

export RieSrf, CPath, TretkoffEdge

export RiemannSurface, discriminant_points, embedding, genus, precision, fundamental_group_of_punctured_P1, monodromy_representation, monodromy_group, homology_basis

export c_line, max_radius, radius_factor, find_paths_to_end, start_point, end_point, c_arc, sheet_ordering, embed_mpoly, path_type, analytic_continuation, reverse, assign_permutation, permutation, minimal_spanning_tree, is_terminated, branch, set_position, terminate, edge_level, get_position, set_label, get_label, PQ, homology_basis

################################################################################
#
#  Types
#
################################################################################

mutable struct CPath

  path_type::Int
  start_point::acb
  end_point::acb
  C::AcbField
  
  center::acb
  radius::arb
  
  length::arb
  gamma::Any
  orientation::Int
  permutation::Perm{Int}
  
  int_params::arb
  t_of_closed_D_point::acb
  bounds::Array{Int}
  
  #Path type index:
  #0 is a line
  #1 is an arc
  #2 is a circle
  
  function CPath(a::acb, b::acb, path_type::Int, c::acb = zero(parent(a)), radius::arb = real(zero(parent(a))), orientation::Int = 1)
  
    P = new()
    P.C = parent(a)
    P.start_point = a
    P.end_point = b
    P.path_type = path_type
    P.center = c
    P.radius = radius
    P.orientation = orientation
    P.bounds = []
    
    #Line
    if path_type == 0
      gamma = function(t::arb)
        return (a + b)//2 + (b - a)//2 * t
      end
      length = abs(b - a)
    end
    
    Cc = P.C
    
    i = onei(Cc)
    piC = real(const_pi(Cc))
    
    #Round real or imag part to zero to compute angle if necessary
    prec = precision(Cc)
    zero_sens = floor(prec*log(2)/log(10)) - 5
    
    a_diff = a - c
    
    if abs(real(a_diff)) < 10^(-zero_sens)
      a_diff = Cc(imag(a_diff))*i
    end
    
    if abs(imag(a_diff)) < 10^(-zero_sens)
      a_diff = Cc(real(a_diff))
    end
    
    b_diff = b - c
    
    if abs(real(b_diff)) < 10^(-zero_sens)
      b_diff = Cc(imag(b_diff))*i
    end
    
    if abs(imag(b_diff)) < 10^(-zero_sens)
      b_diff = Cc(real(b_diff))
    end
    
    phi_a = mod2pi(angle(a_diff))
    phi_b = mod2pi(angle(b_diff))
    
    if orientation == 1
      if phi_b < phi_a
        phi_b += 2*piC
      end
    elseif orientation == - 1
       if phi_a < phi_b
        phi_a += 2*piC
      end
    end
    
    
    
    #Arc
    if path_type == 1
      gamma = function(t::arb)
        return c + radius * exp(i * ((phi_a + phi_b)//2 + (phi_b - phi_a)//2 * orientation * t))
      end
      
      length = abs((phi_b - phi_a)) * radius
      
    end
    
    #Full circle
    if path_type == 2
      gamma = function(t::arb)
        #Minus radius as gamma(-1) = a
        return c - radius * exp(i * (phi_a + piC * t ))
      end
      length = 2 * piC * radius
    end
    
    P.gamma = gamma
    P.length = length
    return P
  end

end

mutable struct RiemannSurface
  defining_polynomial::MPolyElem
  genus::Int
  tau::acb_mat
  prec::Int
  embedding::Union{PosInf, InfPlc}
  discriminant_points::Vector{acb}
  closed_chains::Vector{CPath}
  function_field::AbstractAlgebra.Generic.FunctionField
  basis_of_differentials::Vector{Any}

#=
  function RiemannSurface(tau::acb_mat)
    RS = new()
    g = ncols(tau)
    if nrows(tau) != g
      error("Matrix needs to be a square matrix")
    end
    RS.genus = g
    prec = precision(parent(M[1,1]))
    RS.small_period_matrix = tau
  end
=#
  function RiemannSurface(f::MPolyElem, v::T, prec = 100) where T<:Union{PosInf, InfPlc}
    K = base_ring(f)
    
    RS = new()
    RS.defining_polynomial = f
    RS.prec = prec
    RS.embedding = v
    
    k = base_ring(f)
    kx, x = RationalFunctionField(k, "x")
    kxy, y = PolynomialRing(kx, "y")
    f_new = f(x,y)
    F, a = function_field(f_new)
    diff_bas = basis_of_differentials(F)
    RS.function_field = F
    RS.basis_of_differentials = diff_bas
    RS.genus = dimension(diff_bas)
    
    return RS
  end
end

mutable struct TretkoffEdge
  start_point::Int
  end_point::Int
  level::Int
  terminated::Bool
  branch::Vector{Int}
  position::Int
  label::Int
  
  function TretkoffEdge(a::Int, b::Int, L::Int = 0,  B::Vector{Int} = [a, b], term::Bool = false)
    TE = new()
    TE.start_point = a
    TE.end_point = b
    TE.level = L
    TE.terminated = term
    TE.branch = B
  
    return TE
  end
end

function start_point(e::TretkoffEdge)
  return e.start_point
end

function end_point(e::TretkoffEdge)
  return e.end_point
end

function isequal(e1::TretkoffEdge, e2::TretkoffEdge)
  return start_point(e1) == start_point(e2) && end_point(e1) == end_point(e2)
end

function edge_level(e::TretkoffEdge)
  return e.level
end

function terminate(e::TretkoffEdge)
  e.terminated = true
end

function is_terminated(e::TretkoffEdge)
  return e.terminated
end

function branch(e::TretkoffEdge)
  return e.branch
end

function set_position(e::TretkoffEdge, s::Int)
  e.position = s
end

function get_position(e::TretkoffEdge)
  return e.position
end

function PQ(e::TretkoffEdge)
  return start_point(e) < end_point(e)
end

function reverse(e::TretkoffEdge)
  return TretkoffEdge(end_point(e), start_point(e))
end

function set_label(e::TretkoffEdge,l::Int)
  e.label = l
end

function get_label(e::TretkoffEdge)
  return e.label
end

function reverse(G::CPath)
  
  p_type = path_type(G)
  
  if p_type == 0
    G_rev = c_line(end_point(G), start_point(G))
  else #Circle or arc
    G_rev = c_arc(end_point(G), start_point(G), center(G), orientation = -orientation(G))
  end
  assign_permutation(G_rev, inv(permutation(G)))
  return G_rev
end

function c_line(start_point::acb, end_point::acb)
  return CPath(start_point, end_point, 0)
end

function c_arc(start_point::acb, end_point::acb, center::acb; orientation::Int = 1)
  if contains(end_point, start_point) && contains(start_point, end_point)
    return CPath(start_point, start_point, 2, center, abs(start_point - center), orientation)
  else
    return CPath(start_point, end_point, 1, center, abs(start_point - center), orientation)
  end
end

function show(io::IO, gamma::CPath)
  p_type = path_type(gamma)
  if p_type< 0 || p_type > 2
    error("Path type does not exist")
  end
  
  x0 = start_point(gamma)
  x1 = end_point(gamma)
  if p_type == 0
    print(io, "Line from $(x0) to $(x1).")
  else
    r = radius(gamma)
    c = center(gamma)
    if p_type == 1
      print(io, "Arc around $(c) with radius $(r) starting at $(x0) and ending at $(x1).")
    elseif p_type == 2
      print(io, "Circle around $(c) with radius $(r) starting at $(x0).")
    end
  end
  end

function path_type(G::CPath)
  return G.path_type
end

function start_point(G::CPath)
  return G.start_point
end

function end_point(G::CPath)
  return G.end_point
end

function center(G::CPath)
  if 1 <= path_type(G) <= 2
    return G.center
  else
    error("Path is not a circe or an arc")
  end
end

function radius(G::CPath)
  if 1 <= path_type(G) <= 2
    return G.radius
  else
    error("Path is not a circe or an arc")
  end
end

function evaluate(G::CPath, t::arb)
  return G.gamma(t)
end

function length(G::CPath)
  return G.length
end

function orientation(G::CPath)
  return G.orientation
end

function assign_permutation(G::CPath, permutation::Perm{Int})
  G.permutation = permutation
end

function permutation(G::CPath)
  return G.permutation
end

function set_t_of_closest_d_point(G::CPath, t::acb)
  G.t_of_closest_d_point = t
end

function get_t_of_closest_d_point(G::CPath, t::acb)
  G.t_of_closest_d_point = t
end

function defining_polynomial(RS::RiemannSurface)
  return RS.defining_polynomial
end


function defining_polynomial_univariate(RS::RiemannSurface)
  f = defining_polynomial(RS)
  K = base_ring(f)
  Kx, x = PolynomialRing(K, "x")
  Kxy, y = PolynomialRing(Kx, "y")
  
  return f(x, y)
end

function genus(RS::RiemannSurface)
  return RS.genus
end

function embedding(RS::RiemannSurface)
  return RS.embedding
end

function small_period_matrix(RS::RiemannSurface)
  return tau
end

function precision(RS::RiemannSurface)
  return RS.prec
end

function max_radius(RS::RiemannSurface)
  return ArbField(precision(RS))(1//4)
end

function radius_factor(RS::RiemannSurface)
  return ArbField(precision(RS))(2//5)
end

function function_field(RS::RiemannSurface)
  return RS.function_field
end

function monodromy_representation(RS::RiemannSurface)
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
  
  mon_rep = []
  
  for gamma in pi1_gens
    chain = map(t -> ((t > 0) ? paths[t] : reverse(paths[-t])), gamma)
    gamma_perm = prod(map(permutation, chain))
    
    if gamma_perm != one(s_m)
      push!(mon_rep, (chain, gamma_perm))
     end
  end
  
  inf_chain = []
  inf_perm = one(s_m)
  
  for g in mon_rep
    inf_chain = vcat(inf_chain, map(reverse, g[1]))
    inf_perm *= g[2]
  end
  
  push!(mon_rep, (reverse(inf_chain), inv(inf_perm)))
  
  return mon_rep
  
end

function monodromy_group(RS::RiemannSurface)
  mon_rep = monodromy_representation(RS)
  gens = map(t -> t[2], mon_rep)
  return closure(gens, *)
end

function homology_basis(RS::RiemannSurface)
  mon_rep = monodromy_representation(RS)
  gens = map(t -> t[2], mon_rep)
  s_n = parent(gens[1])
  n = s_n.n
  d = length(gens)
  
  ramification_points = []
  ramification_indices = []
  
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
  edges_on_level = []
  terminated_edges = []
  
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
  
  P = []
  QQ = []
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
  
  cycles_list = []
  
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
  return cycles_list, K, symplectic_reduction(K)
end

function symplectic_reduction(K::MatrixElem{fmpz})

  @req is_zero(K + transpose(K)) "Matrix needs to be skew-symmetric" 
  @req nrows(K) == ncols(K) "Matrix needs to be square"

  n = nrows(K)
  
  function find_one_above_pivot(K::MatrixElem{fmpz}, pivot::Int)
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
    move_to_positive_pivot(next[2], next[1], pivot, A, B)
    zeros_only = true
    pivot_plus = pivot + 1
    for j in (pivot + 2:n)
      v = -A[pivot, j]
      if v != 0
        add_row!(A, v, pivot_plus, j)
        add_column!(A, v, pivot_plus, j)
        add_row!(B, v, pivot_plus, j)
        zeros_only = false
      end
      v = A[pivot_plus, j]
      if v != 0
        add_row!(A, v, pivot, j)
        add_column!(A, v, pivot, j)
        add_row!(B, v, pivot, j)
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
  return vcat([B[Int(i), 1:n] for i in new_rows_ind])
end

function move_to_positive_pivot(i::Int, j::Int, pivot::Int, A::MatrixElem{fmpz}, B::MatrixElem{fmpz})
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
#Follows algorithm 4.3.1 in Neurohr
function fundamental_group_of_punctured_P1(RS::RiemannSurface, abel_jacobi::Bool = true)
  
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
    x0 = Cc(min(floor(fmpz, real(D_points[1]) - 2*max_radius(RS)), -1))
    
    
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

  path_edges = []
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
    next_level = []
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
  paths_with_arcs = []
  
  #We reconstruct the paths 
  for path in reverse(path_indices)
    
    i = path[end]
    loop = []
    
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

    path_to_loop = []

    #Now we attach the line piece
    push!(path_to_loop, i)
   
    #We add the inverse arcs as moving towards the points we want to encircle we move clockwise 
    for k in (length(path)-1:-1:1)  
    
      arc_buffer = []
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
  return vcat(c_lines, c_arcs), reverse(paths_with_arcs)
end

function analytic_continuation(RS::RiemannSurface, path::CPath, abscissae::Vector{arb})
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
  y_vals = [zeros(Cc, m) for i in (1:N)]
  z = zeros(Cc, m)
  x_vals[1] = evaluate(path, u[1])
  
  Kxy = parent(f)
  Ky, y = PolynomialRing(base_ring(Kxy), "y")
  
  
  y_vals[1] = sort!(roots(f(x_vals[1], y), initial_prec = prec), lt = sheet_ordering)
  for l in (2:N)
    x_vals[l] = evaluate(path, u[l])
    z .= y_vals[l-1]
    y_vals[l] .= recursive_continuation(f, x_vals[l-1], x_vals[l], z)
  end
  return collect(zip(x_vals, y_vals))
end

function recursive_continuation(f, x1, x2, z)
  Kxy = parent(f)
  Ky, y = PolynomialRing(base_ring(Kxy), "y")
  Cc = base_ring(f)
  prec = precision(Cc)
  m = degree(f, 2)
  temp_vec = acb_vec(m)
  temp_vec_res = acb_vec(m)
  d = reduce(min, [abs(z[i] - z[j]) for (i, j) in filter(t-> t[1] != t[2], [a for a in Iterators.product((1:m), (1:m))])]) 
  W = [ f(x2, z[i]) // prod([z[i] - z[j] for j in vcat((1:i - 1), i+1:m)];init = one(Cc)) for i in (1:m)]
  w = reduce(max, map(t -> real(t)^2 +imag(t)^2, W))
  
  if w < d // (2*m)
    fill!(temp_vec, z)
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

function Base.mod2pi(x::arb)
  pi2 = 2*const_pi(parent(x))
  while x < 0
    x += pi2
  end
  
  while x > pi2
    x -= pi2
  end
  
  return x
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

function embed_poly(f::PolyElem{nf_elem}, v::T, prec::Int = 100) where T<:Union{PosInf, InfPlc}
  coeffs = coefficients(f)
  coeffs = map(t -> evaluate(t, v, prec), coeffs)
  
  Cx, x = PolynomialRing(AcbField(prec), "x")
  
  return sum(coeffs[i]*x^(i - 1) for i in (1:length(coeffs)))
end

function embed_mpoly(f::MPolyElem, v::T, prec::Int = 100) where T<:Union{PosInf, InfPlc}
  return map_coefficients(x -> evaluate(x, v, prec), f)
end

#Might need to be made more rigorous due to dealing with arb balls
function sheet_ordering(z1::acb,z2::acb)
  if real(z1) < real(z2) 
    return true
  elseif real(z1) > real(z2) 
    return false
  elseif imag(z1) < imag(z2)
    return true
  elseif imag(z2) < imag(z1)
    return false
  end
end

