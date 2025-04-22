function principal_generator_eichler(I::AlgAssRelOrdIdl)
  O = left_order(I)
  @assert is_maximal(O)
  A = algebra(O)
  @assert is_eichler(A)

  orders = representatives_of_maximal_orders(O)
  d = discriminant(O)

  # Compute r such that r orders[i] \subseteq orders[j] for all i, j
  r = ZZRingElem(1)
  for i = 1:length(orders)
    for j = 1:length(orders)
      if i == j
        continue
      end

      # Consider orders[i] as an ideal.
      # The basis pseudo-matrix is probably not in HNF, but we don't need this.
      OO = ideal(A, basis_pmatrix(orders[i], copy = false); M_in_hnf=true)
      r = lcm(r, denominator(OO, orders[j]))
    end
  end
  rd = r*d

  y = integral_coprime_representative(O, I, rd)
  J = I*y

  _N = normred(J, O)
  @assert denominator(_N, copy = false) == 1 # J should be integral
  N = numerator(_N, copy = false)
  OK = order(N)
  R, mR = ray_class_group(OK(1)*OK, ramified_infinite_places(A))
  @assert iszero(mR\N) "Ideal is not principal"

  primes = collect(keys(factor(N)))
  valuations = Int[ valuation(N, p) for p in primes ]
  _w = _norm_equation_valuations_only(O, primes, valuations)
  w = evaluate(_w)

  Ow = O*O(w)
  ww = _eichler_find_transforming_unit(J, Ow)
  return w*ww*inv(y)
end

# Requires nr(M) == nr(N) and that nr(N) is coprime to r*d where d is the
# discriminant of O and r in base_ring(O) such that r O_i \subseteq O_j for a
# system of representatives of the maximal orders.
# Returns t in O^\times such that M = Nt
function _eichler_find_transforming_unit_maximal(M::T, N::T) where { T <: Union{ AlgAssAbsOrdIdl, AlgAssRelOrdIdl } }
  A = algebra(M)
  O = left_order(M)
  @assert is_maximal(O)
  # We assume that left_order(N) == O, but testing this would be really expensive

  if M == N
    return one(O)
  end

  F = FieldOracle(A, [ O ])
  p = normred(M, O)
  @assert p == normred(N, O)
  @assert denominator(p) == 1
  p = numerator(p)
  OpO, toOpO = quo(O, p*O, p)
  B, toB = _as_matrix_algebra(OpO)

  I = _ideal_from_kgens(B, [ toB(toOpO(O(b))) for b in absolute_basis(M) ])
  J = _ideal_from_kgens(B, [ toB(toOpO(O(b))) for b in absolute_basis(N) ])

  # Compute the image of 1 under the canonical projections O -> O/M respectively O -> O/N
  Fq = base_ring(B)
  vv = mod(one(B), I)
  nonZeroCol = 0
  for i = 1:_matdeg(B)
    for j = 1:_matdeg(B)
      if !iszero(vv[i, j])
        nonZeroCol = j
        break
      end
    end
    if !iszero(nonZeroCol)
      break
    end
  end
  v = matrix(Fq, _matdeg(B), 1, elem_type(Fq)[ vv[i, nonZeroCol] for i = 1:_matdeg(B) ])
  ww = mod(one(B), J)
  nonZeroCol = 0
  for i = 1:_matdeg(B)
    for j = 1:_matdeg(B)
      if !iszero(ww[i, j])
        nonZeroCol = j
        break
      end
    end
    if !iszero(nonZeroCol)
      break
    end
  end
  w = matrix(Fq, _matdeg(B), 1, elem_type(Fq)[ ww[i, nonZeroCol] for i = 1:_matdeg(B) ])

  b = ceil(Int, degree(base_ring(B))*dim(B)*log2(BigInt(characteristic(base_ring(B)))))
  # A minimal set of generators of around b elements should generate B^\times
  units = _find_some_units(F, 1, b)
  push!(units, -one(O))
  generators = [ matrix(toB(toOpO(u)), copy = false) for u in units ]
  path_exists, path = find_path(generators, v, w)

  while !path_exists
    # Add 10 more generators
    new_units = _find_some_units(F, 1, 10)
    append!(units, new_units)
    append!(generators, [ matrix(toB(toOpO(u)), copy = false) for u in new_units ])
    path_exists, path = find_path(generators, v, w)
  end

  t = one(O)
  for i = 1:length(path)
    u = units[path[i]]
    t = u*t
  end
  @assert matrix(toB(toOpO(t)))*v == w

  return t
end

# Finds at least n units in the order F.maximal_orders[order_num]
function _find_some_units(F::FieldOracle{S, T, U, M}, order_num::Int, n::Int) where { S <: AbstractAssociativeAlgebra{AbsSimpleNumFieldElem}, T, U, M }
  O = F.maximal_orders[order_num]
  units = Vector{elem_type(O)}()
  while length(units) < n
    LtoA = get_new_field(F, order_num)
    L = domain(LtoA)
    OL = maximal_order(L)
    K, KtoL = simplified_absolute_field(L)
    OK = maximal_order_via_relative(K, KtoL)
    UK, mUK = unit_group(OK)
    for j = 1:ngens(UK)
      u = mUK(UK[j])
      if u == -one(OK)
        continue
      end
      push!(units, O(LtoA(KtoL(elem_in_nf(u, copy = false)))))
    end
  end
  return units
end

function _eichler_find_transforming_unit_recurse(I::S, J::S, primes::Vector{T}) where { S <: Union{ AlgAssAbsOrdIdl, AlgAssRelOrdIdl }, T <: Union{ Int, ZZRingElem, AbsNumFieldOrderIdeal, RelNumFieldOrderIdeal } }
  if length(primes) == 1
    u = _eichler_find_transforming_unit_maximal(I, J)
    return elem_in_algebra(u, copy = false)
  end

  p = pop!(primes)
  IJ = I + J
  if valuation(normred(IJ, left_order(I)), p) != 0
    M = maximal_integral_ideal_containing(IJ, p, :left)
    I = divexact_left(I, M)
    J = divexact_left(J, M)
    return _eichler_find_transforming_unit_recurse(I, J, primes)
  end

  M = maximal_integral_ideal_containing(I, p, :left)
  N = maximal_integral_ideal_containing(J, p, :left)
  u = elem_in_algebra(_eichler_find_transforming_unit_maximal(M, N), copy = false)
  v = inv(u)
  I = divexact_left(I, M)
  OI = left_order(I) # We need it later anyway and it should be the same (as in ===) as the one of J

  J = divexact_left(J, N)
  J = v*J
  J = J*u
  J.left_order = OI

  t = _eichler_find_transforming_unit_recurse(I, J, primes)
  return u*t
end

# Finds x\in A^\times such that I == Jx.
# Requires nr(I) == nr(J) and that nr(I) is coprime to r*d where d is the
# discriminant of O and r in base_ring(O) such that r O_i \subseteq O_j for a
# system of representatives of the maximal orders.
function _eichler_find_transforming_unit(I::AlgAssRelOrdIdl, J::AlgAssRelOrdIdl)
  O = left_order(I)
  @assert is_maximal(O)
  # We assume that left_order(J) == O, but testing this would be really expensive

  n = normred(I, O)
  @assert n == normred(J, O)
  @assert denominator(n, copy = false) == 1
  n = numerator(n, copy = false)

  fac_n = factor(n)
  if isempty(fac_n)
    return one(algebra(order(O)))
  end

  primes = Vector{ideal_type(base_ring(O))}()
  for (p, e) in fac_n
    for i = 1:e
      push!(primes, p)
    end
  end
  t = _eichler_find_transforming_unit_recurse(I, J, primes)
  return t
end

function get_coeff_fmpz!(x::fqPolyRepFieldElem, n::Int, z::ZZRingElem)
  c = ccall((:nmod_poly_get_coeff_ui, libflint), UInt, (Ref{fqPolyRepFieldElem}, Int), x, n)
  set!(z, c)
  return z
end

function get_coeff_fmpz!(x::FqPolyRepFieldElem, n::Int, z::ZZRingElem)
  ccall((:fmpz_poly_get_coeff_fmpz, libflint), Nothing, (Ref{ZZRingElem}, Ref{FqPolyRepFieldElem}, Int), z, x, n)
  return z
end

# Let v and w be non-zero k \times 1-matrices over a finite field and let
# generators be a vector of invertible k \times k-matrices over this field.
# This functions finds a matrix g in the group generated by the elements in
# generators such that gv == w, if such a matrix exists.
# Returns false, rubbish if no such element exists or true and a vector I of
# indices such that g = prod([ generators[i] for i in reverse(I) ]) is the
# searched element.
# This really SLOW! (But it is a hard problem, I guess.)
function find_path(generators::Vector{T}, v::T, w::T) where { T <: MatElem }

  function _weight(v::MatElem{T}, n::ZZRingElem, t::ZZRingElem, jmax::Int) where { T <: Union{ FqPolyRepFieldElem, fqPolyRepFieldElem } }
    n = zero!(n)
    for i = 1:nrows(v)
      for j = 0:jmax
        n = add!(n, n, get_coeff_fmpz!(v[i, 1], j, t))
      end
    end
    return n
  end

  function _weight(v::MatElem{T}, n::ZZRingElem, t::ZZRingElem, jmax::Int) where { T <: Union{ fpFieldElem, EuclideanRingResidueFieldElem{ZZRingElem} } }
    n = zero!(n)
    for i = 1:nrows(v)
      n = add!(n, n, lift!(v[i, 1], t))
    end
    return n
  end

  # The main philosophy is to consider the graph G whose vertices are the elements
  # of F_q^k (k := nrows(v)) and in which there is an edge between two vertices
  # v_1 and v_2 if there exists an element g in generators such that g v_1 = v_2.
  # We then do a graph traversal starting in v and stop as soon as we reach w
  # (or we visited all vertices and w is not in the graph).

  # Initialize the edges (we also add the products of generators)
  edges = Vector{T}()
  edges_in_generators = Vector{Vector{Int}}()
  set_of_edges = Set{T}()
  for i = 1:length(generators)
    e = generators[i]
    if e in set_of_edges
      continue
    end
    push!(edges, e)
    push!(set_of_edges, e)
    push!(edges_in_generators, [ i ])
  end
  for i = 1:length(generators)
    for j = 1:length(generators)
      e = generators[i]*generators[j]
      if e in set_of_edges
        continue
      end
      push!(edges, e)
      push!(set_of_edges, e)
      push!(edges_in_generators, [ j, i ]) # One has to reverse the order
    end
  end
  inv_edges = Dict{Int, T}()
  last_added_edge = Int[ 1, 0 ]

  # We first do a depth first search, where we only visit a vertex if it has
  # smaller weight (with respect to the above weight function).

  # Initialize weight function stuff
  Fq = base_ring(parent(v))
  p = characteristic(Fq)
  ngv = ZZRingElem()
  t = ZZRingElem()
  jmax = degree(Fq) - 1
  minusW = -w
  temp = deepcopy(v)

  res = Vector{Int}()
  visited = Dict{T, Int}()
  no_return = false
  visited[v] = 0
  temp = add!(temp, v, minusW)
  nv = deepcopy(_weight(temp, ngv, t, jmax))
  gv = deepcopy(v)

  # Start the depth first search
  while !iszero(nv)
    j = visited[v] + 1

    # Find the next vertex
    ngv = deepcopy(nv)
    while j <= length(edges)
      gv = mul!(gv, edges[j], v)
      if haskey(visited, gv)
        j += 1
        continue
      end

      # We have not been to gv before, check whether it has smaller weight
      temp = add!(temp, gv, minusW)
      ngv = _weight(temp, ngv, t, jmax)
      if ngv < nv
        break
      end
      j += 1
    end
    visited[v] = j

    if ngv < nv
      v = deepcopy(gv)
      visited[v] = 0
      nv = deepcopy(ngv)
      push!(res, j)
      # Go to gv!
      continue
    end

    # The search ended without a new vertex: we have to go back
    if isempty(res)
      # We are back at the start: add some edges
      if last_added_edge[2] == length(generators)
        if last_added_edge[1] == length(generators)
          # We already added all pairs and 3-tuples of generators, so we give up
          # and do breadth first search now.
          no_return = true
          break
        end
        last_added_edge[1] += 1
      else
        last_added_edge[2] += 1
      end
      e1 = generators[last_added_edge[1]]
      e2 = generators[last_added_edge[2]]
      e12 = e1*e2
      for i = 1:length(generators)
        e = e12*generators[i]
        if e in set_of_edges
          continue
        end
        push!(edges, e)
        push!(set_of_edges, e)
        push!(edges_in_generators, [ i, last_added_edge[2], last_added_edge[1] ])
      end
    else
      # We go one step back
      i = pop!(res)
      if !haskey(inv_edges, i)
        inv_edges[i] = inv(edges[i])
      end
      v = inv_edges[i]*v
      temp = add!(temp, v, minusW)
      nv = deepcopy(_weight(temp, ngv, t, jmax))
    end
  end

  if !no_return
    # We finished with a solution!
    res_in_generators = Vector{Int}()
    for i in res
      append!(res_in_generators, edges_in_generators[i])
    end

    return true, res_in_generators
  end

  # We could not find a path until now, so we do breadth first search (without
  # any weight function)
  Q = Vector{Tuple{T, Vector{Int}}}()
  # I would like to use a queue here, but they are in DataStructures.jl.
  #Q = Queue{Tuple{T, Vector{Int}}}()
  visited = Set{T}()
  push!(Q, (v, Int[]))
  #enqueue!(Q, (v, Int[]))
  push!(visited, v)
  while !isempty(Q)
    u, path_to_u = popfirst!(Q)
    #u, path_to_u = dequeue!(Q)
    for i = 1:length(edges)
      temp = mul!(temp, edges[i], u)
      if temp in visited
        continue
      end
      if temp == w
        path_in_generators = Vector{Int}()
        for j in path_to_u
          append!(path_in_generators, edges_in_generators[j])
        end
        append!(path_in_generators, edges_in_generators[i])
        return true, path_in_generators
      end
      gu = deepcopy(temp)
      push!(visited, gu)
      push!(Q, (gu, push!(copy(path_to_u), i)))
      #enqueue!(Q, (gu, push!(copy(path_to_u), i)))
    end
  end
  # There does not exist a path
  return false, Vector{Int}()
end
