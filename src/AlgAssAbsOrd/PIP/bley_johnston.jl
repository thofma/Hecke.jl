################################################################################
#
#  Bley--Johnston--Hofmann enumeration method
#
################################################################################

# Compute a set S, such that pi(S) = im(pi), where pi : M^* -> (M/F)^*.
function _unit_reps(M, F; GRH::Bool = true)
  D = get_attribute!(M, :unit_reps) do
    return Dict{typeof(F), Vector{Vector{elem_type(algebra(M))}}}()
  end::Dict{typeof(F), Vector{Vector{elem_type(algebra(M))}}}

  if haskey(D, F)
    @vprintln :PIP "Unit representatives cached for this conductor ideal"
    return D[F]
  else
    u = __unit_reps(M, F; GRH = GRH)
    D[F] = u
    return u
  end
end

function __unit_reps_simple(M, F; GRH::Bool = true)
  B = algebra(M)
  @vprintln :PIP _describe(B)
  @vprintln :PIP "Computing generators of the maximal order"
  if dim(B) == 0
    return [zero(B)]
  end
  UB = _unit_group_generators_maximal_simple(M; GRH = GRH)
  Q, MtoQ = quo(M, F)
  for u in UB
    @assert u in M && inv(u) in M
    #@show u in FinB
  end
  @vprintln :PIP "Number of generators: $(length(UB))"
  UB_reduced = [MtoQ(M(u)) for u in UB]
  #@show UB_reduced
  #@show norm(F)
  #QQ, MtoQQ = _quo_as_mat_alg_small(M, F)
  QQ = FakeAbsOrdQuoRing(M, F)
  _UB_reduced = [QQ(M(u)) for u in UB]

  #@show length(UB)
  #@show UB_reduced
  @vprintln :PIP "computing closure"
  @vprintln :PIP "dimension $(dim(B))"

  if isdefined(B, :isomorphic_full_matrix_algebra)
    # It is faster to compute products in M_n(F) than in an associative algebra
    local C::MatAlgebra{AbsSimpleNumFieldElem, Generic.MatSpaceElem{AbsSimpleNumFieldElem}}
    local BtoC::Hecke.AbsAlgAssMorGen{StructureConstantAlgebra{QQFieldElem}, MatAlgebra{AbsSimpleNumFieldElem, AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}}, AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}, QQMatrix}
    #local BtoC::morphism_type(typeof(B), MatAlgebra{AbsSimpleNumFieldElem, Generic.MatSpaceElem{AbsSimpleNumFieldElem}})
    C, BtoC = B.isomorphic_full_matrix_algebra
    UBinC = elem_type(C)[BtoC(u)::elem_type(C) for u in UB]
    ___units = collect(zip(UBinC, UB_reduced))
    ___units_ = collect(zip(UBinC, _UB_reduced))
    ___units_all = collect(zip(UBinC, UB_reduced, _UB_reduced))
    #@time cl = closure(___units, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])
    cl = closure(___units_, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])
    # @show length(cl), length(cl2)
    # @assert length(cl) == length(cl2)
    # @time cl = closure(___units_all, (x, y) ->
    #                    begin
    #                   #   if !(MtoQ\(x[2] * y[2]) - lift(x[3] * y[3]) in F)
    #                   #     push!(_debug, ((M(BtoC\x[1]), x[2], x[3]), (M(BtoC\y[1]), y[2], y[3])))
    #                   #     @show "oops";
    #                   #     @show coordinates(MtoQ\x[2])
    #                   #     @show coordinates(MtoQ\y[2]);
    #                   #     @show lift(x[3]) - M(BtoC\(x[1])) in F
    #                   #     @show lift(y[3]) - M(BtoC\(y[1])) in F
    #                   #     @show MtoQ\x[2] - M(BtoC\(x[1])) in F
    #                   #     @show MtoQ\y[2] - M(BtoC\(y[1])) in F
    #                   #     @show (x[3] * y[3]).v
    #                   #     @show QQ(lift(x[3]) * lift(y[3])).v
    #                   #     @show (QQ(M(BtoC\(x[1] * y[1])))).v
    #                   #    error("asdsdsd")
    #                   #  end;
    #                   #  w = x[3] * y[3];
    #                   #@assert QQ(lift(w)) == w;
    #                 (x[1] * y[1], x[2] * y[2], x[3] * y[3]);
    #               end,
    #                 eq = (x, y) -> begin
    #                # @assert MtoQ\x[2] - lift(x[3]) in F "oooops"; @assert MtoQ\y[2] - lift(y[3]) in F "oooops2"; if (x[2] == y[2]) != (x[3] == y[3]); @show coordinates(MtoQ\y[2]), coordinates(MtoQ\x[2]); @show coordinates(lift(x[3])); @show coordinates(lift(y[3])); @show x[3]; @show y[3]; error("asss"); end;
    #                x[2] == y[2];
    #                end
    #               )
    # #@time cl2 = closure(___units_, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])
    @vprintln :PIP "Number of units: $(length(cl))"
    #@show length(cl2)
    #@assert first.(cl) == first.(cl2)
    #push!(_debug, cl)
    to_return = Vector{elem_type(B)}(undef, length(cl))
    @vprintln :PIP "Mapping back"
    Threads.@threads :static for i in 1:length(cl)
      to_return[i] = BtoC\(cl[i][1])
    end
    #@time to_return2 = elem_type(B)[ (BtoC\(c[1]))::elem_type(B) for c in cl ]
    #@assert to_return == to_return2
    return to_return
  else
    __units = collect(zip(UB, UB_reduced))
    @vprintln :PIP "Closing in the other case"
    cl = closure(__units, (x, y) -> (x[1] * y[1], x[2] * y[2]), eq = (x, y) -> x[2] == y[2])
    return first.(cl)
  end
end

function __unit_reps_estimates(M, F)
  A = algebra(M)
  dec = decompose(algebra(M))
  unit_reps = Vector{elem_type(algebra(M))}[]
  for (B, mB) in dec
    @info _describe(B)
    MinB = Order(B, elem_type(B)[(mB\(mB(one(B)) * elem_in_algebra(b))) for b in absolute_basis(M)])
    FinB = ideal_from_lattice_gens(B, elem_type(B)[(mB\(b)) for b in absolute_basis(F)])
    @assert Hecke._test_ideal_sidedness(FinB, MinB, :right)
    FinB.order = MinB
    C, mC = center(B)
    FinC = Hecke._as_ideal_of_smaller_algebra(mC, FinB)
    CK, CtoCK = Hecke._as_field_with_isomorphism(C)
    @show CK
    OCK = maximal_order(CK)
    I = sum(CtoCK(x) * OCK for x in absolute_basis(FinC))
    @show basis(I)
    @show norm(I)
    @show factor(I)
    FinC.order = maximal_order(C)
    #_unit_reps =  __unit_reps_simple(MinB, FinB)
    #@vprintln :PIP "Mapping back once more"
    #to_return = Vector{elem_type(A)}(undef, length(_unit_reps))
    #Threads.@threads for i in 1:length(_unit_reps)
    #  to_return[i] = mB(_unit_reps[i])
    #end
    #push!(unit_reps, to_return)
  end
  #return unit_reps
end

function __unit_reps(M, F; GRH::Bool = true)
  #_assert_has_refined_wedderburn_decomposition(algebra(M))
  A = algebra(M)
  dec = decompose(algebra(M))
  unit_reps = Vector{elem_type(algebra(M))}[]
  for (B, mB) in dec
    MinB = Order(B, elem_type(B)[(mB\(mB(one(B)) * elem_in_algebra(b))) for b in absolute_basis(M)])
    FinB = ideal_from_lattice_gens(B, elem_type(B)[(mB\(b)) for b in absolute_basis(F)])
    @assert Hecke._test_ideal_sidedness(FinB, MinB, :right)
    FinB.order = MinB
    _unit_reps =  __unit_reps_simple(MinB, FinB; GRH = GRH)
    @vprintln :PIP "Mapping back once more"
    to_return = Vector{elem_type(A)}(undef, length(_unit_reps))
    Threads.@threads :static for i in 1:length(_unit_reps)
      to_return[i] = mB(_unit_reps[i])
    end
    push!(unit_reps, to_return)
  end
  return unit_reps
end

function _is_principal_with_data_bj(I, O; side = :right, _alpha = nothing, local_freeness::Bool = false, GRH::Bool = true)
  # local_freeness needs to be accepted since the generic interface uses it
  A = algebra(O)
  if _alpha === nothing
    _assert_has_refined_wedderburn_decomposition(A)
  end
  dec = decompose(A)
  local M::typeof(O)

  if _alpha !== nothing
    M = parent(_alpha)
    alpha = elem_in_algebra(_alpha)::elem_type(A)
    fl = true
    @assert alpha * M == I * M
  else
    M = maximal_order(O)
    fl, alpha = _isprincipal_maximal(I * M, M, :right)
  end

  if !fl
    @vprintln :PIP "Not principal over maximal order"
    return false, zero(A)
  end

  # Now test local freeness at the primes dividing the index [M : O]
  for p in prime_divisors(index(O, M))
    if !is_locally_free(O, I, p, side = :right)[1]
      @vprintln :PIP "Not locally free at $p"
      return false, zero(A)
    end
  end

  F = Hecke._get_a_twosided_conductor(O, M)
  # Now make corpime to conductor

  Iorig = I
  if F == 1*O || I + F == one(A) * O
    # I should improve this
    I, sca = I, one(A)
  else
    I, sca = _coprime_integral_ideal_class(I, F)
    #I, sca = _coprime_integral_ideal_class_deterministic(I, F)
  end

  @vprintln :PIP 1 "Found coprime integral ideal class"

  @hassert :PIP 1 sca * Iorig == I

  @hassert :PIP 1 I + F == one(A) * O

  alpha = sca * alpha

  @assert alpha * M == I * M

  bases = Vector{elem_type(A)}[]

  IM = I * M

  for (B, mB) in dec
    MinB = Hecke._get_order_from_gens(B, elem_type(B)[(mB\(mB(one(B)) * elem_in_algebra(b))) for b in absolute_basis(M)])
    #@show is_maximal(MinC)
    #@show hnf(basis_matrix(MinC))
    IMinB = ideal_from_lattice_gens(B, elem_type(B)[(mB\(b)) for b in absolute_basis(IM)])
    IMinB_basis = [mB(u) for u in absolute_basis(IMinB)]
    push!(bases, IMinB_basis)
    #@show UB
    #if isdefined(B, :isomorphic_full_matrix_algebra)
    #  local C::MatAlgebra{AbsSimpleNumFieldElem, Generic.MatSpaceElem{AbsSimpleNumFieldElem}}
    #  C, BtoC = B.isomorphic_full_matrix_algebra
    #  MinC = _get_order_from_gens(C, elem_type(C)[BtoC(elem_in_algebra(b)) for b in absolute_basis(MinB)])
    #  @show MinC
    #  @show nice_order(MinC)
    #end
    #@show FinB
  end

  unit_reps = _unit_reps(M, F; GRH = GRH)

  decc = copy(dec)
  p = sortperm(unit_reps, by = x -> length(x))
  dec_sorted = decc[p]
  units_sorted = unit_reps[p]
  bases_sorted = bases[p]
  bases_offsets_and_lengths = Tuple{Int, Int}[]
  k = 1
  for i in 1:length(bases_sorted)
    push!(bases_offsets_and_lengths, (k, length(bases_sorted[i])))
    k += length(bases_sorted[i])
  end

  # let's collect the Z-basis of the Mi
  bases_sorted_cat = reduce(vcat, bases_sorted)
  special_basis_matrix = basis_matrix(bases_sorted_cat)
  inv_special_basis_matrix = inv(special_basis_matrix)
  Amatrix = QQMatrix(basis_matrix(I)) * inv(special_basis_matrix)
  H, U = hnf_with_transform(change_base_ring(ZZ, Amatrix))
  Hinv = inv(QQMatrix(H))

  local_coeffs = Vector{Vector{QQFieldElem}}[]

  inv_special_basis_matrix_Hinv = inv_special_basis_matrix * Hinv

  #@info "preprocessing units"
  #@time for i in 1:length(dec)
  #  _local_coeffs = Vector{QQFieldElem}[]
  #  m = dec_sorted[i][2]::morphism_type(StructureConstantAlgebra{QQFieldElem}, typeof(A))
  #  alphai = dec_sorted[i][2](dec_sorted[i][2]\(alpha))
  #  for u in units_sorted[i]
  #    aui =  alphai * u
  #    auiasvec = _eltseq(matrix(QQ, 1, dim(A), coefficients(aui)) * inv_special_basis_matrix_Hinv)
  #    push!(_local_coeffs, auiasvec)
  #  end
  #  push!(local_coeffs, _local_coeffs)
  #end
  #@info "done"

  @vprintln :PIP "new preprocessing units"
  local_coeffs = _compute_local_coefficients_parallel(alpha, A, dec_sorted, units_sorted, inv_special_basis_matrix_Hinv)
  @vprintln :PIP "Lengths $(length.(local_coeffs))"
  #@time for i in 1:length(dec)
  #  _local_coeffs = Vector{QQFieldElem}[]
  #  m = dec_sorted[i][2]::morphism_type(StructureConstantAlgebra{QQFieldElem}, typeof(A))
  #  alphai = dec_sorted[i][2](dec_sorted[i][2]\(alpha))
  #  par = Iterators.partition(1:length(units_sorted[i]), multi * dim(A))
  #  ui = units_sorted[i]
  #  for p in par
  #    for (j, j_index) in enumerate(p)
  #      u =  ui[j_index]
  #      aui =  alphai * u
  #      __set_row!(t1, j, coefficients(aui, copy = false))
  #      #auiasvec = _eltseq(matrix(QQ, 1, dim(A), coefficients(aui)) * inv_special_basis_matrix_Hinv)
  #      #push!(_local_coeffs, auiasvec)
  #    end
  #    mul!(t2, t1, inv_special_basis_matrix_Hinv)
  #    for (j, j_index) in enumerate(p)
  #      push!(_local_coeffs, QQFieldElem[ t2[j, k] for k in 1:dim(A)])
  #    end
  #    #push!(_local_coeffs, auiasvec)
  #  end
  #  push!(local_coeffs2, _local_coeffs)
  #end
  #@info "done"
  #@assert local_coeffs == local_coeffs2

  #for i in 1:length(dec)
  #  @show local_coeffs
  #end

  # Try to reduce the number of tests
  #@info "Collected information for the last block"
  l = bases_offsets_and_lengths[end][2]
  o = bases_offsets_and_lengths[end][1]
  indices_integral = Vector{Int}[Int[] for i in 1:l]
  indices_nonintegral = Vector{Int}[Int[] for i in 1:l]
  for j in 1:length(local_coeffs[end])
    for i in o:(o + l - 1)
      if is_integral(local_coeffs[end][j][i])
        push!(indices_integral[i - o + 1], j)
      else
        push!(indices_nonintegral[i - o + 1], j)
      end
    end
  end

  @vprintln :PIP "Lengths $(length.(local_coeffs))"
  @vprintln :PIP "Unrestricted length of last block: $(length(local_coeffs[end]))"
  @vprintln :PIP "Restricted lengths (integral) of the last block $(length.(indices_integral))"
  @vprintln :PIP "Restricted lengths (non-integral) of the last block $(length.(indices_nonintegral))"

  dd = dim(A)

  # form the product of the first sets
  #@show length(cartesian_product_iterator([1:length(local_coeffs[i]) for i in 1:length(dec) - 1]))

  @vprintln :PIP "Starting the new method :)"
  fl, x = recursive_iterator([length(local_coeffs[i]) for i in 1:length(dec)], dd, local_coeffs, bases_offsets_and_lengths, indices_integral, indices_nonintegral)
  @vprintln :PIP "New method says $fl"
  if fl
    _vtemp = reduce(.+, (local_coeffs[i][x[i]] for i in 1:length(local_coeffs)))
    el = A(_vtemp * (H * special_basis_matrix))
    el = inv(sca) * el
    @assert el * O == Iorig
    #@vprintln :PIP "Checking with old method"
    #ffl, xx = _old_optimization(dd, local_coeffs, dec, bases_offsets_and_lengths, H, special_basis_matrix, indices_integral, indices_nonintegral, A)
    #@assert ffl
    return true, el
  end

  return false, zero(A)
#
#  ffl, xx = _old_optimization(dd, local_coeffs, dec, bases_offsets_and_lengths, H, special_basis_matrix, indices_integral, indices_nonintegral, A)
#
#  @assert fl === ffl
#  return ffl, inv(sca) * xx
#

  for u in Iterators.product(unit_reps...)
    uu = sum(dec[i][2](dec[i][2]\(u[i])) for i in 1:length(dec))
    aui = [ dec[i][2](dec[i][2]\(alpha)) * dec[i][2](dec[i][2]\(u[i])) for i in 1:length(dec)]
    @assert sum(aui) == alpha * uu
    if alpha * uu in I
      return true, inv(sca) * alpha * uu
    end
  end
  return false, zero(O)
end

function _old_optimization(dd, local_coeffs, dec, bases_offsets_and_lengths, H, special_basis_matrix, indices_integral, indices_nonintegral, A)
  vtemp = [zero(QQFieldElem) for i in 1:dd]
  k = 0
  l = 0
  ll = [0 for i in 1:length(local_coeffs)]
  for idx in cartesian_product_iterator([1:length(local_coeffs[i]) for i in 1:length(dec) - 1])
    k += 1
    if k % 1000000 == 0
      @vprintln :PIP "$k"
    end
    w = local_coeffs[1][idx[1]]
    for i in 1:dd
      set!(vtemp[i], w[i])
    end
    #@show vtemp
    for j in 2:(length(dec) - 1)
      w = local_coeffs[j][idx[j]]
      for i in bases_offsets_and_lengths[j][1]:dd
        add!(vtemp[i], vtemp[i], w[i])
      end
      #@show j, vtemp
    end
    #@show vtemp
    #@assert vtemp == reduce(.+, (local_coeffs[j][idx[j]] for j in 1:length(dec) - 1))
    if any(!is_integral, @view vtemp[1:bases_offsets_and_lengths[end][1] - 1])
      l += 1
      j = findfirst([any(!is_integral, vtemp[bases_offsets_and_lengths[j][1]:bases_offsets_and_lengths[j + 1][1] - 1]) for j in 1:length(dec) - 1])
      ll[j] += 1
      continue
    else
      @vprintln :PIP "good"
    end
    o = bases_offsets_and_lengths[end][1]
    l = bases_offsets_and_lengths[end][2]
    ids = reduce(intersect, [is_integral(vtemp[o - 1 + i]) ? indices_integral[i] : indices_nonintegral[i] for i in 1:l])
    _vtempcopy = deepcopy(vtemp)
    #@show length(ids)
    for j in ids
      #for i in 1:dd
      #  set!(vtemp[i], _vtempcopy[i])
      #end
      _vtemp = deepcopy(vtemp) .+ local_coeffs[end][j]
      if all(is_integral, _vtemp)
        @vprintln :PIP "found x = $((idx...,j))"
        return true, A(_vtemp * (H * special_basis_matrix))
      end
    end
  end
  @vprintln :PIP "when I could have skipped $ll"
  @vprintln :PIP "Skipped $l things"

  return false, zero(A)
end

#
function _recursive_iterator!(x, lengths, d, elts::Vector, bases_offsets, indices_integral, indices_nonintegral, k, i, vtemp::Vector{QQFieldElem})
  if i > k
    println("2", x)
  elseif i == k # unroll 1-loop base case for speed
    # this is the last component

    # We do something clever for the indices
    o = bases_offsets[end][1]
    l = bases_offsets[end][2]
    ids = copy(is_integral(vtemp[o]) ? indices_integral[1] : indices_nonintegral[1])
    for i in 2:l
      intersect!(ids, is_integral(vtemp[o - 1 + i]) ? indices_integral[i] : indices_nonintegral[i])
    end

    #ids2 = reduce(intersect!, (is_integral(vtemp[o - 1 + i]) ? indices_integral[i] : indices_nonintegral[i] for i in 1:l))
    #@assert ids == ids2

    for j in ids # 1:lengths[i]
      x[i] = j
      if _is_admissible(x, i, d, elts, bases_offsets, vtemp)
        #@assert all(is_integral, reduce(.+, (elts[k][x[k]] for k in 1:length(elts))))
        return true
      end
      #if _is_admissible(x, i, d, elts, bases_offsets)
      #  return true
      #end
      # here is the work done
    end
    return false
  else
    for j = 1:lengths[i]
      x[i] = j
      # So x = [...,j,*]
      # We test whether this is admissible
      if !_is_admissible(x, i, d, elts, bases_offsets, vtemp)
        continue
      end
      fl = _recursive_iterator!(x, lengths, d, elts, bases_offsets, indices_integral, indices_nonintegral, k, i + 1, vtemp)
      if fl
        return true
      end
    end
    return false
  end
end

function _is_admissible(x, i, d, elts, bases_offsets, vtemp::Vector{QQFieldElem})
  # Test if x[1,...,i] is admissible
  w = elts[1][x[1]]
  for k in 1:d
    set!(vtemp[k], w[k])
  end
  #@show vtemp
  for j in 2:i
    w = elts[j][x[j]]
    #@assert all(iszero, @view w[1:bases_offsets[j][1] - 1])
    for k in bases_offsets[j][1]:d
      add!(vtemp[k], w[k])
    end
  end

  #@show i, vtemp

  # admissible means different things for different i
  # if i < end
  # then admissible means that the first i component of vtemp must be integral
  #
  # if i == end,
  # then admissible means that the last component must be integral

  vvtemp = @view vtemp[bases_offsets[i][1]:(bases_offsets[i][1] + bases_offsets[i][2] - 1)]

  if any(!is_integral, vvtemp)
    return false
  else
    return true
  end
end

function recursive_iterator(lengths::Vector{Int}, d::Int, elts::Vector, bases_offsets::Vector{Tuple{Int, Int}}, indices_integral, indices_nonintegral)
  k = length(lengths)
  x = zeros(Int, k)
  vtemp = QQFieldElem[zero(QQFieldElem) for i in 1:d]
  if _recursive_iterator!(x, lengths, d, elts, bases_offsets, indices_integral, indices_nonintegral, k, 1, vtemp)
    return true, x
  else
    return false, zeros(Int, k)
  end
end

function _local_coeffs_buffer(A, l)
  D = get_attribute!(A, :local_coeffs_buffer) do
    Dict{Vector{Int}, Vector{Vector{Vector{QQFieldElem}}}}()
  end::Dict{Vector{Int}, Vector{Vector{Vector{QQFieldElem}}}}

  return get!(D, l) do
    Vector{Vector{QQFieldElem}}[Vector{QQFieldElem}[ QQFieldElem[zero(QQFieldElem) for i in 1:dim(A)] for ii in 1:l[j]] for j in 1:length(l)]
  end::Vector{Vector{Vector{QQFieldElem}}}
end

function _compute_local_coefficients_parallel(alpha, A, dec_sorted, units_sorted, M, block_size = 1)
  #push!(_debug, (alpha, A, dec_sorted, units_sorted, M, block_size))
  res = Vector{Vector{QQFieldElem}}[]
  k = dim(A)
  kblock = k * block_size
  if VERSION >= v"1.11"
    nt = Threads.maxthreadid()
  else
    nt = Threads.nthreads()
  end

  @assert size(M) == (k, k)
  #@assert all(x -> ncols(x) == k, tmps)
  #@assert all(x -> ncols(x) == k, tmps2)
  __local_coeffs = _local_coeffs_buffer(A, length.(units_sorted))
  for i in 1:length(dec_sorted)
    ui = units_sorted[i]
    #@info "Allocating for result"
    _local_coeffs = __local_coeffs[i]
    #_local_coeffs = _local_coeffs_buffer(A, length(ui)) #Vector{QQFieldElem}[ QQFieldElem[zero(QQFieldElem) for i in 1:k] for ii in 1:length(ui)]
    #_local_coeffs = Vector{QQFieldElem}[ QQFieldElem[zero(QQFieldElem) for i in 1:k] for ii in 1:length(ui)]
    m = dec_sorted[i][2]::morphism_type(StructureConstantAlgebra{QQFieldElem}, typeof(A))
    alphai = dec_sorted[i][2](dec_sorted[i][2]\(alpha))
    kblock = div(length(ui), nt)
    if mod(length(ui), nt) != 0
      kblock += 1
    end
    if length(ui) < 100
      kblock = length(ui)
    end
    par = collect(Iterators.partition(1:length(ui), kblock))
    @assert length(ui) < 100 || length(par) == nt
    #@info "Length/Blocksize: $(length(ui))/$(kblock)"
    tmps = [zero_matrix(QQ, kblock, k) for i in 1:nt]
    tmps2 = [zero_matrix(QQ, kblock, k) for i in 1:nt]
    tmp_elem = [A() for i in 1:nt]
    if length(par) >= nt
      GC.gc(true)
      Threads.@threads :static for i in 1:length(par)
        #thi = 1 #Threads.threadid()
        thi = Threads.threadid()
        p = par[i]
        t1 = tmps[thi]
        t2 = tmps2[thi]
        t_elem = tmp_elem[thi]
        for (j, j_index) in enumerate(p)
          u =  ui[j_index]
          #aui =  alphai * u
          mul!(t_elem, alphai, u)
          __set_row!(t1, j, coefficients(t_elem, copy = false))
        end
        mul!(t2, t1, M)
        for (j, j_index) in enumerate(p)
          Hecke.__set_row!(_local_coeffs[j_index], t2, j)
        end
      end
    else
      for i in 1:length(par)
        #thi = 1 #Threads.threadid()
        thi = 1
        p = par[i]
        t1 = tmps[thi]
        t2 = tmps2[thi]
        t_elem = tmp_elem[thi]
        for (j, j_index) in enumerate(p)
          u =  ui[j_index]
          mul!(t_elem, alphai, u)
          __set_row!(t1, j, coefficients(t_elem, copy = false))
        end
        mul!(t2, t1, M)
        for (j, j_index) in enumerate(p)
          Hecke.__set_row!(_local_coeffs[j_index], t2, j)
        end
      end
    end
    push!(res, _local_coeffs)
  end
  return res
end


