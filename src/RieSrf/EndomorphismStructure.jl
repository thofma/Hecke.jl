################################################################################
#
#  Endomorphism structure of abelian varieties
#
#  apres
#    https://doi.org/10.1090/mcom/3373
#  and
#    https://github.com/edgarcosta/endomorphisms
#  by
#   Edgar Costa, Davide Lombardo, Jeroen Sijsling
#
################################################################################

################################################################################
#
#  Stubs for functionality not yet in Hecke
#
################################################################################

@doc raw"""
    rosati_fixed_module(EndoRep) -> Vector

Given a representation `EndoRep` of an endomorphism ring as a list of pairs
$(A, R)$ (analytic and rational homological representations), return a basis of
the submodule of generators fixed by the Rosati involution
$R \mapsto -J R^\top J$, where $J$ is the standard symplectic matrix.
"""
function rosati_fixed_module(EndoRep)
  As = [gen[1] for gen in EndoRep]
  Rs = QQMatrix[QQ.(gen[2]) for gen in EndoRep]
  k = length(Rs)
  n = nrows(Rs[1])   # n = 2g
  g = div(n, 2)

  # Standard symplectic matrix J = [0 I_g; -I_g 0]
  J = zero_matrix(QQ, n, n)
  for i in 1:g
    J[i, g + i] = QQ(1)
    J[g + i, i] = QQ(-1)
  end

  # Rdiff[j] = Rosati(Rs[j]) - Rs[j] = -J * Rs[j]^T * J - Rs[j]
  Rdiffs = QQMatrix[-J * transpose(R) * J - R for R in Rs]

  # Build coefficient matrix A (k x n^2): row i = vectorization of Rs[i]
  A = zero_matrix(QQ, k, n^2)
  for i in 1:k
    for r in 1:n, c in 1:n
      A[i, (r - 1) * n + c] = Rs[i][r, c]
    end
  end

  # For each Rdiff, express it in the basis {Rs[i]} by solving
  # transpose(A) * s = vec(Rdiff), i.e. sum_i s[i]*Rs[i] = Rdiff
  rows = Vector{QQFieldElem}[]
  for Rdiff in Rdiffs
    rhs = matrix(QQ, n^2, 1, [Rdiff[r, c] for r in 1:n for c in 1:n])
    fl, s = can_solve_with_solution(transpose(A), rhs; side = :right)
    @assert fl "Rdiff is not in the QQ-span of the generators"
    push!(rows, QQFieldElem[s[i, 1] for i in 1:k])
  end

  # M is k x k; row j = coordinate vector of Rdiffs[j] in {Rs[i]}
  M = matrix(QQ, k, k, reduce(vcat, rows))

  # Left kernel of M: rows b with b * M = 0
  # <-> sum_i b[i] * Rs[i] is fixed by the Rosati involution
  B = kernel(M; side = :left)
  dim_ker = nrows(B)

  CC = base_ring(As[1])
  result = []
  for i in 1:dim_ker
    b = QQFieldElem[B[i, j] for j in 1:k]
    Afixed = sum(CC(b[j]) * As[j] for j in 1:k)
    Rfixed = sum(b[j] * Rs[j] for j in 1:k)
    push!(result, (Afixed, Rfixed))
  end
  return result
end

################################################################################
#
#  Building a StructureConstantAlgebra from rational matrix generators
#
################################################################################

# Given a list of rational matrices `gens` (generators of a matrix subalgebra
# of M_n(QQ)), build the StructureConstantAlgebra they generate together with
# the elements of that algebra corresponding to each generator.
#
# Returns (C, GensC) where:
#   - C = StructureConstantAlgebra over QQ
#   - GensC = Vector of elements of C, one per input generator
function _algebra_from_generators(gens::Vector{<:MatElem{QQFieldElem}})
  @assert !isempty(gens) "Need at least one generator"

  MA = matrix_algebra(QQ, gens)
  C, CtoMA  = StructureConstantAlgebra(MA)
  GensC = elem_type(C)[preimage(CtoMA, MA(g)) for g in gens]

  return C, GensC
end

################################################################################
#
#  Matrix from idempotent
#
################################################################################

# Given:
#   C = StructureConstantAlgebra over QQ
#   GensC = generators of C (as elements of C), aligned with Rs
#   idem = an idempotent element of C
#   Rs = vector of QQMatrix (the rational homology matrices)
#
# Express idem as a linear combination of GensC and return the corresponding
# linear combination of the rational matrices.
function _matrix_from_idempotent(
    C,
    GensC::Vector,
    idem,
    Rs::Vector{<:MatElem{QQFieldElem}},
  )
  k  = length(GensC)
  d  = dim(C)

  # Build matrix M (k × d): row j = coordinates of GensC[j] in the basis of C
  M = zero_matrix(QQ, k, d)
  for j in 1:k
    coords = coefficients(GensC[j])
    for l in 1:d
      M[j, l] = coords[l]
    end
  end

  # Coordinates of idem in basis of C  (d × 1 column vector)
  idem_col = matrix(QQ, d, 1, coefficients(idem))

  # Solve M^T * alpha = idem_col  (d × k system, k unknowns)
  fl, alpha = can_solve_with_solution(transpose(M), idem_col; side = :right)
  @assert fl "Could not express idempotent as linear combination of generators"

  # Return sum_j alpha[j] * Rs[j]
  n = nrows(Rs[1])
  idemR = zero_matrix(QQ, n, n)
  for j in 1:length(Rs)
    idemR = idemR + alpha[j, 1] * Rs[j]
  end
  return idemR
end

################################################################################
#
#  Discriminant descriptor for a quaternion-type component
#
################################################################################

# For a central simple algebra E1 over its center F (a number field or QQ)
# with dim(E1) = 4 (quaternion algebra), compute the signed squarefree integer
# encoding the finite ramification, following the Magma convention:
#   disc > 0  <->  indefinite (not ramified at any real place)
#   disc < 0  <->  definite   (ramified at all real places of F)
#   disc = 1  <->  split (matrix ring M_2(F))
#
# For algebras over non-QQ number fields, only the squarefree radical of the
# norm of the finite part of the discriminant is computed; the sign encodes
# parity of the number of distinct prime factors of that norm (Magma convention).
function _disc_descriptor(E1)
  if is_split(E1)
    return ZZRingElem(1)
  end

  F = base_ring(E1)

  if F isa QQField
    # local_schur_indices over QQ returns Pair{ZZRingElem, Int}
    # where 0 represents the infinite place
    lsd = Hecke.local_schur_indices(E1)
    finite_ram = ZZRingElem[p for (p, _) in lsd if !iszero(p)]
    disc = prod(finite_ram; init = ZZRingElem(1))
    if isone(disc)
      return ZZRingElem(1)
    end
    fac = collect(factor(disc))
    disc_rad = isempty(fac) ? ZZRingElem(1) : prod(ZZRingElem(p) for (p, _) in fac)
    # QQ is totally real; odd number of finite ramified primes <-> definite
    if isodd(length(fac))
      disc_rad = -disc_rad
    end
    return disc_rad
  else
    # F is an AbsSimpleNumField
    # local_schur_indices returns Any[], mixing InfPlc and prime-ideal keys
    lsd = Hecke.local_schur_indices(E1)
    # Collect norms of finite ramified prime ideals
    norm_disc = ZZRingElem(1)
    n_finite  = 0
    for (p, _) in lsd
      if p isa InfPlc
        continue
      end
      norm_disc = norm_disc * norm(p)
      n_finite += 1
    end
    if isone(norm_disc)
      return ZZRingElem(1)
    end
    fac = collect(factor(norm_disc))
    disc_rad = isempty(fac) ? ZZRingElem(1) : prod(ZZRingElem(q) for (q, _) in fac)
    if is_totally_real(F) && isodd(length(fac))
      disc_rad = -disc_rad
    end
    return disc_rad
  end
end

################################################################################
#
#  Endomorphism algebra description over QQ
#
################################################################################

# Analyse the semisimple QQ-algebra C and return:
#   C = the algebra itself
#   EndoDescQQ = sorted vector of NamedTuples, one per simple component
#   idems = central idempotents of C (one per simple component)
#
# Each entry of EndoDescQQ is a NamedTuple with fields:
#   m::Int = the matrix size in M_m(Δ)
#   dimalg::Int = dimension of the division ring Δ over QQ
#   center::AbsSimpleNumField = the center (field) of the component
#   disc::ZZRingElem = discriminant descriptor (see _disc_descriptor)
#   dimfac::Int = mdimfac = rank(idemR)/2 (genus contribution)
function _endo_algebra_QQ(C, GensC::Vector, Rs::Vector{<:MatElem{QQFieldElem}}; sort_result::Bool = true)
  decomp  = decompose(C)
  idems   = elem_type(C)[DtoC(one(D)) for (D, DtoC) in decomp]

  EndoDescQQ = NamedTuple[]

  for i in 1:length(decomp)
    D, DtoC = decomp[i]
    idem = idems[i]

    # View D as an algebra over its center F
    E1, _  = Hecke._as_algebra_over_center(D)
    F = base_ring(E1)
    dimF = (F isa QQField) ? 1 : degree(F)

    # Dimension of E1 over F; must be a perfect square m^2*s^2
    m2reldimalg = dim(E1)
    fl, sqrtm2rel = is_square_with_sqrt(ZZ(m2reldimalg))
    if !fl
      error("Dimension of algebra over center is not a perfect square: ", m2reldimalg)
    end
    sqrtm2reldimalg = Int(sqrtm2rel)

    # Genus contribution from this idempotent
    idemR = _matrix_from_idempotent(C, GensC, idem, Rs)
    mdimfac = rank(idemR) ÷ 2

    # Determine Schur index s of E1 over F and the matrix-ring factor m
    s = schur_index(E1)        # global Schur index (= 1 or 2 in genus ≤ 7)
    m_val = div(sqrtm2reldimalg, s)   # matrix size

    reldimalg = s^2                # dim of division ring over F
    dimalg = dimF * reldimalg   # dim of division ring over QQ
    dimfac = div(mdimfac, m_val)

    disc = _disc_descriptor(E1)

    desc = (m = m_val, dimalg = dimalg, center = F, disc = disc, dimfac = dimfac)
    push!(EndoDescQQ, desc)
  end

  if sort_result
    sort!(EndoDescQQ; by = d -> d.m)
  end

  return C, EndoDescQQ, idems
end

################################################################################
#
#  Endomorphism algebra description over RR
#
################################################################################

# From the QQ description, determine the real type of each Wedderburn component.
#
# Each entry of EndoDescRR is a Tuple{Int, Int} where:
#   first  = matrix size
#   second = Albert type:
#              1 -> M_n(RR)           (totally real field or indefinite quat)
#              2 -> M_n(CC)           (CM field)
#              4 -> M_n(Hamilton's H) (definite quaternion algebra)
#
# Albert classification of simple components:
#   Type I   — totally real F, Schur index 1 -> M_{d*m}(RR)^e     disc=1, d=sqrt(reldimalg)
#   Type II  — totally real F, indefinite quat (disc>0) -> M_{d*m}(RR)^e  (m = matrix in quat-mat)
#   Type III — totally real F, definite quat   (disc<0) -> M_m(H)^e
#   Type IV  — CM field F -> M_{d*m}(CC)^(e/2)
function _endo_algebra_RR(EndoDescQQ::Vector)
  EndoDescRR = Tuple{Int, Int}[]

  for desc in EndoDescQQ
    m, dimalg, F, disc, dimfac = desc.m, desc.dimalg, desc.center, desc.disc, desc.dimfac
    if m == -1
      push!(EndoDescRR, (-1, -1))
      continue
    end

    e = (F isa QQField) ? 1 : degree(F)
    d_sq = dimalg ÷ e          # = s^2 where s = Schur index
    fl, d = is_square_with_sqrt(ZZ(d_sq))
    @assert fl "dimalg/degree(center) is not a perfect square"
    d = Int(d)                   # Schur index

    if (F isa QQField) ? true : is_totally_real(F)
      if d == 2
        if sign(disc) == 1
          # Type II: matrix ring over indefinite quaternion algebra
          append!(EndoDescRR, [((d * m), 1) for _ in 1:e])
        else
          # Type III: matrix ring over definite quaternion algebra
          append!(EndoDescRR, [(m, 4) for _ in 1:e])
        end
      else
        # Type I: matrix ring over totally real field F
        append!(EndoDescRR, [((d * m), 1) for _ in 1:e])
      end
    else
      # Type IV: matrix ring over CM field F
      append!(EndoDescRR, [((d * m), 2) for _ in 1:(e ÷ 2)])
    end
  end

  sort!(EndoDescRR)
  return EndoDescRR
end

################################################################################
#
#  Endomorphism algebra description over ZZ
#
################################################################################

# Compute an order OC in C generated by GensC and describe it.
#
# Returns (GensC, desc) where desc is a NamedTuple with fields:
#   index::ZZRingElem = index of OC in the maximal order
#   eichler::Int = 1 if OC is Eichler, 0 if not, -1 if not applicable
function _endo_algebra_ZZ(C, GensC::Vector)
  OC = order(C, GensC)
  DOC = discriminant(OC)
  DOM = discriminant(maximal_order(C))

  fl, ind = is_square_with_sqrt(DOC // DOM)
  @assert fl "Index of order in maximal order is not a perfect square"
  ind = ZZ(ind)

  decomp = decompose(C)
  eichler_flag = -1

  if length(decomp) == 1
    D, DtoC  = decomp[1]
    E1, E1toD = Hecke._as_algebra_over_center(D)
    F = base_ring(E1)

    if dim(E1) == 4 && (F isa QQField || (F isa AbsSimpleNumField && degree(F) == 1))
      # Single quaternion algebra component over QQ — check Eichler
      fl, QE1toE1 = Hecke._is_quaternion_algebra(E1)
      @assert fl
      QE1 = domain(QE1toE1)

      CC = order(QE1, [QE1toE1\(E1toD\(DtoC\(c))) for c in GensC])

      if is_eichler(CC)
        eichler_flag = 1
      else
        eichler_flag = 0
      end
    end
  end

  desc = (index = ind, eichler = eichler_flag)
  return GensC, desc
end

################################################################################
#
#  Main function
#
################################################################################

@doc raw"""
    endomorphism_structure(EndoRep; calc_pic=true)
      -> Tuple{Tuple, Tuple}

Given a representation `EndoRep` of an endomorphism ring of an abelian variety,
return the endomorphism structure over the base field.

`EndoRep` is a vector of pairs `(A, R)` where:
  - `A` is a $g \times g$ analytic (complex) matrix
  - `R` is a $2g \times 2g$ rational (homology) matrix

Returns `(EndoAlg, EndoDesc)` where:

  `EndoAlg = (C, GensC)`:
  - `C::StructureConstantAlgebra{QQFieldElem}` = the endomorphism algebra
  - `GensC` = generators of the endomorphism order inside `C`

  `EndoDesc = (EndoDescRR, EndoDescQQ, EndoDescZZ[, pic])`:
  - `EndoDescRR` = sorted vector of `(matrix_size, albert_type)` pairs (over RR)
  - `EndoDescQQ` = sorted vector of NamedTuples describing simple QQ-components
  - `EndoDescZZ` = NamedTuple `(index, eichler)` describing the endomorphism order
  - `pic` = size of the Rosati-fixed module (only if `calc_pic = true`)

Albert types in `EndoDescRR`:
  1 -> $M_n(\mathbb{R})$
  2 -> $M_n(\mathbb{C})$
  4 -> $M_n(\mathbb{H})$

Each entry of `EndoDescQQ` has fields:
  - `m` = matrix size in $M_m(\Delta)$
  - `dimalg` = $\dim_{\mathbb{Q}}(\Delta)$
  - `center` = the centre field $F$
  - `disc` = discriminant descriptor (1 if split; signed squarefree otherwise)
  - `dimfac` = genus contribution of this component
"""
function endomorphism_structure(EndoRep::Vector; calc_pic::Bool = true)
  Rs = QQMatrix[QQ.(gen[2]) for gen in EndoRep]
  @assert !isempty(Rs) "EndoRep must be non-empty"
  g  = div(nrows(Rs[1]), 2)

  # Build the structure constant algebra C generated by the rational matrices
  C, GensC = _algebra_from_generators(Rs)

  # Analyse the algebra
  EndoAlgQQ, EndoDescQQ, _idems = _endo_algebra_QQ(C, GensC, Rs)
  EndoAlgZZ, EndoDescZZ = _endo_algebra_ZZ(C, GensC)
  EndoDescRR = _endo_algebra_RR(EndoDescQQ)

  EndoAlg = (C, GensC)

  if calc_pic
    pic = length(rosati_fixed_module(EndoRep))   # stub
    EndoDesc = (EndoDescRR, EndoDescQQ, EndoDescZZ, pic)
  else
    EndoDesc = (EndoDescRR, EndoDescQQ, EndoDescZZ)
  end

  return EndoAlg, EndoDesc
end
