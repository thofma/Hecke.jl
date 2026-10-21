################################################################################
#
#  Principal ideals in totally definite quaternion algebras
#
################################################################################

# Whether A is a quaternion algebra over QQ or over a totally real number
# field that ramifies at every real place: (a, b) is ramified at a real place
# exactly when a and b are both negative there.
function _is_totally_definite_quaternion(A::AbstractAssociativeAlgebra)
  A isa QuaternionAlgebra || return false
  K = base_ring(A)
  a, b = standard_form(A)
  if K isa QQField
    return a < 0 && b < 0
  end
  K isa AbsSimpleNumField || return false
  is_totally_real(K) || return false
  return all(P -> is_negative(a, P) && is_negative(b, P), real_places(K))
end

# Whether the right ideal I = beta O (side = :right), or the left ideal
# I = O beta (side = :left), of the order O is principal, and such a beta.
# The algebra A of O must be central of dimension 4 over QQ or a totally real
# field K, and ramified at every real place; O may be any order.
#
# If I = beta O, then [O : I] = (nrd(beta) R)^2, with R the ring of integers
# of K, and an element of I of reduced norm nrd(beta) z, for a totally
# positive unit z of R, is beta times an element of O of reduced norm z, a
# unit of O: a generator too. So with [O : I] = (cR)^2, I is principal exactly
# when it holds an element x of reduced norm cz, for z running over the
# totally positive units modulo squares, with x O = I, and then every element
# of I of reduced norm cz is a generator. On the Z-lattice I, the positive
# definite form x -> Tr_{K/Q}(trd(x conj(y))/(cz)) takes the value
# 2 Tr_{K/Q}(nrd(x)/(cz)) at x, which is 2[K : Q] when nrd(x) = cz. So each z
# costs one query for the vectors of that length, and the first of them of
# reduced norm cz decides: it generates I if I is principal. When nrd(x) lies
# in cR, as for an invertible ideal, the value 2[K : Q] forces nrd(x) = cz
# (arithmetic and geometric mean); the reduced norm is still checked, since
# for an ideal that is not invertible the norms need not lie in cR. Checking
# x O = I likewise makes the answer correct for such an ideal, where Lemma 4.8
# of Kirschmer-Voight (SIAM J. Comput. 39 (2010), 1714-1747), on which
# Algorithm 6.3 there rests, does not apply.
function _is_principal_with_data_definite_quaternion(I, O, side::Symbol)
  @req side === :right || side === :left "side must be :right or :left"
  A = algebra(O)
  fl, c, units = _reduced_norm_generator(I, O)
  fl || return false, zero(A)
  f = standard_involution(A)
  B = absolute_basis(I)
  d = length(B)
  n = div(d, 4)
  P = [trred(B[i] * f(B[j])) for i in 1:d, j in 1:d]
  for z in units
    w = inv(c * z)
    G = matrix(QQ, d, d, [absolute_tr(w * P[i, j]) for i in 1:d, j in 1:d])
    L = integer_lattice(; gram = G, check = false)
    for (v, _) in short_vectors_iterator(L, 2 * n, 2 * n; check = false)
      beta = sum(v[i] * B[i] for i in 1:d)
      normred(beta) == c * z || continue
      if side === :right
        fl = beta * O == I
      else
        fl = O * beta == I
      end
      return fl, fl ? beta : zero(A)
    end
  end
  return false, zero(A)
end

# A generator c of the reduced norm of the ideal I of O, if it is principal,
# and representatives of the totally positive units modulo squares, so that
# c z runs over the possible reduced norms of a generator of I.
function _reduced_norm_generator(I::AlgAssAbsOrdIdl, O::AlgAssAbsOrd)
  fl, c = is_power(norm(I, O), 2)
  return fl, QQ(c), QQFieldElem[one(QQ)]
end

function _reduced_norm_generator(I::AlgAssRelOrdIdl, O::AlgAssRelOrd)
  K = base_ring(algebra(O))
  fl, N = is_power(norm(I, O), 2)
  fl || return false, zero(K), elem_type(K)[]
  fl, c = is_principal_with_data(N)
  fl || return false, zero(K), elem_type(K)[]
  c = K(c)
  fl, u, units = _reps_for_totally_positive(c, K)
  return fl, u * c, units
end
