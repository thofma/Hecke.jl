################################################################################
#
#   FakeAbsOrdQuoRing
#
################################################################################

# The following is a fake implementation for finite O/I to speed up
# multiplication in the quotient ring. This is good for applications where you
# only do computations in O/I and there is not much going back and forth
# between O and O/I.
#
# At the moment, the additive structure is not implemented and there is some
# other restriction, but it would not be hard to implement the full
# ring interface.
#
# We use the SNF basis SI of I, meaning that if a = (x_1,...,x_n) is an element
# with respect to this basis, then reduction modulo I is very cheap.  It is
# just the reduction of the x_i mod n_i.
#
# We represent [a] in O/I by the vector (x_1,...,x_n) *and* an nxn matrix M
# over Z/mZ, where m is the exponent of O/I. The matrix M is the transpose of
# the representation matrix of z -> z * a with respect to SI. Note that this
# matrix M does not identify a uniquely.
#
# Two elements (x, M), (y, N) are multiplied by doing (N * x, N * M). Note that
# N * x has to be reduced modulo the n_i.
#
# The reason the transposing and change of order appears is not fully written
# down yet, but it seems to work.

mutable struct FakeAbsOrdQuoRing{S, T, U, V}
  O::S                      # the order
  id::T                     # the ideal
  B::U                      # the SNF basis of the ideal
  eldiv::V                  # the elementary divisors, Vector{Int}
  adjusted_bmat::ZZMatrix   # the basis matrix of B, from basis(O) to B
  n::Int                    # the exponent of O/id
  ZnZ::zzModRing             # the residue ring Z/nZ
  onevec::Vector{Int}       # vector of the one
end

mutable struct FakeAbsOrdQuoRingElem{S}
  rep_mat::zzModMatrix         # reduction of representation matrix mod n
  v::Vector{Int}            # coordinate vector with respect to the SNF basis
                            # this is always reduced
  par::S                    # parent
end

function FakeAbsOrdQuoRing(O::S, id::T) where {S, T}
  B = integral_basis_matrix_wrt(id, O)
  Snf, U, V = snf_with_transform(B)
  # the new basis is given by V^-1, since Snf = U * B * V
  Vinv = inv(V)
  newbas = [ O(_eltseq(Vinv[i:i, :])) for i in 1:degree(O)]
  @assert O == order(algebra(O), elem_in_algebra.(newbas))
  eld = diagonal(Snf)
  # I am assuming everything fits Int :)
  n = Int(eld[end])
  ZnZ = residue_ring(ZZ, n)[1]

  coord = coordinates(one(O)) * V
  coords = Int[Int(mod(coord[i], eld[i])) for i in 1:length(eld)]

  return FakeAbsOrdQuoRing{typeof(O), typeof(id), typeof(newbas), typeof(eld)}(O, id, newbas, eld, Vinv, n, ZnZ, coords)
end

function (R::FakeAbsOrdQuoRing)(x::AlgAssAbsOrdElem)
  repmat = transpose(change_base_ring(R.ZnZ,
                     representation_matrix_wrt(x, R.B, :right)))
  coord = coordinates(x) * inv(R.adjusted_bmat)
  coords = Int[Int(mod(coord[i], R.eldiv[i])) for i in 1:length(R.eldiv)]
  return FakeAbsOrdQuoRingElem{typeof(R)}(repmat, coords, R)
end

# equality
function Base.:(==)(x::FakeAbsOrdQuoRingElem, y::FakeAbsOrdQuoRingElem)
  return x.v == y.v
end

function Base.hash(x::FakeAbsOrdQuoRingElem, h::UInt)
  return hash(x.v, h)
end

# multiplication
function Base.:(*)(x::FakeAbsOrdQuoRingElem, y::FakeAbsOrdQuoRingElem)
  rmat = y.rep_mat * x.rep_mat
  vv = map(n -> Int(n.data), y.rep_mat * (x.par.ZnZ.(x.v)))
  for i in 1:length(vv)
    vv[i] = mod(vv[i], x.par.eldiv[i])
  end
  return FakeAbsOrdQuoRingElem{typeof(x.par)}(rmat, vv, x.par)
end

# isone
function isone(x::FakeAbsOrdQuoRingElem)
  return x.v == x.par.onevec
end

function one(R::FakeAbsOrdQuoRing)
  return FakeAbsOrdQuoRingElem{typeof(R)}(identity_matrix(R.ZnZ, degree(R.O)), R.onevec, R)
end

# lift, mainly for debugging purposes
function lift(x::FakeAbsOrdQuoRingElem)
  c = ZZRingElem.(x.v)
  return dot(c, x.par.B)
end
