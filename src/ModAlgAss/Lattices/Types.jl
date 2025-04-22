################################################################################
#
#  Lattice type
#
################################################################################

@attributes mutable struct ModAlgAssLat{S, T, U}
  base_ring::S   # the underlying order
  V::T           # the underlying module
  basis::U       # the basis matrix
  basis_inv::U   # the inverse of the basis matrix

  function ModAlgAssLat{S, T, U}(base_ring::S, V::T, basis::U) where {S, T, U}
    z = new{S, T, U}()
    z.base_ring = base_ring
    z.V = V
    z.basis = basis
    return z
  end
end
