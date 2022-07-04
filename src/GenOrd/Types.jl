@attributes mutable struct GenOrd{S, T} <: Ring
  F::S
  R::T
  trans#::dense_matrix_type(elem_type(S))
  itrans#::dense_matrix_type(elem_type(S))
  is_standard::Bool

  function GenOrd(R::AbstractAlgebra.Ring, F::AbstractAlgebra.Field, empty::Bool = false; check::Bool = true)
    #empty allows to create an Order that is none:
    # Z[x]/3x+1 is no order. This will be "fixed" by using any_order, but
    #the intial shell needs to be empty (illegal)
    r = new{typeof(F), typeof(R)}()
    r.F = F
    r.R = R
    r.is_standard = true
    empty && return r
    Qt = base_field(F)
    d = reduce(lcm, map(x->denominator(x, R), coefficients(defining_polynomial(F))))
    f = map_coefficients(x->numerator(Qt(d)*x, R), defining_polynomial(F))
    if !is_monic(f) #need Lenstra Order
      d = degree(F)
      M = zero_matrix(Qt, d, d)
      M[1, 1] = one(Qt)
      for i in 2:d
        for j in i:-1:1
          M[i, j] = coeff(f, d - (i - j))
        end
      end
      O = GenOrd(r, M, one(Qt), check = check)
      return O
    end
    return r
  end

  function GenOrd(O::GenOrd, T::MatElem, d::RingElem; check::Bool = true)
    F = base_field(O.F)
    T = map_entries(F, T)
    T = divexact(T, base_ring(T)(d))
    Ti = inv(T)
    r = GenOrd(O.R, O.F, true)
    r.is_standard = false
    if isdefined(O, :trans)
      r.trans = T*O.trans
      r.itrans = O.itrans*Ti
    else
      r.trans = T
      r.itrans = Ti
    end
    check && map(representation_matrix, basis(r))
    return r
  end
end

mutable struct GenOrdElem{S, T} <: RingElem
  parent::GenOrd
  data::S
  coord::Vector{T}

  function GenOrdElem(O::GenOrd{S, T}, f::FieldElem, check::Bool = false) where {S, T}
    @assert parent(f) === O.F
    if check && !isone(integral_split(f, O)[2])
      error("element not in order")
    end
    r = new{typeof(f), elem_type(T)}()
    r.parent = O
    r.data = f
    return r
  end
end
