mutable struct G1Model{T}
  degree::Int
  equations::Vector{MPolyRingElem{T}}
  defining_equation::MPolyRingElem

  function G1Model{T}() where {T}
    D = new{T}()
    return D
  end
end

function degree(D::G1Model{T}) where T
  return D.degree
end

function equations(D::G1Model{T}) where T
  return D.equations
end

function g1_model_d2(Q::MPolyRingElem{T}, P::MPolyRingElem{T}) where T
  R_P = parent(P)
  K = base_ring(R_P)
  @req number_of_generators(R_P) == 2 "Q and P need to be defined over a polynomial ring with 2 variables."
  @req parent(Q) == R_P "P and Q need to have the same parent."
  @req is_homogeneous(P) && is_homogeneous(Q) "P and Q need to be homogeneous."
  println(Q)
  println(total_degree(P))
  @req (total_degree(P) == 2 || total_degree(P) == -1) && total_degree(Q) == 4 "P needs to be of degree 2 and Q needs to be of degree 4."

  (x1,x2) = gens(R_P)
  R, (x, y, z) = K[:x,:y,:z]
  D = G1Model{T}()
  D.degree = 2
  eqs = [Q, P]
  D.defining_equation = -y^2 - P(x,z)*y - Q(x,z)
  D.equations = eqs
  return D
end

function g1_model_d3(F::MPolyRingElem{T}) where T
  R_P = parent(P)
  K = base_ring(R_P)
  @req number_of_generators(R_Q1) == 3 "F needs to be defined over a polynomial ring with 3 variables."
  @req is_homogeneous(P) && is_homogeneous(Q) "F needs to be homogeneous."
  @req total_degree(F) == 3 "F needs to be of degree 3."

  D = G1Model{T}()
  D.degree = 3
  D.equations = [F]
  return D
end

function g1_model_d4(Q1::MPolyRingElem{T}, Q2::MPolyRingElem{T}) where T
  R_Q1 = parent(Q1)
  K = base_ring(Q1)
  @req number_of_generators(R_Q1) == 4 "Q1 and Q1 need to be defined over a polynomial ring with 4 variables."
  @req parent(Q2) == R_Q1 "Q1 and Q2 need to have the same parent."
  @req is_homogeneous(Q1) && is_homogeneous(Q2) "Q1 and Q2 need to be homogeneous."
  @req total_degree(Q1) == 2 && total_degree(Q2) == 2 "Q1 and Q2 need to be of degree 2."

  D = G1Model{T}()
  D.degree = 4
  D.equations = [Q1, Q2]
  return D
end

function jacobian(D::G1Model)
  return elliptic_curve(a_invariants(D))
end

