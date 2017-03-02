################################################################################
#
#  NfMaxOrd/LinearAlgebra.jl : Linear algebra over maximal orders
#
# This file is part of Hecke.
#
# Copyright (c) 2015, 2016: Claus Fieker, Tommy Hofmann
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
#
# (C) 2016 Tommy Hofmann
#
################################################################################

using Hecke

export pseudo_matrix, pseudo_hnf

function _det_bound(M::GenMat{NfOrdElem{NfMaxOrd}})
  n = rows(M)
  O = base_ring(M)
  d = degree(O)
  c1, c2 = Hecke.norm_change_const(O)

  return fmpz(BigInt(ceil(sqrt(c2)*c1^(n/2)*BigInt(n)^n*BigInt(d)^n*BigInt(_max_max(M))^n)))
end

function _max_max(M::GenMat{NfOrdElem{NfMaxOrd}})
  d = FlintZZ(1)
  for i in 1:rows(M)
    for j in 1:cols(M)
      if !iszero(M[i, j])
        v = elem_in_basis(M[i, j])
        for k in degree(base_ring(M))
          d = max(d, abs(v[k]))
        end
      end
    end
  end
  return d
end
  
#function det(M::GenMat{NfOrdElem{NfMaxOrd}})
#  O = base_ring(M)::NfMaxOrd
#  B = _det_bound(M)
#  p = next_prime(2^60) # magic numbers
#  P = fmpz(1)
#  i = 1
#  res = zero(O)
#  t = 0.0
#  while P < 2*B
#    # reject some bad primes
#    if true  
#      #println("$p");
#      Omodp, pi_p = quo(O, ideal(O, p))
#      Mmodp = MatrixSpace(Omodp, rows(M), cols(M))(M)
#      t += @elapsed detmodp = pi_p\Hecke.det(Mmodp)
#      if i == 1
#        res = detmodp
#      elseif i >= 2
#        g, e, f = gcdx(P, fmpz(p))
#        @assert isone(g)
#        res = f*p*res + e*P*detmodp
#        res = mod_sym(res, P*p)
#        #@assert _basis_coord_nonneg(res)
#      end
#      P = P*p
#      p = next_prime(p)
#      i += 1
#    end
#  end
#  #println("Modular determinant time: $t");
#  return res
#end

function _get_coeff_raw(x::nmod_poly, i::Int)
  u = ccall((:nmod_poly_get_coeff_ui, :libflint), UInt, (Ptr{nmod_poly}, Int), &x, i)
  return u
end

function det(M::GenMat{NfOrdElem{NfMaxOrd}})
  O = base_ring(M)::NfMaxOrd
  K = nf(O)
  B = _det_bound(M)
  if Int==Int64
    p = next_prime(2^61) # magic numbers
  else
    p = next_prime(2^30)
  end  
  P = fmpz(1)
  i = 1
  res = O()
  t_det = 0.0
  t_reducing = 0.0
  t_splitting = 0.0
  used_primes = Array{UInt, 1}()
  tmp_polys = Array{nf_elem, 1}()


  while P < 2*B
    # reject some bad primes
    if isindex_divisor(O, p) 
      continue
    end

    ttt = @elapsed me = modular_init(K, p)

    push!(used_primes, UInt(p))

    t_splitting += ttt

    detmodp = nmod_poly(UInt(p))

    t_reducing += @elapsed Mp = modular_proj(M, me)
    
    t_det += @elapsed detmodQ = [det(x) for x = Mp]

      # now the CRT step
    detmodp = modular_lift(detmodQ, me)

    push!(tmp_polys, detmodp)

    P = P*p
    p = next_prime(p)
    i += 1
  end

  # now the CRT on each coefficient

  fc = crt_env(fmpz[x for x = used_primes])
  fv = Array{fmpz}(length(used_primes))
  for i=1:length(used_primes)
    fv[i] = fmpz(0)
  end
  zz = fmpz()

  @assert length(used_primes) == length(tmp_polys)

  tmp_fmpz_poly = PolynomialRing(FlintZZ)[1]()

  for i in 0:degree(O)
    for j=1:length(used_primes)
      Nemo.num_coeff!(fv[j], tmp_polys[j], i)
    end
    crt!(zz, fv, fc)
    setcoeff!(tmp_fmpz_poly, i, zz)
  end

  tut = fmpq_poly(tmp_fmpz_poly)
  tut.parent = parent(nf(O).pol)
  res = mod_sym(O(nf(O)(tut)), P)
  
  println("Modular determinant time: $t_det");
  println("Time for reducing: $t_reducing");
  println("Time for splitting: $t_splitting");
  println("Used $(length(used_primes)) primes")

  return res
end

# s, t are auxillary variables, r1, r2 are the residues, m1, m2 are the moduli
# aliasing is not allowed (?)
function crt!(z::nmod_poly, r1::nmod_poly, r2::Union{nmod_poly, fq_nmod}, m1::nmod_poly, m2::nmod_poly, s::nmod_poly, t::nmod_poly)
  ccall((:nmod_poly_xgcd, :libflint), Void, (Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{nmod_poly}), &z, &s, &t, &m1, &m2)
  @assert Bool(ccall((:nmod_poly_is_one, :libflint), Cint, (Ptr{nmod_poly}, ), &z))
  # z = s*m1*r2 + t*m2*r1
  mul!(z, s, m1)
  ccall((:nmod_poly_mul, :libflint), Void, (Ptr{nmod_poly}, Ptr{nmod_poly}, Ptr{fq_nmod}), &z, &z, &r2)
  mul!(t, t, m2)
  mul!(t, t, r1)
  add!(z, z, t)
  mul!(s, m1, m2)
  rem!(z, z, s)  
end

function set!(z::nmod_poly, x::nmod_poly)
  ccall((:nmod_poly_set, :libflint), Void, (Ptr{nmod_poly}, Ptr{nmod_poly}), &z, &x)
end

function __helper!(z, mF, entries)
  s = size(entries)
  for i in 1:s[2]
    for j in 1:s[1]
      z[j, i] = mF(entries[j, i])
    end
  end
  return z
end

function mod_sym(x, m)
  z = elem_in_basis(x)
  for i in 1:length(z)
    z[i] = mod(z[i], m)
    if 2*z[i] > m
      z[i] = z[i] - m
    end
  end
  return parent(x)(z)
end

function _basis_coord_nonneg(x)
  b = elem_in_basis(x)
  for i in 1:length(b)
    if b[i] < 0
      return false
    end
  end
  return true
end

function rand(M::GenMatSpace{NfOrdElem{NfMaxOrd}}, B::Union{Int, fmpz})
  z = M()
  for i in 1:rows(z)
    for j in 1:cols(z)
      z[i, j] = Hecke.rand(Hecke.base_ring(M), B)
    end
  end
  return z
end

type PMat
  parent
  matrix::GenMat{nf_elem}
  coeffs::Array{NfMaxOrdFracIdl, 1}

  function PMat(m::GenMat{nf_elem}, c::Array{NfMaxOrdFracIdl, 1})
    z = new()
    z.matrix = m
    z.coeffs = c
    return z
  end
end

function show(io::IO, P::PMat)
  print(io, "Pseudo-matrix over $(parent(P.matrix[1, 1]))\n")
  for i in 1:rows(P.matrix)
    print(io, "$(P.coeffs[i]) with row vector $(sub(P.matrix, i:i, 1:cols(P.matrix)))\n")
  end
end

function PseudoMatrix(m::GenMat{nf_elem}, c::Array{NfMaxOrdFracIdl, 1})
  # sanity checks
  return PMat(m ,c)
end


function PseudoMatrix(m::GenMat{NfOrdElem{NfMaxOrd}}, c::Array{NfMaxOrdIdl, 1})
  mm = change_ring(m, nf(base_ring(m)))
  cc = map(z -> NfMaxOrdFracIdl(z, fmpz(1)), c)
  return PMat(mm, cc)
end

function rows(m::PMat)
  return rows(m.matrix)
end

function cols(m::PMat)
  return cols(m.matrix)
end

function change_ring(m::GenMat{NfOrdElem{NfMaxOrd}}, K::AnticNumberField)
  return MatrixSpace(K, rows(m), cols(m))(map(z -> K(z), m.entries))
end

function det(m::PMat)
  z = m.coeffs[1]
  for i in 2:rows(m)
    if isdefined(z.num, :gen_two) && isdefined(m.coeffs[i].num, :gen_two)
    end
    z = z*m.coeffs[i]
  end
  return det(m.matrix)*z
end

# this is slow
function _coprime_integral_ideal_class(x::NfMaxOrdFracIdl, y::NfMaxOrdIdl)
  O = order(y)
  c = conjugates_init(nf(O).pol)
  #num_x_inv = inv(num(x))
  x_inv = inv(x)
  check = true
  z = ideal(O, O(1))
  a = nf(O)()
  i = 0
  while check
    i += 1
    a = rand(x_inv, 10)
    b = x*a
    z = divexact(num(b), den(b))
    norm(z + y) == 1 ? (check = false) : (check = true)
  end
  return z, a 
end

# this is slow
function _coprime_norm_integral_ideal_class(x::NfMaxOrdFracIdl, y::NfMaxOrdIdl)
  O = order(y)
  c = conjugates_init(nf(O).pol)
  #num_x_inv = inv(num(x))
  x_inv = inv(x)
  check = true
  z = ideal(O, O(1))
  a = nf(O)()
  i = 0
  while check
    i += 1
    a = rand(x_inv, 10)
    b = x*a
    z = divexact(num(b), den(b))
    gcd(norm(z), norm(y)) == 1 ? (check = false) : (check = true)
  end
  @assert gcd(norm(z), norm(y)) == 1
  return z, a 
end

function rand(I::NfMaxOrdIdl, B::Int)
  r = rand(1:B, degree(order(I)))
  b = basis(I)
  z = r[1]*b[1]
  for i in 2:degree(order(I))
    z = z + r[i]*b[i]
  end
  return z
end

function rand(I::NfMaxOrdFracIdl, B::Int)
  z = rand(num(I), B)
  return divexact(elem_in_nf(z), den(I))
end

function pseudo_hnf(P::PMat, m::NfMaxOrdIdl, shape::Symbol = :upperright)
  O = order(m)

  t_comp_red = 0.0
  t_mod_comp = 0.0
  t_sum = 0.0
  t_div = 0.0
  t_idem = 0.0
  
  t_comp_red += @elapsed z = _matrix_for_reduced_span(P, m)
  t_mod_comp += @elapsed zz = strong_echelon_form(z, shape)

  res_mat = MatrixSpace(nf(O), rows(P), cols(P))()
  for i in 1:rows(P)
    for j in 1:cols(P)
      res_mat[i, j] = elem_in_nf(zz[i, j].elem)
    end
  end

  res = PMat(res_mat, [ deepcopy(x)::NfMaxOrdFracIdl for x in P.coeffs])

  for i in 1:rows(P)
    if iszero(zz[i, i].elem)
      res.matrix[i, i] = one(nf(O))
      res.coeffs[i] = NfMaxOrdFracIdl(deepcopy(m), fmpz(1))
    else
      o = ideal(O, zz[i, i].elem)
      t_sum += @elapsed g = o + m
      t_div += @elapsed oo = divexact(o, g)
      t_div += @elapsed mm = divexact(m, g)
      t_idem += @elapsed e, f = idempotents(oo, mm)
      res.coeffs[i] = NfMaxOrdFracIdl(deepcopy(g), fmpz(1))
      mul_row!(res.matrix, i, elem_in_nf(e))
      divide_row!(res.matrix, i, elem_in_nf(zz[i, i].elem))
      res.matrix[i, i] = one(nf(O))
    end
  end

  #println("computation of reduction : $t_comp_red")
  #println("modular computation      : $t_mod_comp")
  #println("computation of ideal sum : $t_sum")
  #println("computation of ideal div : $t_div")
  #println("computation of idems     : $t_idem")

  return res
end

#this is Algorithm 4 of FH2014
# we assume that span(P) \subseteq O^r
function _matrix_for_reduced_span(P::PMat, m::NfMaxOrdIdl)
  O = order(m)
  c = Array{NfMaxOrdIdl}(rows(P))
  mat = deepcopy(P.matrix)
  for i in 1:rows(P)
    I, a = _coprime_norm_integral_ideal_class(P.coeffs[i], m)
    divide_row!(mat, i, a)
    c[i] = I
  end
  Om, OtoOm = quo(O, m)
  z = MatrixSpace(Om, rows(P), cols(P))()
  for i in 1:rows(z)
    for j in 1:cols(z)
      @assert norm(c[i])*mat[i, j] in O
      @assert euclid(OtoOm(O(norm(c[i])))) == 1
      q = OtoOm(O(norm(c[i])*mat[i,j]))
      qq = inv(OtoOm(O(norm(c[i]))))
      z[i, j] = q*qq
    end
  end
  return z
end

_check(a) = a.has_coord ? dot(a.elem_in_basis, basis(parent(a))) == a : true

function _check(m::GenMat{NfOrdElem{NfMaxOrd}})
  for i in 1:rows(m)
    for j in 1:cols(m)
      if !_check(m[i, j].elem)
        println("$i $j not consistent: $(m[i, j]) : $(m[i, j].elem_in_basis)")
        error("dasdsad")
      end
    end
  end
end

function _check(m::GenMat{NfMaxOrdQuoRingElem})
  for i in 1:rows(m)
    for j in 1:cols(m)
      if !_check(m[i, j].elem)
        println("$i $j not consistent: $(m[i, j].elem) : $(m[i, j].elem.elem_in_basis)")
        error("dasdsad")
      end
    end
  end
end

function divide_row!{T}(M::GenMat{T}, i::Int, r::T)
  for j in 1:cols(M)
    M[i, j] = divexact(M[i, j], r)
  end
end

function mul_row!{T}(M::GenMat{T}, i::Int, r::T)
  for j in 1:cols(M)
    M[i, j] = M[i, j] * r
  end
end

function _contained_in_span_of_pseudohnf(v::GenMat{nf_elem}, P::PMat)
  # assumes that P is upper right pseudo-HNF
  w = deepcopy(v)
  for i in 1:rows(P)
    if !(w[1, i] in P.coeffs[i])
      return false
    end
    e = w[1, i]
    for j in 1:cols(P)
      w[1, j] = w[1, j] - e*P.matrix[i, j]
    end
  end
  if !iszero(w)
    return false
  end
  return true
end

function _contained_in_span_of_pseudohnf_lowerleft(v::GenMat{nf_elem}, P::PMat)
  # assumes that P is lowerleft pseudo-HNF
  w = deepcopy(v)
  for i in rows(P):-1:1
    if !(w[1, i] in P.coeffs[i])
      return false
    end
    e = w[1, i]
    for j in 1:cols(P)
      w[1, j] = w[1, j] - e*P.matrix[i, j]
    end
  end
  if !iszero(w)
    return false
  end
  return true
end

function _spans_subset_of_pseudohnf(M::PMat, P::PMat)
# P upperright
  for i in rows(M)
    A = M.coeffs[i]
    v = sub(M.matrix, i:i, 1:cols(P))
    for b in basis(A.num)
      bb = divexact(elem_in_nf(b), A.den)
      if !Hecke._contained_in_span_of_pseudohnf(bb*v, P)
        return false
      end
    end
  end
  return true
end

function sub(M::GenMat, rows::UnitRange{Int}, cols::UnitRange{Int})
  @assert step(rows) == 1 && step(cols) == 1
  z = MatrixSpace(base_ring(M), length(rows), length(cols))()
  for i in rows
    for j in cols
      z[i - start(rows) + 1, j - start(cols) + 1] = M[i, j]
    end
  end
  return z
end

function in(x::nf_elem, y::NfMaxOrdFracIdl)
  B = inv(basis_mat(y))
  O = order(y)
  M = MatrixSpace(FlintZZ, 1, degree(O))()
  t = FakeFmpqMat(M)
  elem_to_mat_row!(t.num, 1, t.den, x)
  v = t*basis_mat_inv(O)
  v = v*B

  return v.den == 1
end

pseudo_matrix(x...) = PseudoMatrix(x...)
