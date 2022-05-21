################################################################################
#
# NfOrd/FacElem.jl : Factored elements over number fields
#
# This file is part of hecke.
#
# Copyright (c) 2015: Claus Fieker, Tommy Hofmann
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
#  Copyright (C) 2015, 2016 Tommy Hofmann
#
################################################################################

# Get FacElem from ClassGrpCtx
function FacElem(x::ClassGrpCtx, y::fmpz_mat, j::Int)
  return FacElem(x.R, [ deepcopy(y[j, i]) for i in 1:ncols(y) ])
end

function FacElem(x::ClassGrpCtx, y::Vector{fmpz})
  return FacElem(x.R, [ deepcopy(y[i]) for i in 1:length(y) ])
end

# Get the trivial factored element from an ordinary element
function FacElem(x::T) where {T <: NumFieldElem}
  z = FacElem{T, parent_type(T)}()
  z.fac[x] = fmpz(1)
  z.parent = FacElemMon(parent(x)::parent_type(T))::FacElemMon{parent_type(T)}
  return z
end

function is_torsion_unit(x::FacElem{T}, checkisunit::Bool = false, p::Int = 16) where T
  @vprint :UnitGroup 2 "Checking if factored element is torsion\n"

  if checkisunit
    _isunit(x) ? nothing : return false, p
  end

  K = base_ring(x)
  d = degree(K)
  r, s = signature(K)

  @vprint :UnitGroup 2 "Precision is now $(p) \n"
  l = 0
  @vprint :UnitGroup 2 "Computing conjugates ... \n"
  @v_do :UnitGroup 2 pushindent()
  A = ArbField(p, cached = false)
  B = log(A(1) + A(1)//A(6) * log(A(d))//A(d^2))
  p = Int(upper_bound(fmpz, -log(B)/log(A(2)))) + 2

  cx = conjugates_arb_log(x, p) #this guarantees the result with an abs. error
                                # of 2^-p
  @v_do :UnitGroup 2 popindent()
  @vprint :UnitGroup 2 "Conjugates log are $cx\n"
  for i in 1:r
    k = abs(cx[i])
    if is_positive(k)
      return false, p
    elseif is_nonnegative(B - k)
      l = l + 1
    else
      println("fail 1")
    end
  end
  for i in 1:s
    k = cx[r + i]//2
    if is_positive(k)
      return false, p
    elseif is_nonnegative(B - k)
      l = l + 1
    else
      println("fail 2")
    end
  end

  if l == r + s
    return true, p
  end
  error("precision was not sufficient")
end

function factored_norm(x::FacElem{nf_elem, AnticNumberField})
  b = fmpq[]
  c = fmpz[]
  for (a, e) in x.fac
    if iszero(e)
      continue
    end
    n = norm(a)
    d = numerator(n)
    if !isone(d)
      push!(b, d)
      push!(c, e)
    end
    d = denominator(n)
    if !isone(d)
      push!(b, d)
      push!(c, -e)
    end
  end
  if length(b) == 0
    push!(b, fmpq(1))
    push!(c, 0)
  end
  f = FacElem(b, c)
  simplify!(f)
  return f
end

function norm(x::FacElem{nf_elem})
  return evaluate(factored_norm(x))
end

_base_ring(x::nf_elem) = parent(x)::AnticNumberField

_base_ring(x::FacElem{nf_elem}) = base_ring(x)::AnticNumberField

*(x::FacElem{nf_elem}, y::NfOrdElem) = x*elem_in_nf(y)

*(x::NfOrdElem, y::FacElem{nf_elem}) = y*x

function _conjugates_arb_log(A::FacElemMon{AnticNumberField}, a::nf_elem, abs_tol::Int)
  abs_tol = 1<<nbits(abs_tol)
  if haskey(A.conj_log_cache, abs_tol)
    if haskey(A.conj_log_cache[abs_tol], a)
      return A.conj_log_cache[abs_tol][a]::Vector{arb}
    else
      z = conjugates_arb_log(a, abs_tol)
      A.conj_log_cache[abs_tol][a] = z
      return z::Vector{arb}
    end
  else
    A.conj_log_cache[abs_tol] = Dict{nf_elem, arb}()
    z = conjugates_arb_log(a, abs_tol)
    A.conj_log_cache[abs_tol][a] = z
    return z::Vector{arb}
  end
end

function conjugates_arb(x::FacElem{nf_elem, AnticNumberField}, abs_tol::Int)
  d = degree(_base_ring(x))
  res = Array{acb}(undef, d)

  first = true

  for (a, e) in x.fac
    if iszero(e)
      continue
    end
    z = conjugates_arb(a, abs_tol)
    if first
      for j in 1:d
        res[j] = z[j]^e
      end
      first = false
    else
      for j in 1:d
        res[j] = res[j] * z[j]^e
      end
    end
  end
  return res
end

function conjugates_arb_log(x::FacElem{nf_elem, AnticNumberField}, abs_tol::Int)
  K = _base_ring(x)
  r1, r2 = signature(K)
  d = r1 + r2
  res = Array{arb}(undef, d)

  if isempty(x.fac) || all(x -> iszero(x), values(x.fac))
    x.fac[one(K)] = fmpz(1)
  end


  target_tol = abs_tol
  pr = abs_tol + nbits(maximum(abs, values(x.fac))) + nbits(length(x.fac))

  while true
    prec_too_low = false
    first = true
    for (a, e) in x.fac
      if iszero(e)
        continue
      end
      z = _conjugates_arb_log(parent(x), a, pr)
      if first
        for j in 1:d
          res[j] = parent(z[j])()::arb
          muleq!(res[j], z[j], e)
          if !radiuslttwopower(res[j], -target_tol) || !isfinite(res[j])
            prec_too_low = true
            break
          end
          #res[j] = x.fac[a] * z[j]
        end
        first = false
      else
        for j in 1:d
          addmul!(res[j], z[j], e)
          #res[j] = res[j] + x.fac[a]*z[j]
          if !radiuslttwopower(res[j], -target_tol) || !isfinite(res[j])
            prec_too_low = true
            break
          end
        end
      end
      if prec_too_low
        break
      end
    end
    if prec_too_low
      pr *= 2
      continue
    end

    for j in 1:d
      expand!(res[j], -target_tol)
    end
    return res
  end
end

function conjugates_arb_log(x::FacElem{nf_elem, AnticNumberField}, R::ArbField)
  z = conjugates_arb_log(x, -R.prec)
  return map(R, z)
end

@doc Markdown.doc"""
    valuation(a::FacElem{nf_elem, AnticNumberField}, P::NfOrdIdl) -> fmpz

The valuation of $a$ at $P$.
"""
function valuation(a::FacElem{nf_elem, AnticNumberField}, P::NfOrdIdl)
  val = fmpz(0)
  for (a, e) = a.fac
    if !iszero(e)
      val += valuation(a, P)*e
    end
  end
  return val
end

#the normalise bit ensures that the "log" vector lies in the same vector space
#well, the same hyper-plane, as the units
@doc Markdown.doc"""
    conjugates_arb_log_normalise(x::nf_elem, p::Int = 10)
    conjugates_arb_log_normalise(x::FacElem{nf_elem, AnticNumberField}, p::Int = 10)

The "normalised" logarithms, i.e. the array $c_i\log |x^{(i)}| - 1/n\log|N(x)|$,
so the (weighted) sum adds up to zero.
"""
function conjugates_arb_log_normalise(x::nf_elem, p::Int = 10)
  K = parent(x)
  r,s = signature(K)
  c = conjugates_arb_log(x, p)
  n = sum(c)//degree(K)
  for i=1:r
    c[i] -= n
  end
  for i=r+1:r+s
    c[i] -= n
    c[i] -= n
  end
  return c
end

#the normalise bit ensures that the "log" vector lies in the same vector space
#well, the same hyper-plane, as the units
function conjugates_arb_log_normalise(x::FacElem{nf_elem, AnticNumberField}, p::Int = 10)
  K = base_ring(x)
  r,s = signature(K)
  c = conjugates_arb_log(x, p)
  n = sum(c)//degree(K)
  for i=1:r
    c[i] -= n
  end
  for i=r+1:r+s
    c[i] -= n
    c[i] -= n
  end
  return c
end

function _conj_arb_log_matrix_normalise_cutoff(u::Vector{T}, prec::Int = 32)::arb_mat where T
  z = conjugates_arb_log_normalise(u[1], prec)
  A = zero_matrix(parent(z[1]), length(u), length(z)-1)
  for i=1:length(z)-1
    A[1,i] = z[i]
  end

  for j=2:length(u)
    z = conjugates_arb_log_normalise(u[j], prec)
    for i=1:length(z)-1
      A[j,i] = z[i]
    end
  end
  return A
end

#used (hopefully) only inside the class group
function FacElem(A::Vector{nf_elem_or_fac_elem}, v::Vector{fmpz})
  local B::FacElem{nf_elem, AnticNumberField}
  if typeof(A[1]) == nf_elem
    B = FacElem(A[1]::nf_elem)
  else
    B = A[1]::FacElem{nf_elem, AnticNumberField}
  end
  B = B^v[1]
  for i=2:length(A)
    if iszero(v[i])
      continue
    end
    if typeof(A[i]) == nf_elem
      local t::nf_elem = A[i]::nf_elem
      add_to_key!(B.fac, t, v[i])
    else
      local s::FacElem{nf_elem, AnticNumberField} = A[i]::FacElem{nf_elem, AnticNumberField}
      for (k, v1) in s
        if iszero(v1)
          continue
        end
        add_to_key!(B.fac, k, v1*v[i])
      end
    end
  end
  return B::FacElem{nf_elem, AnticNumberField}
end

################################################################################
#
#  Coprime factorization of the support of a factored element
#
################################################################################

function _get_support(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet)
  Zk = order(I)
  A = Tuple{NfOrdIdl, fmpz}[]
  sizehint!(A, length(a.fac))
  i = 0
  for (e, v) = a.fac
    if iszero(v)
      continue
    end
    i += 1
    @vprint :CompactPresentation 3 "Element $i / $(length(a.fac))"
    if isinteger(e)
      Id1 = ideal(Zk, FlintZZ(e))
      push!(A, (Id1, v))
      continue
    end
    if e in Zk
      N = ideal(Zk, Zk(e, false))
      push!(A, (N, v))
      continue
    end
    Id = ideal(Zk, e)
    N, D = integral_split(Id)
    if !isone(N)
      push!(A, (N, v))
      #add_to_key!(A, N, v)
    end
    if !isone(D)
      push!(A, (D, -v))
      #add_to_key!(A, D, -v)
    end
    @vprint :CompactPresentation 3 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
  end
  @vprint :CompactPresentation 3 "\n"
  return A
end
@doc Markdown.doc"""
    factor_coprime(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}

Factors the rincipal ideal generated by $a$ into coprimes by computing a coprime
basis from the principal ideals in the factorisation of $a$.
"""
function factor_coprime(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet; refine::Bool = false)
  Zk = order(I)
  @assert nf(Zk) == base_ring(a)
  A = _get_support(a, I)
  if isempty(A)
    return Dict{NfOrdIdl, fmpz}(ideal(Zk, 1) => 1)
  end
  base = NfOrdIdl[y for (y, v) in A if !iszero(v)]
  cp = coprime_base(base, refine = refine)
  ev = Dict{NfOrdIdl, fmpz}()
  if isempty(cp)
    return Dict{NfOrdIdl, fmpz}(ideal(Zk, 1) => 1)
  end
  for p in cp
    if isone(p)
      continue
    end
    P = minimum(p)
    @vprint :CompactPresentation 3 "Computing valuation at an ideal lying over $P"
    assure_2_normal(p)
    v = fmpz(0)
    for (b, e) in A
      if iszero(e)
        continue
      end
      if divisible(norm(b, copy = false), P)
        v += valuation(b, p)*e
      end
    end
    @vprint :CompactPresentation 3 "$(Hecke.set_cursor_col())$(Hecke.clear_to_eol())"
    if !iszero(v)
      ev[p] = v
    end
  end
  if isempty(ev)
    ev[ideal(Zk, 1)] = 1
  end
  return ev
end

@doc Markdown.doc"""
    factor(a::nf_elem, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}

Factors the principal ideal generated by $a$.
"""
function factor(a::nf_elem, I::NfOrdIdlSet)
  return factor(ideal(order(I),  a))
end

@doc Markdown.doc"""
    factor(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet) -> Dict{NfOrdIdl, fmpz}

Factors the principal ideal generated by $a$ by refinind a coprime factorisation.
"""
function factor(a::FacElem{nf_elem, AnticNumberField}, I::NfOrdIdlSet)
  cp = factor_coprime(a, I, refine = true)
  f = Dict{NfOrdIdl, fmpz}()
  for (I, v) = cp
    lp = factor(I)
    for (p, e) = lp
      f[p] = e*v
    end
  end
  return f
end
