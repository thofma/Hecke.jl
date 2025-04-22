const default_class_mod_pol_db = joinpath(artifact"ClassicalModularPolynomialsDB", "ClassicalModularPolynomialsDB", "data")

const _classical_modular_polynomial_cache = Dict{Any, Any}()

@doc raw"""
    classical_modular_polynomial([R::MPolyRing,] n::Int) -> Poly

Returns the classical modular polynomial of level $n as an element of
$\mathbf{Z}[x, y]$. If an optional bivariate polynomial $R$ is specified,
the polynomial will be evaluated at the variables of $R$.

Modular polynomials are available up to level `59`.
"""
classical_modular_polynomial

function classical_modular_polynomial(n::Int)
  return classical_modular_polynomial(Globals.Zxy, n)
end

function classical_modular_polynomial(R::MPolyRing, n::Int)
  @req 1 <= n <= 59 "Database only contains classical modular polynomials up to level 59"
  get!(_classical_modular_polynomial_cache, (R, n)) do
    open(joinpath(default_class_mod_pol_db, "$n")) do io
      b, exps = _parse(Vector{Vector{Int}}, io)
      @assert Char(b) == ','
      b, coeffs = _parse(Vector{ZZRingElem}, io)
      C = MPolyBuildCtx(R)
      for i in 1:length(exps)
        push_term!(C, base_ring(R)(coeffs[i]), exps[i])
        if exps[i][1] != exps[i][2]
          push_term!(C, base_ring(R)(coeffs[i]), reverse(exps[i]))
        end
      end
      return finish(C)
    end
  end::elem_type(R)
end

const default_atkin_mod_pol_db = joinpath(artifact"AtkinModularPolynomialsDB", "AtkinModularPolynomialsDB", "data")

const _atkin_modular_polynomial_cache = Dict{Any, Any}()

@doc raw"""
    atkin_modular_polynomial([R::MPolyRing,] n::Int) -> Poly

Returns the Atkin modular polynomial of prime level $n as an element of
$\mathbf{Z}[x, y]$. If an optional bivariate polynomial $R$ is specified,
the polynomial will be evaluated at the variables of $R$.

Atkin modular polynomials are available up to level `400`.
"""
atkin_modular_polynomial

function atkin_modular_polynomial(n::Int)
  return atkin_modular_polynomial(Globals.Zxy, n)
end

function atkin_modular_polynomial(R::MPolyRing, n::Int)
  @req is_prime(n) "Level ($n) must be prime"
  @req 1 <= n <= 400 "Database only contains Atkin modular polynomials up to level 400"
  get!(_atkin_modular_polynomial_cache, (R, n)) do
    open(joinpath(default_atkin_mod_pol_db, "$n")) do io
      b, m = _parse(Int, io)
      @assert n == m
      @assert Char(b) == ','
      b, exps = _parse(Vector{Vector{Int}}, io)
      @assert Char(b) == ','
      b, coeffs = _parse(Vector{ZZRingElem}, io)
      C = MPolyBuildCtx(R)
      for i in 1:length(exps)
        push_term!(C, base_ring(R)(coeffs[i]), exps[i])
      end
      return finish(C)
    end
  end::elem_type(R)
end
