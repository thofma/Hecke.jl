#fin. gen. submodules of Z^n and F_p^n (and possibly more)
import Base.show, Base.reduce, Base.inv, Nemo.inv, Base.solve, Hecke.solve,
       Hecke.lift, Hecke.rational_reconstruction

type ModuleCtx_UIntMod
  R::ZZModUInt
  basis::Smat{UIntMod}
  gens::Smat{UIntMod}
  function ModuleCtx_UIntMod()
    return new()
  end
  function ModuleCtx_UIntMod(p::Int, dim::Int)
    M = new()
    M.R = ZZModUInt(UInt(p))
    M.basis = Smat{UIntMod}()
    M.basis.c = dim
    M.gens = Smat{UIntMod}()
    return M
  end
end

type ModuleCtx_fmpz
  basis::Smat{fmpz}
  bas_gens::Smat{fmpz}
  rel_gens::Smat{fmpz}
  Mp::ModuleCtx_UIntMod
  function ModuleCtx_fmpz(dim::Int)
    M = new()
    M.basis = Smat{fmpz}()
    M.basis.c = dim
    M.bas_gens = Smat{fmpz}()
    M.rel_gens = Smat{fmpz}()
    M.Mp = ModuleCtx_UIntMod(13, dim)
    return M
  end
end

function show(io::IO, M::ModuleCtx_UIntMod)
  println("Module over $(M.R) of (current) rank $(rows(M.basis)) and $(rows(M.gens))")
end
function show(io::IO, M::ModuleCtx_fmpz)
  println("Module over FlintZZ of (current) rank $(rows(M.basis)) and further $(rows(M.rel_gens))")
end

function reduce(A::Smat{UIntMod}, g::SmatRow{UIntMod})
  #assumes A is upper triangular, reduces g modulo A
  # supposed to be a field...
  if A.r == A.c
    return SmatRow{UIntMod}()
  end
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      break
    end
    @assert A.rows[j].pos[1] == g.pos[1]
    @assert (A.rows[j].values[1]) == 1
    p = g.values[1]
    g = Hecke.add_scaled_row(A[j], g, -p)
    @assert length(g)==0 || g.pos[1] > A[j].pos[1]
  end
  if length(g) > 0
    li = inv(g.values[1])
    for i=1:length(g)
      g.values[i] *= li
    end
  end
  return g
end

function inv(x::UIntMod)
  return 1//x
end

#returns true if g enlarged M
function add_gen!(M::ModuleCtx_UIntMod, g::SmatRow{UIntMod})
  if M.basis.r == M.basis.c
    return false
  end
  h = reduce(M.basis, g)
  if !iszero(h)
    i = 1
    while i<= rows(M.basis) && M.basis.rows[i].pos[1] < h.pos[1]
      i += 1
    end
    @assert i > rows(M.basis) || M.basis[i].pos[1] > h.pos[1]
    insert!(M.basis.rows, i, h)
    M.basis.r += 1
    M.basis.nnz += length(h)
    M.basis.c = max(M.basis.c, h.pos[end])
    push!(M.gens, g)
    return true
  end
  return false 
end

function reduce(A::Smat{fmpz}, g::SmatRow{fmpz})
  #assumes A is upper triangular, reduces g modulo A
  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      if g.values[1] < 0
        for i=1:length(g.values)
          g.values[i] *= -1
        end
      end
      return g
    end
    h = typeof(g)()
    st_g = 2
    st_A = 2
    p = g.values[1]
    if divides(p, A.rows[j].values[1])[1]
      g = Hecke.add_scaled_row(A[j], g, - divexact(p, A.rows[j].values[1]))
      @assert length(g)==0 || g.pos[1] > A[j].pos[1]
    else
      x, a, b = gcdx(A.rows[j].values[1], p)
      @assert x > 0
      c = -div(p, x)
      d = div(A.rows[j].values[1], x)
      A[j], g = Hecke.transform_row(A[j], g, a, b, c, d)
      @assert A[j].values[1] == x
      @assert length(g)==0 || g.pos[1] > A[j].pos[1]
    end
  end
  if g.values[1] < 0
    for i=1:length(g.values)
      g.values[i] *= -1
    end
  end
  return g
end

function add_gen!(M::ModuleCtx_fmpz, g::SmatRow{fmpz})
  gp = mod(g, 13)
  if add_gen!(M.Mp, gp)
#    push!(M.basis, g)
#    return true
    h = reduce(M.basis, g)
    @assert !iszero(h)
    i = 1
    while i<= rows(M.basis) && M.basis.rows[i].pos[1] < h.pos[1]
      i += 1
    end
    @assert i > rows(M.basis) || M.basis[i].pos[1] > h.pos[1]
    insert!(M.basis.rows, i, h)
    M.basis.r += 1
    M.basis.nnz += length(h)
    M.basis.c = max(M.basis.c, h.pos[end])
    push!(M.bas_gens, g)
    return true
  else
    push!(M.rel_gens, g)
  end
  return false 
end

function check_index(M::ModuleCtx_fmpz)
  if rows(M.Mp.basis) < cols(M.Mp.basis)
    return fmpz(0)
  end

  C = copy(M.basis)
  for i=1:5
    push!(C, Hecke.randrow(M.rel_gens))
    for j=1:5
      C[end] = Hecke.add_scaled_row(C[end], Hecke.randrow(M.rel_gens), fmpz(rand(1:10)))
    end
  end
  Hecke.upper_triangular(C)
  return prod([C[i,i] for i=1:rows(C)])
end


function solve(A::Smat{UIntMod}, g::SmatRow{UIntMod})
  @assert cols(A) == rows(A)
  # assumes A is upper triangular, reduces g modulo A to zero and collects
  # the tansformation
  # supposed to be a field...

  sol = typeof(g)()

  while length(g)>0
    s = g.pos[1]
    j = 1
    while j<= rows(A) && A.rows[j].pos[1] < s
      j += 1
    end  
    if j > rows(A) || A.rows[j].pos[1] > s
      break
    end
    @assert A.rows[j].pos[1] == g.pos[1]
    p = g.values[1]//A.rows[j].values[1]
    push!(sol.pos, j)
    push!(sol.values, p)
    g = Hecke.add_scaled_row(A[j], g, -p)
    @assert length(g)==0 || g.pos[1] > A[j].pos[1]
  end
  if length(g) > 0
    li = inv(g.values[1])
    for i=1:length(g)
      g.values[i] *= li
    end
  end
  return sol
end

function lift(a::SmatRow{UIntMod})
  b = SmatRow{fmpz}()
  for (p,v) = a
    push!(b.pos, p)
    push!(b.values, fmpz(v.m))
  end
  return b
end

#TODO: write vector reconstruction and use it here.
function rational_reconstruction(A::SmatRow{fmpz}, M::fmpz)
  B = SmatRow{fmpz}()
  de = fmpz(1)
  for (p,v) = A
    fl, n, d = rational_reconstruction(v, M)
    if !fl
      return false, B, de
    end
    if de % d == 0
      push!(B.pos, p)
      push!(B.values, n*(div(de, d)))
    else
      l = lcm(d, de)
      B = div(l, de) * B
      push!(B.pos, p)
      push!(B.values, div(l, d)*n)
      de = l
    end
  end
  return true, B, de
end
   
function dixon_solve(A::Smat{fmpz}, b::SmatRow{fmpz})
  #assumes A to be upper triangular of full rank - for now at least

  p = next_prime(2^20)
  b_orig = b

  Ap = mod(A, p)
  bp = mod(b, p)

  sol = SmatRow{fmpz}()

  pp = fmpz(1)

  last = (sol, 1)
  while true
    zp = solve(Ap, bp)
#    @assert Hecke.mul(zp, Ap) == bp

    z = lift(zp)
#    @assert mod(z, p) == zp

    sol += pp*z

    pp *= fmpz(p)

#    @assert iszero(mod(b_orig - Hecke.mul(sol, A), pp)) 

    fl, nu, de = rational_reconstruction(sol, pp)
    if fl 
#      @assert mod(de*sol, pp) == mod(nu, pp)
#      @assert mod(mul(nu, A), pp) == mod(de*b_orig, pp)
      if last == (nu, de)
        if Hecke.mul(nu, A) == de*b_orig
          return nu, de
        end
        println("bad")
      else
        last = (nu, de)
      end
    end

#    @assert mod(Hecke.mul(z, A), p) == bp
    b = b - Hecke.mul(z, A)

    for i=1:length(b.values)
#      @assert b.values[i] % p == 0
      b.values[i] = div(b.values[i], p)
    end
    bp = mod(b, p)
    if nbits(pp) > 200 
      return (false, nu, de, sol, pp)
    end  
  end
end

