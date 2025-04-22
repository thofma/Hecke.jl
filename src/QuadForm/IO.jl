################################################################################
#
#  Conversion to parseble Hecke code
#
################################################################################

# This is helpful to construct code for the tests.
function to_hecke(L::AbstractLat; target = "L", skip_field = false)
  return to_hecke(stdout, L, target = target, skip_field = skip_field)
end

function to_hecke(G::HermGenus; target = "G")
  return to_hecke(stdout, G, target=target)
end

function to_hecke_string(L::AbstractLat; target = "L", skip_field = false)
  b = IOBuffer()
  to_hecke(b, L, target = target, skip_field = skip_field)
  return String(take!(b))
end

function to_hecke(io::IO, L::QuadLat; target = "L", skip_field = false)
  K = nf(base_ring(L))
  if !skip_field
    println(io, "Qx, x = polynomial_ring(QQ, :x, cached = false)")
    f = absolute_minpoly(gen(K))
    pol = string(f)
    pol = replace(pol, string(var(parent(f))) => "x")
    println(io, "f = ", pol, ";")
    println(io, "K, a = number_field(f, :a, cached = false)")
  end
  F = gram_matrix(ambient_space(L))
  Fst = "[" * split(string([F[i, j] for i in 1:nrows(F) for j in 1:ncols(F)]), '[')[2]
  Fst = replace(Fst, string(var(K)) => "a")
  println(io, "D = matrix(K, ", nrows(F), ", ", ncols(F), ", ", Fst, ");")
  gens = generators(L)
  Gs = "Vector{$(elem_type(K))}["
  for i in 1:length(gens)
    g = gens[i]
    Gs = Gs * "map(K, [" * split(string(g), "[")[2] * ")"
    Gs = replace(Gs, string(var(K)) => "a")
    if i < length(gens)
      Gs = Gs * ", "
    end
  end
  Gs = Gs * "]"
  println(io, "gens = ", Gs)
  println(io, target, " = quadratic_lattice(K, gens, gram = D)")
end

function to_hecke(io::IO, L::HermLat; target = "L", skip_field = false)
  E = nf(base_ring(L))
  K = base_field(E)
  println(io, "Qx, x = polynomial_ring(QQ, :x)")
  f = defining_polynomial(K)
  pol = replace(string(f), string(var(parent(f))) => "x")
  println(io, "f = ", pol)
  println(io, "K, a = number_field(f, :a, cached = false)")
  println(io, "Kt, t = polynomial_ring(K, :t)")
  f = defining_polynomial(E)
# FIXME: the following will be wrong if `var(K) == :t`  or `var(K) == var(parent(f))`
  pol = replace(string(f), string(var(parent(f))) => "t")
  pol = replace(pol, string(var(K)) => "a")
  println(io, "g = ", pol, "")
  println(io, "E, b = number_field(g, :b, cached = false)")
  F = gram_matrix(ambient_space(L))
  Fst = "[" * split(string([F[i, j] for i in 1:nrows(F) for j in 1:ncols(F)]), '[')[2]
  Fst = replace(Fst, string(var(K)) => "a")
  Fst = replace(Fst, string(var(E)) => "b")
  println(io, "D = matrix(E, ", nrows(F), ", ", ncols(F), ", ", Fst, ")")

  gens = generators(L)
  Gs = "Vector{$(elem_type(E))}["
  for i in 1:length(gens)
    g = gens[i]
    gst = replace(string(g), string(var(K)) => "a")
    gst = replace(gst, string(var(E)) => "b")

    Gs = Gs * "map(E, [" * split(gst, "[")[2] * ")"
    if i < length(gens)
      Gs = Gs * ", "
    end
  end
  Gs = Gs * "]"
  println(io, "gens = ", Gs)

  println(io, target, " = hermitian_lattice(E, gens, gram = D)")
end

function to_hecke(io::IO, G::HermGenus; target = "G")
  E = base_field(G)
  K = base_field(E)
  println(io, "Qx, x = polynomial_ring(QQ, :x)")
  f = defining_polynomial(K)
  pol = replace(string(f), string(var(parent(f))) => "x")
  println(io, "f = ", pol)
  println(io, "K, a = number_field(f, :a, cached = false)")
  println(io, "Kt, t = polynomial_ring(K, :t)")
  f = defining_polynomial(E)
  pol = replace(string(f), string(var(parent(f))) => "t")
  pol = replace(pol, string(var(K)) => "a")
  println(io, "g = ", pol, "")
  println(io, "E, b = number_field(g, :b, cached = false);")
  sig = signatures(G)
  SE = collect(keys(sig))
  sort!(SE, lt=(p,q) -> isless(real(embedding(p).r), real(embedding(q).r)))
  println(io, "S = unique([restrict(r, K) for r in filter(!is_real, infinite_places(E)) if is_real(restrict(r, K))]);")
  println(io, "sort!(S, lt=(p,q) -> isless(real(embedding(p).r), real(embedding(q).r)));")
  vals = [sig[p] for p in SE]
  println(io, "vals = Int$(vals);")
  println(io, "sig = Dict(S[i] => vals[i] for i in 1:$(length(vals)));")
  println(io, "OK = MaximalOrder(K);")
  lgs = G.LGS
  pp = prime.(lgs)
  bases = [gens(p) for p in pp]
  str = "ps = $(typeof(pp[1]))[ideal(OK, v) for v in Vector{$(elem_type(maximal_order(K)))}["
  for bb in bases
    bb = replace("$(bb)", string(var(K)) => "a")
    bb = bb[10:end]
    str *= "map(OK, "*bb*"), "
  end
  str = str[1:end-2]*"]];"
  println(io, str)
  println(io, "datas = $([G[p].data for p in pp]);")
  println(io, "lgs = HermLocalGenus{typeof(E), $(typeof(pp[1]))}[genus(HermLat, E, ps[i], datas[i]) for i in 1:$(length(pp))];")
  println(io, target, " = HermGenus(E, $(rank(G)), lgs, sig)")
end

################################################################################
#
#  Conversion to Magma
#
################################################################################

function to_magma(L::AbstractLat; target = "L")
  return to_magma(stdout, L, target = target)
end

function to_magma_string(L::AbstractLat; target = "L")
  b = IOBuffer()
  to_magma(b, L, target = target)
  return String(take!(b))
end

function to_magma(io::IO, L::HermLat; target = "L")
  E = nf(base_ring(L))
  K = base_field(E)
  println(io, "Qx<x> := PolynomialRing(Rationals());")
  f = defining_polynomial(K)
  pol = replace(string(f), "//" => "/")
  pol = replace(pol, string(var(parent(f))) => "x")
  println(io, "f := ", pol, ";")
  println(io, "K<a> := NumberField(f : DoLinearExtension);")
  println(io, "Kt<t> := PolynomialRing(K);")
  f = defining_polynomial(E)
  pol = replace(string(f), string(var(parent(f))) => "t")
  pol = replace(pol, string(var(K)) => "a")
  pol = replace(pol, "//" => "/")
  println(io, "g := ", pol, ";")
  println(io, "E<b> := NumberField(g : DoLinearExtension);")
  F = gram_matrix(ambient_space(L))
  Fst = "[" * split(string([F[i, j] for i in 1:nrows(F) for j in 1:ncols(F)]), '[')[2]
  println(io, "F := Matrix(E, ", nrows(F), ", ", ncols(F), ", ", Fst, ");")
  pm = pseudo_matrix(L)
  M = matrix(pm)
  Mst = "[" * split(string([M[i, j] for i in 1:nrows(M) for j in 1:ncols(M)]), '[')[2]
  Mst = replace(Mst, "//" => "/")
  println(io, "M := Matrix(E, ", nrows(M), ", ", ncols(M), ", ", Mst, ");")
  println(io, "OE := MaximalOrder(E);")
  print(io, "C := [ ")
  for (i, I) in enumerate(coefficient_ideals(pm))
    print(io, "ideal< OE | ")
    bas = "[" * split(string(absolute_basis(I)), '[')[2]
    bas = replace(bas, string(var(K)) => "a")
    bas = replace(bas, string(var(E)) => "b")
    bas = replace(bas, "//" => "/")
    if i < length(coefficient_ideals(pm))
      print(io, bas, ">, ")
    else
      println(io, bas, ">];")
    end
  end
  println(io, "M := Module(PseudoMatrix(C, M));")
  println(io, "$target := HermitianLattice(M, F);")
end

function to_magma(io::IO, L::QuadLat; target = "L")
  K = nf(base_ring(L))
  println(io, "Qx<x> := PolynomialRing(Rationals());")
  f = absolute_minpoly(gen(K))
  pol = replace(string(f), "//" => "/")
  pol = replace(pol, string(var(parent(f))) => "x")
  println(io, "f := ", pol, ";")
  println(io, "K<a> := NumberField(f : DoLinearExtension);")
  F = gram_matrix(ambient_space(L))
  Fst = "[" * split(string([F[i, j] for i in 1:nrows(F) for j in 1:ncols(F)]), '[')[2]
  Fst = replace(Fst, string(var(K)) => "a")
  Fst = replace(Fst, "//" => "/")
  println(io, "F := Matrix(K, ", nrows(F), ", ", ncols(F), ", ", Fst, ");")
  pm = pseudo_matrix(L)
  M = matrix(pm)
  Mst = "[" * split(string([M[i, j] for i in 1:nrows(M) for j in 1:ncols(M)]), '[')[2]
  Mst = replace(Mst, "//" => "/")
  println(io, "M := Matrix(K, ", nrows(M), ", ", ncols(M), ", ", Mst, ");")
  println(io, "OK := MaximalOrder(K);")
  print(io, "C := [ ")
  for (i, I) in enumerate(coefficient_ideals(pm))
    print(io, "ideal< OK | ")
    bas = "[" * split(string(absolute_basis(I)), '[')[2]
    bas = replace(bas, string(var(K)) => "a")
    bas = replace(bas, "//" => "/")
    if i < length(coefficient_ideals(pm))
      print(io, bas, ">, ")
    else
      println(io, bas, ">];")
    end
  end
  println(io, "M := Module(PseudoMatrix(C, M));")
  println(io, "$target := LatticeModule(M, F);")
end

function var(E::RelSimpleNumField)
  return E.S
end

################################################################################
#
#  Zlattices
#
################################################################################

function to_hecke(io::IO, L::ZZLat; target = "L", skip_field = false)
  B = basis_matrix(L)
  G = gram_matrix(ambient_space(L))
  Bst = "[" * split(string([B[i, j] for i in 1:nrows(B) for j in 1:ncols(B)]), '[')[2]
  Gst = "[" * split(string([G[i, j] for i in 1:nrows(G) for j in 1:ncols(G)]), '[')[2]
  println(io, "B = matrix(QQ, ", nrows(B), ", ", ncols(B), " ,", Bst, ");")
  println(io, "G = matrix(QQ, ", nrows(G), ", ", ncols(G), " ,", Gst, ");")
  println(io, target, " = ", "integer_lattice(B, gram = G);")
end

function to_magma(io::IO, L::ZZLat; target = "L")
  B = basis_matrix(L)
  G = gram_matrix(ambient_space(L))
  Bst = "[" * split(string([B[i, j] for i in 1:nrows(B) for j in 1:ncols(B)]), '[')[2]
  Gst = "[" * split(string([G[i, j] for i in 1:nrows(G) for j in 1:ncols(G)]), '[')[2]
  Bst = replace(Bst, "//" => "/")
  Gst = replace(Gst, "//" => "/")
  println(io, "B := Matrix(Rationals(), ", nrows(B), ", ", ncols(B), " ,", Bst, ");")
  println(io, "G := Matrix(Rationals(), ", nrows(G), ", ", ncols(G), " ,", Gst, ");")
  println(io, target, " := ", "LatticeWithBasis(B, G);")
end

function to_sage(L::AbstractLat; target = "L")
  return to_sage(stdout, L, target = target)
end

function to_sage_string(L::AbstractLat; target = "L")
  b = IOBuffer()
  to_sage(b, L, target = target)
  return String(take!(b))
end

function to_sage(io::IO, L::ZZLat; target = "L")
  B = basis_matrix(L)
  G = gram_matrix(ambient_space(L))
  Bst = "[" * split(string([B[i, j] for i in 1:nrows(B) for j in 1:ncols(B)]), '[')[2]
  Gst = "[" * split(string([G[i, j] for i in 1:nrows(G) for j in 1:ncols(G)]), '[')[2]
  Bst = replace(Bst, "//" => "/")
  Gst = replace(Gst, "//" => "/")
  println(io, "B = Matrix(QQ, ", nrows(B), ", ", ncols(B), " ,", Bst, ")")
  println(io, "G = Matrix(QQ, ", nrows(G), ", ", ncols(G), " ,", Gst, ")")
  if is_integral(L)
    println(io, target, " = ", "IntegralLattice(G, B)")
  else
    println(io, "V = FreeQuadraticModule(ZZ, ", degree(L), ", ",  "inner_product_matrix = G)")
    println(io, target, " = ", "V.span(B)")
  end
end

