################################################################################
#
#  Conversion to parseble Hecke code
#
################################################################################

# This is helpful to construct code for the tests.
function to_hecke(L::AbsLat; target = "L", skip_field = false)
  return to_hecke(stdout, L, target = target, skip_field = skip_field)
end

function to_hecke_string(L::AbsLat; target = "L", skip_field = false)
  b = IOBuffer()
  to_hecke(b, L, target = target, skip_field = skip_field)
  return String(take!(b))
end

function to_hecke(io::IO, L::QuadLat; target = "L", skip_field = false)
  K = nf(base_ring(L))
  if !skip_field
    println(io, "Qx, x = PolynomialRing(FlintQQ, \"x\", cached = false)")
    f = defining_polynomial(K)
    pol = string(f)
    pol = replace(pol, string(var(parent(f))) => "x")
    println(io, "f = ", pol, ";")
    println(io, "K, a = number_field(f)")
  end
  F = gram_matrix(ambient_space(L))
  Fst = "[" * split(string([F[i, j] for i in 1:nrows(F) for j in 1:ncols(F)]), '[')[2]
  Fst = replace(Fst, string(var(K)) => "a")
  println(io, "D = matrix(K, ", nrows(F), ", ", ncols(F), ", ", Fst, ");")
  gens = generators(L)
  Gs = "["
  for i in 1:length(gens)
    g = gens[i]
    Gs = Gs * "[" * split(string(g), "[")[2]
    if i < length(gens)
      Gs = Gs * ", "
    end
  end
  Gs = Gs * "]"
  println(io, "gens = ", Gs)
  println(io, target, " = quadratic_lattice(K, generators = gens, gram_ambient_space = D)")
end

function to_hecke(io::IO, L::HermLat; target = "L", skip_field = skip_field)
  E = nf(base_ring(L))
  K = base_field(E)
  println(io, "Qx, x = PolynomialRing(FlintQQ, \"x\")")
  f = defining_polynomial(K)
  pol = replace(string(f), "//" => "/")
  pol = replace(pol, string(var(parent(f))) => "x")
  println(io, "f = ", pol)
  println(io, "K, a = NumberField(f, \"a\", cached = false)")
  println(io, "Kt, t = PolynomialRing(K, \"t\")")
  f = defining_polynomial(E)
  pol = replace(string(f), "//" => "/")
  pol = replace(pol, string(var(parent(f))) => "t")
  println(io, "g = ", pol, "")
  println(io, "E, b = NumberField(g, \"b\", cached = false)")
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
    gst = replace(string(g), string(var(E)) => "b")

    Gs = Gs * "map(E, [" * split(gst, "[")[2] * ")"
    if i < length(gens)
      Gs = Gs * ", "
    end
  end
  Gs = Gs * "]"
  println(io, "gens = ", Gs)

  println(io, target, " = hermitian_lattice(E, generators = gens, gram_ambient_space = D)")
end

################################################################################
#
#  Conversion to Magma
#
################################################################################

function to_magma(L::AbsLat; target = "L")
  return to_magma(stdout, L, target = target)
end

function to_magma_string(L::AbsLat; target = "L")
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
  pol = replace(string(f), "//" => "/")
  pol = replace(pol, string(var(parent(f))) => "t")
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

function to_magma(io::IO, L::AbsLat{AnticNumberField}; target = "L")
  K = nf(base_ring(L))
  println(io, "Qx<x> := PolynomialRing(Rationals());")
  f = defining_polynomial(K)
  pol = replace(string(f), "//" => "/")
  pol = replace(pol, string(var(parent(f))) => "x")
  println(io, "f := ", pol, ";")
  println(io, "K<a> := NumberField(f : DoLinearExtension);")
  F = gram_matrix(ambient_space(L))
  Fst = "[" * split(string([F[i, j] for i in 1:nrows(F) for j in 1:ncols(F)]), '[')[2]
  Fst = replace(Fst, "//" => "/")
  Fst = replace(Fst, string(var(K)) => "a")
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
  if L isa HermLat
    println(io, "$target := HermitianLattice(M, F);")
  else
    println(io, "$target := LatticeModule(M, F);")
  end
end

function var(E::NfRel)
  return E.S
end

################################################################################
#
#  Zlattices
#
################################################################################

function to_hecke(io::IO, L::ZLat; target = "L")
  B = basis_matrix(L)
  G = gram_matrix(ambient_space(L))
  Bst = "[" * split(string([B[i, j] for i in 1:nrows(B) for j in 1:ncols(B)]), '[')[2]
  Gst = "[" * split(string([G[i, j] for i in 1:nrows(G) for j in 1:ncols(G)]), '[')[2]
  println(io, "B = matrix(FlintQQ, ", nrows(B), ", ", ncols(B), " ,", Bst, ");")
  println(io, "G = matrix(FlintQQ, ", nrows(G), ", ", ncols(G), " ,", Gst, ");")
  println(io, target, " = ", "Zlattice(B, gram = G);")
end
