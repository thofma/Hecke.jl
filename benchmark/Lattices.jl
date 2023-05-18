using BenchmarkTools

function to_pari(x::ZZMatrix, varname = "x")
  s = "$varname = ["
  y = Hecke._eltseq(x)
  n = ncols(x)
  for i in 1:length(y)
    s = s * "$(y[i])"

    if i % n != 0
      s = s * ","
    else
      if i != length(y)
        s = s * ";"
      end
    end
  end

  s = s * "]"
  return s
end

function to_magma(x::ZZMatrix, varname = "x")
  n = nrows(x)
  m = ncols(x)
  s = "$varname := Matrix(Integers(), $n, $m, ["
  y = Hecke._eltseq(x)
  for i in 1:length(y)
    s = s * "$(y[i])"
    if i < length(y)
      s = s * ","
    end
  end
  s = s * "]);"
end

function to_magma(x::QQMatrix, varname = "x")
  n = nrows(x)
  m = ncols(x)
  s = "$varname := Matrix(Rationals(), $n, $m, ["
  y = Hecke._eltseq(x)
  for i in 1:length(y)
    s = s * "$(y[i])"
    if i < length(y)
      s = s * ","
    end
  end
  s = s * "]);"
  return s
end

function to_sage(x::QQMatrix, varname = "x")
  n = nrows(x)
  m = ncols(x)
  s = "$varname = Matrix(QQ, $n, $m, ["
  y = Hecke._eltseq(x)
  for i in 1:length(y)
    s = s * "$(y[i])"
    if i < length(y)
      s = s * ","
    end
  end
  s = s * "]);"
  return s
end

function benchmark_code_sage(L::Vector{Hecke.ZZLat}, repetitions::Int = 10; out_file::String = "sage_timings")
  s = """
  from sage.all import *
  import timeit
  res = []
  out_file = \"$(out_file)\"
  """
  for i in 1:length(L)
    G = gram_matrix(L[i])
    s = s * to_sage(G, "G$i") * "\n"
    s = s * """
    print(\"Doing\", $(i))
    t = 0.0
    for i in range($repetitions):
      L = IntegralLattice(G$(i))
      s = timeit.repeat(lambda: L.automorphisms(), repeat = 1, number = 1)
      t = t + s[0]
    t = t/$(repetitions)
    t = t/1000
    res.append(t)
    """
  end
  s = s * """
f = open(out_file, 'w')
f.write(\"%s\\n\" % res)
f.close()
quit()

  """
  return s
end

function benchmark_code_magma(L::Vector{Hecke.ZZLat}, repetitions::Int = 10; out_file::String = "magma_timings")
  default_repetitions = repetitions
  s = """
  res := [];
  """
  for i in 1:length(L)
    if rank(L[i]) <= 15
      repetitions = 100
    else
      repetitions = default_repetitions
    end
    G = gram_matrix(L[i])
    s = s * to_magma(G, "G$i") * "\n"
    s = s * """
    t0 := 0.0;
    \"Doing $(i)\";
    for i in [1..$(repetitions)] do
      L := LatticeWithGram(G$(i));
      t := Cputime();
      _ := AutomorphismGroup(L);
      t0 := t0 + Cputime(t);
    end for;
    t0av := RealNumberField()!t0/$(repetitions);
    Append(~res, [t0av, RealNumberField()!t0]);
    """
  end
  s = s * """
  PrintFile(\"$(out_file)\", res);
  quit;
  """
  return s
end

function benchmark_magma(L::Vector{Hecke.ZZLat})
  t, fp = mktemp()
  @show t
  out_file, fp_out = mktemp()
  close(fp_out)
  mcode = benchmark_code_magma(L, out_file = out_file)
  print(fp, mcode)
  close(fp)

  run(`magma $(t)`)
  rm(t)

  s = read(out_file, String)

  rm(out_file)

  t = Meta.eval(Meta.parse(s))
  return Float64[x[1] for x in t]
end

function benchmark_sage(L::Vector{Hecke.ZZLat})
  t, fp = mktemp()
  @show t
  out_file, fp_out = mktemp()
  close(fp_out)
  scode = benchmark_code_sage(L, out_file = out_file)
  print(fp, scode)
  close(fp)

  run(`/home/thofmann/SageMath/sage $(t)`)
  rm(t)

  s = read(out_file, String)

  rm(out_file)

  return Meta.eval(Meta.parse(s))
end

function benchmark_hecke(L::Vector{Hecke.ZZLat})
  res = Float64[]
  for i in 1:length(L)
    LL = L[i]
    println("Doing $i")
    t = @belapsed Hecke.assert_has_automorphisms($LL, redo = true) samples=10
    push!(res, t)
  end
  return res
end

function benchmark_all(L::Vector{Hecke.ZZLat})
  bM = benchmark_magma(L)
  bH = benchmark_hecke(L)
  bS = benchmark_sage(L)
end
