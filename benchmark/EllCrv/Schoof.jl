function fmt_time(t)
  if t < 0.001
    return string(round(t * 1e6, digits=1), " us")
  elseif t < 1.0
    return string(round(t * 1000, digits=2), " ms")
  else
    return string(round(t, digits=3), " s")
  end
end

function bench_schoof(E, label; nruns=3)
  n = Hecke.order_via_schoof(E)  # warmup
  GC.gc()
  tmin = Inf
  for _ in 1:nruns
    t = @elapsed Hecke.order_via_schoof(E)
    tmin = min(tmin, t)
    GC.gc()
  end
  println("  $(rpad(label, 30)) |E| = $(rpad(n, 25))  $(lpad(fmt_time(tmin), 12))")
  return tmin
end

println("\n  -- Prime fields (large characteristic, degree 1) --")
println("  " * "-"^66)
for p in ZZRingElem[1009, 10007, 100003, 1000003, 10000019, 100000007,
                    1000000007, 10000000019, 100000000019, 1000000000039,
                    10000000000037, 100000000000031, 1000000000000037]
  F, a = finite_field(p, 1)
  E = elliptic_curve(F, [F(1), F(2)])
  bench_schoof(E, "GF($p)")
end

println("\n  -- Extension fields (small characteristic, large degree) --")
println("  " * "-"^66)
for (p, d) in Iterators.product([5, 7, 11, 13], [7, 8, 9, 10, 11, 12])
  F, a = finite_field(p, d)
  E = elliptic_curve(F, [a, a + F(1)])
  bench_schoof(E, "GF($(p)^$(d))")
end
