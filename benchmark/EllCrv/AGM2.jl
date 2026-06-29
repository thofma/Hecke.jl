function fmt_time(t)
  if t < 0.001
    return string(round(t * 1e6, digits=1), " us")
  elseif t < 1.0
    return string(round(t * 1000, digits=2), " ms")
  else
    return string(round(t, digits=3), " s")
  end
end

function from_integer(F::FinField, a::Hecke.IntegerUnion)
  return F(digits(a; base = Int(characteristic(F)), pad = degree(F)))
end

# we want to test some "standard" curves over large finite field of characteristic 2
# and they are not defined in canonical (for point counting) form
# thus we use _order_ordinary_char2 which handles transform (instead of direct _trace_of_frobenius_char2_agm)
function bench_agm(E, label, expected; nruns=3)
  n = Hecke._order_ordinary_char2(E)  # warmup
  @assert n == expected
  GC.gc()

  tmin = Inf
  for _ in 1:nruns
    t = @elapsed Hecke._order_ordinary_char2(E)
    tmin = min(tmin, t)
    GC.gc()
  end
  println("  $(rpad(label, 30)) $(lpad(fmt_time(tmin), 12))")
end

println("\n  -- Standard Curves --")
println("  " * "-"^66)

u = polynomial_ring(GF(2), :u; cached = false)[2]

# B-283 / sect283r1
R = finite_field(u^283 + u^12 + u^7 + u^5 + 1; cached = false)[1]
b = from_integer(R, 0x27b680ac8b8596da5a4af8a19a0303fca97fd7645309fa2a581485af6263e313b79a2f5)

E = elliptic_curve(R, [1, 1, 0, 0, b])
bench_agm(E, "B-283", ZZ(15541351137805832567355695254588151253139251848753809778218393053540088555574757385742))

# B-409 / sect409r1
R = finite_field(u^409 + u^87 + 1; cached = false)[1]
b = from_integer(R, 0x021a5c2c8ee9feb5c4b9a753b7b476b7fd6422ef1f3dd674761fa99d6ac27c8a9a197b272822f6cd57a55aa4f50ae317b13545f)

E = elliptic_curve(R, [1, 1, 0, 0, b])
bench_agm(E, "B-409", ZZ(1322111937580497197903830616065542079656809365928562438569297596608315549654749610416287447524358221931959734576733135053542))

# B-571 / sect571r1
R = finite_field(u^571 + u^10 + u^5 + u^2 + 1; cached = false)[1]
b = from_integer(R, 0x2f40e7e2221f295de297117b7f3d62f5c6a97ffcb8ceff1cd6ba8ce4a9a18ad84ffabbd8efa59332be7ad6756a66e294afd185a78ff12aa520e4de739baca0c7ffeff7f2955727a)

E = elliptic_curve(R, [1, 1, 0, 0, b])
bench_agm(E, "B-571", ZZ(7729075046034516689390703781863974688597854659412869997314470502903038284579120849072287998778831546166267762243853888972493744925633626140469056576606664822786382210571406))

println("\n  -- y^2 + xy = x^3 + t, t generator of GF(2^d) --")
println("  " * "-"^66)

R, t = finite_field(u^512 + u^8 + u^5 + u^2 + 1; cached = false)
E = elliptic_curve(R, [1, 0, 0, 0, t])
bench_agm(E, "d = 512", ZZ(13407807929942597099574024998205846127479365820592393377723561443721764030073606276971006953667003751979365653600622587914984785247330023043277969573988352))

R, t = finite_field(u^638 + u^6 + u^5 + u + 1; cached = false)
E = elliptic_curve(R, [1, 0, 0, 0, t])
bench_agm(E, "d = 638", ZZ(1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829344045437526326029232240235184516831587336476299238325770132737354627139472665885088739053994770432))

R, t = finite_field(u^791 + u^30 + 1; cached = false)
E = elliptic_curve(R, [1, 0, 0, 0, t])
bench_agm(E, "d = 791", ZZ(13023465689218465379062210528752456635048356098273258125773941038601635230112562639690297267327254474107284981627799297883438549033585908176509381195888109263257596837091903070389915318768370645415058883911233311061481962204917786597392384))

R, t = finite_field(u^1024 + u^19 + u^6 + u + 1; cached = false)
E = elliptic_curve(R, [1, 0, 0, 0, t])
bench_agm(E, "d = 1024", ZZ(179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474119168919771257752299164531615270143011858073768453147573722158291276608811283884527820736482067271591019972022810277271713322531975681952344292581844291584))
