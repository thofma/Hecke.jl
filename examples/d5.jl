using Hecke

boundexp = ARGS[1]
startfield = ARGS[2]
endfield = ARGS[3]

if length(ARGS) == 4
  basename = ARGS[4]
else
  basename = ""
end

boundexp = parse(Int, boundexp)
startfield = parse(Int, startfield)
endfield = parse(Int, endfield)

@assert iseven(boundexp)

boundquad = div(boundexp, 2)

l = Hecke.quadratic_extensions(10^boundquad, u = startfield:endfield)

for (i, K) in enumerate(l)
  fname = basename * @sprintf("%012d", startfield + i - 1)
  @show fname
  file = open(fname, "a")
  write(file, "# $(K.pol)\n")
  Hecke.D5_extensions(fmpz(10)^boundexp, [K], file)
  close(file)
end
