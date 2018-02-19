using Hecke

boundexp = ARGS[1]
startfield = ARGS[2]
number = ARGS[3]

sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

if length(ARGS) == 4
  basename = ARGS[4]
else
  basename = ""
end

boundexp = parse(Int, boundexp)
startfield = parse(Int, startfield)
number = parse(Int, number)

@assert iseven(boundexp)

boundquad = div(boundexp, 2)

lall = Hecke.quadratic_extensions(10^boundquad)

l = Hecke.quadratic_extensions(10^boundquad, u = startfield:(startfield + number - 1))

width = length(string(length(lall)))

for (i, K) in enumerate(l)
  fname = basename * sprint_formatted("%0$(width)d", startfield + i - 1)
  @show fname
  file = open(fname, "a")
  write(file, "# $(K.pol)\n")
  Hecke.D5_extensions(fmpz(10)^boundexp, [K], file)
  close(file)
end
