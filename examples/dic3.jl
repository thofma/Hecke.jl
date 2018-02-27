using Hecke

boundexp = ARGS[1]
c4fields = ARGS[2]
startfield = ARGS[3]
number = ARGS[4]

sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

if length(ARGS) == 5
  basename = ARGS[5]
else
  basename = ""
end

boundexp = parse(Int, boundexp)
startfield = parse(Int, startfield)
number = parse(Int, number)

@assert mod(boundexp, 3) == 0

boundquad = div(boundexp, 3)

lall = Hecke._read_fields(c4fields)

l = lall[startfield:(startfield + number - 1)]

width = length(string(length(lall)))

for (i, f) in enumerate(l)
  K, _ = NumberField(f[1], "a")
  @show K
  z = Hecke.Dic3_extensions(fmpz(10)^boundexp, K)
  @show length(z)
  if length(z) != 0
    fname = basename * sprint_formatted("%0$(width)d", startfield + i - 1)
    @show fname
    file = open(fname, "a")
    write(file, "# $(K.pol)\n")
    for (p, D) in z
      write(file, "($p, $D)\n")
    end
    close(file)
  end
end
