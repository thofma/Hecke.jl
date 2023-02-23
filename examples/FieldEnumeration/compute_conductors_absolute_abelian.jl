using Hecke

bounddisc = ARGS[1]
gtype = ARGS[2]

file = "conductors_" * bounddisc * "_" * gtype;

bounddisc = ZZRingElem(eval(parse(bounddisc)))
gtype = convert(Vector{Int}, eval(parse(gtype)))

sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

Qx, x = polynomial_ring(QQ, "x")
K, a = number_field(x - 1, "a")
O = maximal_order(K)

n=prod(gtype)
expo=lcm(gtype)

print("Computing conductors ... ")

conductors = sort!(Hecke.conductorsQQ(O, n, bounddisc))

println("DONE")

if length(ARGS) == 3
  file = ARGS[3]
else
  file = file * "_" * string(length(conductors))
end

if isfile(file)
  error("File $file already exists")
end

open(file, "w") do f
  print("Writing conductors to $file ... ")
  writedlm(f, conductors)
  println("DONE")
end

@assert countlines(file) == length(conductors)
