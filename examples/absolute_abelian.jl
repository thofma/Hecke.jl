using Hecke

bounddisc = ARGS[1]
real = ARGS[2]
gtype = ARGS[3]
startcond = ARGS[4]
number = ARGS[5]

bounddisc = fmpz(eval(parse(bounddisc)))
gtype = convert(Vector{Int}, eval(parse(gtype)))
startcond = parse(Int, startcond)
number = parse(Int, number)
real = parse(Bool, real)

sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

Qx, x = PolynomialRing(QQ, "x")
K, a = NumberField(x - 1, "a")
O = maximal_order(K)

n=prod(gtype)
expo=lcm(gtype)


if length(ARGS) == 6
   print("Loading conductors ... ")
   conductors = readdlm(ARGS[6], Int)
   conductors = conductors[:, 1]
   println("DONE")
#  basename = ARGS[4]
else
   conductors = sort!(Hecke.conductorsQQ(O, n, bounddisc))
end

width = length(string(length(conductors)))

l_conductors = conductors[startcond:max(length(conductors), startcond + number - 1)]


fields=Tuple{AnticNumberField, fmpz}[]
#  autos=Vector{NfRel_nsToNfRel_nsMor}[]

#Now, the big loop
for (i, k) in enumerate(l_conductors)
  print("Left: $(length(l_conductors) - i)\n")
  r,mr=Hecke.ray_class_groupQQ(O,k,!real,expo)
  if !Hecke._are_there_subs(r,gtype)
    continue
  end
  ls=subgroups(r,quotype=gtype, fun= (x, y) -> quo(x, y, false)[2])
  for s in ls
    C=Hecke.ray_class_field(mr*inv(s))
    if Hecke._is_conductor_minQQ(C,n) && Hecke.discriminant_conductorQQ(O,C,k,bounddisc,n)
      L=number_field(C)
      LL = Hecke.absolute_field(Hecke.simple_extension(L)[1])[1]
      push!(fields, (Hecke.simplify(LL)[1], discriminant(maximal_order(LL))))
    end
  end
end

if length(ARGS) == 6
  file = ARGS[6] * "_" * sprint_formatted("%0$(width)d", startcond) * "-" * sprint_formatted("%0$(width)d", startcond + number - 1)
else
  file = sprint_formatted("%0$(width)d", startcond) * "-" * sprint_formatted("%0$(width)d", startcond + number - 1)
end

@show length(fields)

Hecke._write_fields(fields, file)

