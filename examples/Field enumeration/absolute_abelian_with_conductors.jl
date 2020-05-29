using Hecke

gtype = ARGS[1]
conductors = ARGS[2]
startcond = ARGS[3]
endcond = ARGS[4]

gtype = convert(Vector{Int}, eval(parse(gtype)))
gtype = map(Int, snf(abelian_group(gtype))[1].snf)
conductors = convert(Vector{Int}, eval(parse(conductors)))
startcond = parse(Int, startcond)
endcond = parse(Int, endcond)
l_conductors = conductors[startcond:endcond]

sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

Qx, x = PolynomialRing(QQ, "x")
K, a = NumberField(x - 1, "a")
O = maximal_order(K)

n=prod(gtype)
expo=lcm(gtype)


class_fields = Vector{Hecke.ClassField{MapRayClassGrp, GrpAbFinGenMap}}()
for (i, k) in enumerate(l_conductors)
  r, mr = Hecke.ray_class_groupQQ(O, k, true, expo)
  if !has_quotient(r, gtype)
    continue
  end
  ls = subgroups(r, quotype = gtype, fun = (x, y) -> quo(x, y, false)[2])
  for s in ls
    C = ray_class_field(mr, s)::Hecke.ClassField{MapRayClassGrp, GrpAbFinGenMap}
    if Hecke._is_conductor_minQQ(C, n) 
      push!(class_fields, C)
    end
  end
end
fields = Vector{AnticNumberField}(undef, length(class_fields))
for i = 1:length(class_fields)
  @vprint :Fields 1 "\e[1FComputing class field $(i) /$(length(class_fields)) \n"
  C = class_fields[i]
  fields[i] = _from_relative_to_absQQ(number_field(C), Hecke.automorphism_groupQQ(C))[1]
end

Hecke._write_fields(fields, file)