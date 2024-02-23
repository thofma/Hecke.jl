using Hecke, ArgParse

include(joinpath(Hecke.pkgdir,"examples/FieldEnumeration/FieldEnumeration.jl"))

function ArgParse.parse_item(::Type{ZZRingElem}, x::AbstractString)
  if in('^', x)
    l = split(x, '^')
    if length(l) != 2
      error("Could not parse $x as ZZRingElem")
    end
    l = string.(l)
    return (parse(ZZRingElem, l[1]))^parse(Int, l[2])
  else
    return parse(ZZRingElem, string(x))
  end
end

function ArgParse.parse_item(::Type{Vector{Int}}, x::AbstractString)
  return Meta.eval(Meta.parse(x))
end

function parse_commandline()
  s = ArgParseSettings()

  @add_arg_table s begin
    "--type", "-t"
      help = "Type of the abelian group"
      arg_type = Vector{Int}
      required = true
    "--conductors", "-c"
      help = "File containing the conductors"
      arg_type = String
      required = true
    "--only-real"
      help = "Only totally real fields"
      action = :store_true
    "--only-cm"
      help = "Only CM fields"
      action = :store_true
    "--non-simple"
      help = "Compute also non-simple presentation"
      action = :store_true
  end

  return parse_args(s)
end

function main()
  parsed_args = parse_commandline()

  local type::Vector{Int}
  local conds::String
  local only_real::Bool
  local only_cm::Bool
  local non_simple::Bool

  for (arg, val) in parsed_args
    println("$arg => $val")
    if arg == "type"
      type = val
    elseif arg == "conductors"
      conds = val
    elseif arg == "only-real"
      only_real = val
    elseif arg == "only-cm"
      only_cm = val
    elseif arg == "non-simple"
      non_simple = val
    end
  end

  sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

  @show type
  @show conds
  @show only_real
  @show only_cm
  @show non_simple

  file = "fields_" * string(type) * "_from_" * conds

  println("Output file $file")

  if isfile(file)
    error("File $file does already exist")
  end

  l_conductors = Vector{Int}()

  print("Loading conductors ... ")
  open(conds) do f
    for (i, lline) in enumerate(eachline(f))
      push!(l_conductors, parse(Int, lline))
    end
  end

  gtype = type

  Qx, x = polynomial_ring(QQ, "x")
  K, a = number_field(x - 1, "a")
  O = maximal_order(K)

  n=prod(gtype)
  expo=lcm(gtype)


  class_fields = Vector{Hecke.ClassField{Hecke.MapRayClassGrp, FinGenAbGroupHom}}()
  for (i, k) in enumerate(l_conductors)
    r, mr = Hecke.ray_class_groupQQ(O, k, true, expo)
    if !Hecke.has_quotient(r, gtype)
      continue
    end
    ls = subgroups(r, quotype = gtype, fun = (x, y) -> quo(x, y, false)[2])
    for s in ls
      C = ray_class_field(mr, s)::Hecke.ClassField{Hecke.MapRayClassGrp, FinGenAbGroupHom}
      if Hecke._is_conductor_minQQ(C, n)
        push!(class_fields, C)
      end
    end
  end
  fields = Vector()
  for i = 1:length(class_fields)
    println("Computing class field $(i) /$(length(class_fields))")
    C = class_fields[i]
    r, s = signature(C)
    if (!only_cm && !only_real) || (only_cm && r == 0) || (only_real && s == 0)
      NC = number_field(C)
      sfield = Hecke._from_relative_to_absQQ(NC, Hecke.automorphism_groupQQ(C))[1]
      if non_simple
        push!(fields, (sfield, NC, discriminant(maximal_order(sfield))))
      else
        push!(fields, (sfield, discriminant(maximal_order(sfield))))
      end
    end
  end

  #=
  #The non simple absolute extension and the absolute value of its discriminant
  fields = Vector{Tuple{AbsNonSimpleNumField, ZZRingElem}}()
  for i = 1:length(class_fields)
    println("Computing class field $(i) /$(length(class_fields))")
    C = class_fields[i]
    r, s = signature(C)
    if (!only_cm && !only_real) || (only_cm && r == 0) || (only_real && s == 0)
      L = number_field(C)
      polys = Vector{QQPolyRingElem}(undef, length(L.pol))
      for t = 1:length(L.pol)
        fK = Hecke.is_univariate(L.pol[t])[2]
        f = Qx(QQFieldElem[coeff(coeff(fK, j), 0) for j = 0:degree(fK)])
        polys[t] = f
      end
      NS, gNS = number_field(polys, check = false, cached = false)
      push!(fields, (NS, Hecke.discriminantQQ(O, C, Int(minimum(defining_modulus(C)[1])))))
    end
  end
  =#

  ll = fields

  # Discriminant always at the end
  sort!(ll, lt = (x, y) -> abs(x[end]) <= abs(y[end]))

  @show length(ll)

  println("Writing to $file...")

  ll = identity.(ll)
  _write_fields(ll, file)
end

main()


