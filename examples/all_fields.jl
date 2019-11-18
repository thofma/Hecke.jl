using GAP, Hecke, Printf, ArgParse

include(joinpath(Hecke.pkgdir,"examples/FieldEnumeration.jl"))

###############################################################################
#
#  Read-Write
#
###############################################################################

function _write_fields(list::Array{Tuple{AnticNumberField, fmpz},1}, filename::String)
  f=open(filename, "a")
  for L in list
    x=([coeff(L[1].pol, i) for i=0:degree(L[1].pol)], L[2])
    Base.write(f, "$x\n")
  end
  close(f)
end

function _read_fields(filename::String)
  f=open(filename, "r")
  Qx,x=PolynomialRing(FlintQQ,"x")
  pols=Tuple{fmpq_poly, fmpz}[]
  for s in eachline(f)
    a=eval(parse(s))
    push!(pols,(Qx(a[1]), a[2]))
  end
  close(f)
  return pols
end 

function ArgParse.parse_item(::Type{fmpz}, x::AbstractString)
  if in('^', x)
    l = split(x, '^')
    if length(l) != 2
      throw(error("Could not parse $x as fmpz"))
    end
    l = string.(l)
    return (parse(fmpz, l[1]))^parse(Int, l[2])
  else
    return parse(fmpz, string(x))
  end
end

function parse_commandline()
  s = ArgParseSettings()

  @add_arg_table s begin
    "--order", "-o"
      help = "Order of the group"
      arg_type = Int
      default = -1
    "--id", "-i"
      help = "Id of the group"
      arg_type = Int
      default = -1
    "--number", "-n"
      help = "Number of the group"
      arg_type = Int
      default = -1
    "--tamely-ramified"
      help = "Only tamely ramified fields"
      action = :store_true
    "--only-real"
      help = "Only totally real fields"
      action = :store_true
    "--disc-bound"
      help = "Discriminant bound"
      arg_type = fmpz
      required = true
  end

  return parse_args(s)
end

function main()
  parsed_args = parse_commandline()

  local grp_order::Int
  local grp_id::Int
  local dbound::fmpz
  local only_real::Bool
  local only_tame::Bool
  local grp_no::Int

  for (arg, val) in parsed_args
    println("$arg => $val")
    if arg == "order"
      grp_order = val
    elseif arg == "id"
      grp_id = val
    elseif arg == "disc-bound"
      dbound = val
    elseif arg == "only-real"
      only_real = val
    elseif arg == "tamely-ramified"
      only_tame = val
    elseif arg == "number"
      grp_no = val
    end
  end

  sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

  if grp_id != -1
    @assert grp_order != -1
    n = grp_order
    i = grp_id
    grp_no = findfirst(isequal((n, i)), small_solvable_groups)
  else
    @assert grp_no != -1
    n, i = small_solvable_groups[grp_no]
  end

  _n = clog(dbound, fmpz(10))
  if fmpz(10)^_n == dbound
    file = sprint_formatted("%0$(length(string(length(small_solvable_groups))))d", grp_no) * "-$n-$i-10^$(_n)."* "log"
  else
    file = sprint_formatted("%0$(length(string(length(small_solvable_groups))))d", grp_no) * "-$n-$i-$dbound."* "log"
  end

  @show grp_order
  @show grp_id
  @show grp_no
  @show dbound
  @show only_real
  @show only_tame
  @show file

  if isfile(file)
    throw(error("File $file does already exist"))
  end

  println("========================================")
  println("Group: $grp_no: $n $i")
  println("========================================")

  println("========================================")
  println("Discriminant bound: $dbound")
  println("========================================")

  set_verbose_level(:FieldsNonFancy, 1)

  l = fields(n, i, dbound, only_real = only_real, simplify = false)

  ll = map(v -> v.field, l)
  ffields = [ (x, discriminant(maximal_order(x))) for x in ll ]
  sort!(ffields, lt = (x, y) -> abs(x[2]) <= abs(y[2]))

  @show length(ffields)

  _write_fields(ffields, file)
end

main()
