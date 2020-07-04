using GAP, Hecke, Printf, ArgParse

include(joinpath(Hecke.pkgdir,"examples/FieldEnumeration/FieldEnumeration.jl"))

###############################################################################
#
#  Read-Write
#
###############################################################################

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
    "--only-cm"
      help = "Only CM fields"
      action = :store_true
    "--max-ab-subfields"
      help = "File containing maximal abelian subextensions" 
    "--simplify"
      help = "Simplify the field"
      action = :store_true
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
  local only_cm::Bool
  local maxabsubfields::Union{String, Nothing}
  local simplify::Bool

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
    elseif arg == "only-cm"
      only_cm = val
    elseif arg == "max-ab-subfields"
      maxabsubfields = val
    elseif arg == "simplify"
      simplify = val
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
    file = sprint_formatted("%0$(length(string(length(small_solvable_groups))))d", grp_no) * "-$n-$i-10^$(_n)"
  else
    file = sprint_formatted("%0$(length(string(length(small_solvable_groups))))d", grp_no) * "-$n-$i-$dbound"
  end

  if maxabsubfields isa String
    file = file * "_" * maxabsubfields
  end

  file = file * ".log"

  @show grp_order
  @show grp_id
  @show grp_no
  @show dbound
  @show only_real
  @show only_tame
  @show only_cm
  @show file
  @show simplify

  if maxabsubfields isa String
    @show maxabsubfields
  end

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

  if maxabsubfields isa String
    maxabsub = Hecke._read_from_file(maxabsubfields)
    l = fields(n, i, maxabsub, dbound, only_real = only_real, simplify = simplify)
  else
    l = fields(n, i, dbound, only_real = only_real, simplify = simplify)
  end

  # Determine the automorphism groups
  if only_cm
    Hecke.assure_automorphisms.(l)
  end

  ll = map(v -> v.field, l)

  if only_cm
    ffields = [ (x, discriminant(maximal_order(x))) for x in ll if Hecke.iscm_field(x)[1]]
  else
    ffields = [ (x, discriminant(maximal_order(x))) for x in ll ]
  end

  sort!(ffields, lt = (x, y) -> abs(x[2]) <= abs(y[2]))

  @show length(ffields)

  _write_fields(ffields, file)
end

main()
