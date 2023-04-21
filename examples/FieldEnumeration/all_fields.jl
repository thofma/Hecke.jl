using GAP, Hecke, Printf, ArgParse

include(joinpath(Hecke.pkgdir,"examples/FieldEnumeration/FieldEnumeration.jl"))

###############################################################################
#
#  Read-Write
#
###############################################################################

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
    "--only-complex"
      help = "Only totally complex fields"
      action = :store_true
    "--disc-bound"
      help = "Discriminant bound"
      arg_type = ZZRingElem
    "--rootdisc-bound"
      help = "Discriminant bound"
      arg_type = Float64
    "--only-cm"
      help = "Only CM fields"
      action = :store_true
    "--max-ab-subfields"
      help = "File containing maximal abelian subextensions"
    "--simplify"
      help = "Simplify the field"
      action = :store_true
    "--output"
      help = "Output file"
      arg_type = String
      default = ""
    "--output-type"
      help = "Type of output file. Options are default (uses _write_fields), polys, nfdb"
      default = "default"
    "--silent"
      help = "No verbose out"
      action = :store_true
  end

  return parse_args(s)
end

function main()
  parsed_args = parse_commandline()

  local grp_order::Int
  local grp_id::Int
  local dbound::Union{ZZRingElem, Nothing}
  local only_real::Bool
  local only_complex::Bool
  local only_tame::Bool
  local grp_no::Int
  local only_cm::Bool
  local maxabsubfields::Union{String, Nothing}
  local simplify::Bool
  local output::String
  local rdbound::Union{Float64, Nothing}
  local silent::Bool

  for (arg, val) in parsed_args
    #println("$arg => $val")
    if arg == "order"
      grp_order = val
    elseif arg == "id"
      grp_id = val
    elseif arg == "disc-bound"
      dbound = val
    elseif arg == "rootdisc-bound"
      rdbound = val
    elseif arg == "only-real"
      only_real = val
    elseif arg == "only-complex"
      only_complex = val
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
    elseif arg == "silent"
      silent = val
    elseif arg == "output"
      output = val
    end
  end

  sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

  if grp_id != -1
    n = grp_order
    i = grp_id
  end

  if !silent
    @info "Small group ($n, $i)"

    if dbound !== nothing
      @info "Discriminant bound $dbound"
    end

    if rdbound !== nothing
      @info "Root discriminant bound $rdbound"
    end

    @info "Simplifying fields: $simplify"

    if output == ""
      output = "fields_$(i)_$(n).nfdb"
    end

    if isfile(output)
      error("Output file $output already exists. You may specify the output file by setting --output")
    end

    @info "Maximal abelian fields: $maxabsubfields"
    @info "Only real fields: $only_real"
    @info "Only complex fields: $only_complex"
    @info "Only CM: $only_cm"

    @info "Output to: $output"

    set_verbose_level(:FieldsNonFancy, 3)
  end

  if dbound == nothing && rdbound == nothing
    error("One of --disc-bound or --rootdisc-bound must be specified")
  elseif dbound != nothing && rdbound != nothing
    error("Only one of --disc-bound or --rootdisc-bound can be set")
  end

  if only_complex && only_real
    error("Only one of --only-real or --only-complex can be set")
  end

  if dbound === nothing
    dbound = ZZRingElem(BigInt(ceil(BigFloat(rdbound)^(n))))
    if !silent
      @info "Translated root discriminant bound to: $dbound"
    end
  end

  if grp_id != -1
    @assert grp_order != -1
    n = grp_order
    i = grp_id
    grp_no = findfirst(isequal((n, i)), small_solvable_groups)
  else
    @assert grp_no != -1
    n, i = small_solvable_groups[grp_no]
  end

  flush(stdout)

  if maxabsubfields isa String
    maxabsub = Hecke._read_from_file(maxabsubfields)
    l = fields(n, i, maxabsub, dbound, only_real = only_real)
  else
    l = fields(n, i, dbound, only_real = only_real)
  end

  flush(stdout)

  # Determine the automorphism groups
  if only_cm
    Hecke.assure_automorphisms.(l)
  end

  flush(stdout)

  ll = map(v -> v.field, l)

  flush(stdout)

  if only_cm
    ffields = [ (x, discriminant(maximal_order(x))) for x in ll if Hecke.is_cm_field(x)[1]]
  else
    ffields = [ (x, discriminant(maximal_order(x))) for x in ll ]
  end

  flush(stdout)

  sort!(ffields, lt = (x, y) -> abs(x[2]) <= abs(y[2]))

  res = eltype(Hecke.NFDB{1})[]

  for (x, y) in ffields
    if simplify
      x, _ = Hecke.simplify(x)
    end
    r = Hecke._create_record(x)
    r[:discriminant] = y
    push!(res, r)
  end

  DBout = Hecke.NFDB(res)
  t = "fields($n, $i, $dbound, only_real = $only_real, simplify = $simplify)"
  if rdbound !== nothing
    t = t * " (rd bound $rdbound)"
  end
  if maxabsubfields isa String
    t = t * " with maximal abelian subfields from $maxabsubfields"
  end
  Hecke.add_meta!(DBout, :title => t)
  open(output, "w") do f
    Base.write(f, DBout)
  end
end

main()
