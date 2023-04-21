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

function ArgParse.parse_item(::Type{Vector{Int}}, x::AbstractString)
  return map(y -> parse(Int, y), split(x, ','))
end

function parse_commandline()
  s = ArgParseSettings()

  @add_arg_table s begin
    "--input"
      help = "Input file"
      arg_type = String
      default = ""
    "--only-real"
      help = "Only totally real fields"
      action = :store_true
    "--disc-bound"
      help = "Discriminant bound"
      arg_type = ZZRingElem
    "--rootdisc-bound"
      help = "Root discriminant bound"
      arg_type = Float64
    "--only-complex"
      help = "Only totally complex fields"
      action = :store_true
    "--simplify"
      help = "Simplify the field"
      action = :store_true
    "--output"
      help = "Output file"
      arg_type = String
      default = ""
    "--type"
      help = "Type of the abelian extension"
      arg_type = Vector{Int}
      required = true
    "--silent"
      help = "No verbose out"
      action = :store_true
  end

  return parse_args(s)
end

function main()
  parsed_args = parse_commandline()

  local dbound::Union{ZZRingElem, Nothing}
  local rdbound::Union{Nothing, Float64}
  local only_real::Bool
  local only_complex::Bool
  local input::String
  local output::String
  local simplify::Bool
  local type::Vector{Int}
  local silent::Bool

  for (arg, val) in parsed_args
    if arg == "disc-bound"
      dbound = val
    elseif arg == "rootdisc-bound"
      rdbound = val
    elseif arg == "only-real"
      only_real = val
    elseif arg == "only-complex"
      only_complex = val
    elseif arg == "simplify"
      simplify = val
    elseif arg == "input"
      input = val
    elseif arg == "output"
      output = val
    elseif arg == "type"
      type = val
    elseif arg == "silent"
      silent = val
    end
  end

  if !silent
    if dbound !== nothing
      @info "Discriminant bound $dbound"
    end

    if rdbound !== nothing
      @info "Root discriminant bound $rdbound"
    end

    @info "Extensions of type: $type"

    @info "Simplifying fields: $simplify"

    old_output = output

    if output == ""
      output = input * ".out"
    end

    @info "Only real fields: $only_real"
    @info "Only complex fields: $only_complex"
    @info "Input from: $input"

    if old_output == ""
      @info "Output to: $output (default)"
    else
      @info "Output to: $output"
    end

    set_verbose_level(:AbExt, 1)
  end

  if input == ""
    error("Input file must be specified by --input")
  end

  if dbound == nothing && rdbound == nothing
    error("One of --disc-bound or --rootdisc-bound must be specified")
  elseif dbound != nothing && rdbound != nothing
    error("Only one of --disc-bound or --rootdisc-bound can be set")
  end

  if only_complex && only_real
    error("Only one of --only-real or --only-complex can be set")
  end

  sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

  if output == ""
    output = input * ".out"
  end

  if isfile(output)
    error("Output file $output already exists. You may specify the output file by setting --output")
  end

  ending = String(split(basename(input), ".")[2])

  relative_deg = prod(type)

  if ending == "nfdb"
    DBin = Base.read(input, Hecke.NFDB)

    res = eltype(DBin)[]

    for _K in DBin
      K = Hecke.field(_K, cached = false)
      if dbound isa ZZRingElem
        _dbound = dbound
      else
        @assert rdbound isa Float64
        _dbound = ZZRingElem(BigInt(ceil(BigFloat(rdbound)^(degree(K) * relative_deg))))
      end

      if only_real
        if !is_totally_real(K)
          continue
        end

        l = Hecke.abelian_extensions(K, type, _dbound, ramified_at_inf_plc = (true, InfPlc[]))
      elseif only_complex
        l = Hecke.abelian_extensions(K, type, _dbound, ramified_at_inf_plc = (true, real_places(K)))
      else
        l = Hecke.abelian_extensions(K, type, _dbound)
      end

      for C in l
        if dbound isa ZZRingElem
          @assert absolute_discriminant(C) <= dbound
        elseif rdbound isa Float64
          @assert Float64(absolute_discriminant(C)) <= rdbound^(degree(K) * relative_deg)
        end
        if only_real
          @assert signature(C)[2] == 0
        elseif only_complex
          @assert signature(C)[1] == 0
        end

        L = absolute_simple_field(number_field(C), cached = false, simplify = simplify)[1]
        r = Hecke._create_record(L)
        r[:discriminant] = absolute_discriminant(C)
        push!(res, r)
      end
    end

    DBout = Hecke.NFDB(res)
    t = "Abelian extensions with type $type"
    if dbound isa ZZRingElem
      t = t * ", dbound $dbound"
    else
      t = t * ", rdbound $rdbound"
    end
    t = t * ", of $input"
    Hecke.add_meta!(DBout, :title => t)
    open(output, "w") do f
      Base.write(f, DBout)
    end
  end
end

main()
