using Hecke, ArgParse

set_verbose_level(:ClassGroup, 1)

include(joinpath(Hecke.pkgdir,"examples/FieldEnumeration/FieldEnumeration.jl"))

function has_obviously_not_class_number_one(K::AnticNumberField)
  lll(maximal_order(K))
  subs = Hecke.subfields_normal(K)
  cmfields = []
  for (k,_) in subs
    if degree(k) == degree(K)
      continue
    end 
    fl, tau = Hecke.iscm_field(k)
    if !fl
      continue
    end
    kplus,_ = fixed_field(k, tau)
    h = order(class_group(lll(maximal_order(k)))[1])
    hplus = order(class_group(lll(maximal_order(kplus)))[1])
    @assert mod(h, hplus) == 0
    hminus = divexact(h, hplus)
    if gcd(hminus, fmpz(4)) == 1 || hminus > 4 
      return true
    end 
  end 
  return false
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

function ArgParse.parse_item(::Type{Vector{Int}}, x::AbstractString)
  return Meta.eval(Meta.parse(x))
end

function parse_commandline()
  s = ArgParseSettings()

  @add_arg_table s begin
    "--plus"
      help = "Compute plus class number"
      action = :store_true
    "--minus"
      help = "Compute minus class number"
      action = :store_true
    "--fields"
      help = "List containing the fields"
      arg_type = String
      required = true
  end

  return parse_args(s)
end

function main()
  parsed_args = parse_commandline()

  local plus::Bool
  local minus::Bool
  local fieldsfile::String

  for (arg, val) in parsed_args
    println("$arg => $val")
    if arg == "plus"
      plus = val
    elseif arg == "minus"
      minus = val
    elseif arg == "fields"
      fieldsfile = val
    end
  end

  sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

  if plus && !minus
    outfile = "class_numbers_h_hp_" * fieldsfile
  elseif !plus && minus
    outfile = "class_numbers_h_hm_" * fieldsfile
  elseif plus && minus
    outfile = "class_numbers_h_hp_hm_" * fieldsfile
  elseif !plus && !minus
    outfile = "class_numbers_h_" * fieldsfile
  end

  @show plus
  @show minus
  @show fieldsfile

  if !isfile(fieldsfile)
    throw(error("File $fields does not exist"))
  end

  if isfile(outfile)
    throw(error("Output file $outfile already exists!"))
  end

  print("Loading fields ... ")

  fields = _read_fields(fieldsfile)
  println("DONE")
  result = Vector{Any}(undef, length(fields))

  nonsimpleincluded = length(fields[1]) == 3

  # I change fields inplace

  for i in 1:length(fields)
    f = fields[i][1]
    K, = number_field(f, cached = false)

    local res
    
    if minus || plus
      println("Doing the cheap test $i/$(length(fields))")
      flush(stdout)
      fl = has_obviously_not_class_number_one(K)
      if fl
        println("Not relative class number one")
        flush(stdout)
        res = [fmpz(0), fmpz(0), fmpz(0)]
        result[i] = (fields[i]..., res...)
        continue
      end
    end

    OK = lll(maximal_order(K))
    @assert discriminant(OK) == fields[i][end]
    println("Computing class group number $i/$(length(fields)) ($f)")
    flush(stdout)
    c, _ = class_group(OK)
    h = order(c)
    res = [h]
    if minus || plus
      fl, tau = Hecke.iscm_field(K)
      println("Computing fixed field")
      k, = fixed_field(K, tau, simplify = true)
      println("Computing class group number $i/$(length(fields)) ($(defining_polynomial(k)))")
      flush(stdout)
      cc, = class_group(lll(maximal_order(k)))
      hplus = order(cc)
      @assert mod(h, hplus) == 0
      hminus = divexact(h, hplus)
      if plus
        push!(res, hplus)
      end
      if minus
        push!(res, hminus)
      end
    end
    result[i] = (fields[i]..., res...)
  end

  println("Writing to $outfile...")

  f = open(outfile, "a")

  for L in result
    z = (fmpq[ coeff(L[1], i) for i in 0:degree(L[1]) ],)
    i = -1
    if nonsimpleincluded
      y = Vector{fmpq}[fmpq[coeff(g, i) for i=0:degree(g)] for g in L[2]]
      zz = (z, y, L[3])
      i = 4
    else
      zz = (z, L[2])
      i = 3
    end
    zzz = (zz..., L[i:end]...)
    Base.write(f, "$zzz\n")
  end
  close(f)
end

main()
