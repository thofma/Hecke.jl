using ArgParse

using Hecke

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
    "--only-relative-one"
      help = "Keep only fields with relative class number one"
      action = :store_true
    "--relative-class-number"
      help = "Compute relative class number"
      action = :store_true
    "--class-number"
      help = "Compute class number"
      action = :store_true
    "--automorphism-group"
      help = "Compute Galois group"
      action = :store_true
    "--discriminant"
      help = "Discriminant"
      action = :store_true
    "--fields"
      help = "List containing the fields"
      arg_type = String
      required = true
  end

  return parse_args(s)
end

module T

if isdefined(Base, :Experimental) && isdefined(Base.Experimental, Symbol("@optlevel"))
  @eval Base.Experimental.@optlevel 0
end

using Hecke

using Base.Threads

set_verbose_level(:ClassGroup, 0)

function _fancy_class_number(OK)
  K = nf(OK)
  fl, N = Hecke.NormRel.norm_relation(K)
  if !fl || degree(K) < 20
    hK = order(class_group(OK, use_aut = true)[1])
  else
    hK = order(Hecke.NormRel.class_group_via_brauer(OK, N, compact = false)[1])
  end
  return hK
end


function has_obviously_not_relative_class_number_one(K::AnticNumberField)
  lll(maximal_order(K))
  subs = Hecke.subfields_normal(K)
  cmfields = []
  for (k,_) in subs
    if degree(k) == degree(K)
      continue
    end
    fl, tau = Hecke.is_cm_field(k)
    if !fl
      continue
    end
    kplus,_ = fixed_field(k, tau)
    h = order(class_group(lll(maximal_order(k)), use_aut = true)[1])
    hplus = order(class_group(lll(maximal_order(kplus)), use_aut = true)[1])
    @assert mod(h, hplus) == 0
    hminus = divexact(h, hplus)
    if hminus > 4 || hminus == 3
      return true
    end
  end
  return false
end

include(joinpath(Hecke.pkgdir,"examples/FieldEnumeration/FieldEnumeration.jl"))

function main()
  parsed_args = Main.parse_commandline()

  local _only_relative_one::Bool
  local _relative_class_number::Bool
  local _class_number::Bool
  local _automorphism_group::Bool
  local _discriminant::Bool
  local fieldsfile::String

  for (arg, val) in parsed_args
    println("$arg => $val")
    if arg == "only-relative-one"
      _only_relative_one = val
    elseif arg == "relative-class-number"
      _relative_class_number = val
    elseif arg == "class-number"
      _class_number = val
    elseif arg == "automorphism-group"
      _automorphism_group = val
    elseif arg == "discriminant"
      _discriminant = val
    elseif arg == "fields"
      fieldsfile = val
    end
  end

  sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

  outfile = splitext(fieldsfile)[1] * ".nfdb"

  if !isfile(fieldsfile)
    error("File $fields does not exist")
  end

  if isfile(outfile)
    error("Output file $outfile already exists!")
  end

  print("Loading fields ... ")

  fields = _read_fields(fieldsfile)
  println("DONE")
  result = Vector{Any}(undef, length(fields))

  nonsimpleincluded = length(fields[1]) == 3

  # I change fields inplace

  res = Dict{Any, Hecke.NFDBRecord{1}}()

  @threads for _f in fields
    f = _f[1]
    K, = number_field(f, cached = false)
    println(threadid(), ": Looking at", f)
    OK = lll(maximal_order(K))
    #@assert discriminant(OK) == fields[i][end]
    println(threadid(), ": Looking at disc", discriminant(OK))

    hK = ZZRingElem(0)
    hrelative = ZZRingElem(0)

    if _only_relative_one
      if has_obviously_not_relative_class_number_one(K)
        continue
      end
      hK = _fancy_class_number(OK)
      fl, tau = Hecke.is_cm_field(K)
      k, = fixed_field(K, tau, simplify = true)
      Ok = lll(maximal_order(k))
      hk = _fancy_class_number(Ok)
      @assert mod(hK, hk) == 0
      hrelative = divexact(hK, hk)
      if hrelative != 1
        continue
      end
    end

    r = Hecke._create_record(K)

    if _relative_class_number
      if hrelative == 0
        hK = _fancy_class_number(OK)
        fl, tau = Hecke.is_cm_field(K)
        k, = fixed_field(K, tau, simplify = true)
        Ok = lll(maximal_order(k))
        hk = _fancy_class_number(Ok)
        @assert mod(hK, hk) == 0
        hrelative = divexact(hK, hk)
      end

      r[:relative_class_number] = hrelative
    end

    if _class_number
      if hK == 0
        hK = _fancy_class_number(OK)
      end

      r[:class_number] = hK
    end

    if _automorphism_group
      r[:automorphism_group] = find_small_group(automorphism_group(K)[1])[1]
    end

    if _discriminant
      r[:discriminant] = discriminant(OK)
    end

    res[f] = r
  end

  nfdb = Hecke.NFDB(collect(values(res)))

  Hecke.add_meta!(nfdb, :title => "Database of $fieldsfile (only relative class number one $_only_relative_one)")

  f = open(outfile, "a")

  write(f, nfdb)

  close(f)
end
end

T.main()
