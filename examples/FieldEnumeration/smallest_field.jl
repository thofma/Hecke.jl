using GAP, Hecke, Printf, ArgParse

include(joinpath(Hecke.pkgdir,"examples/FieldEnumeration.jl"))

###############################################################################
#
#  Read-Write
#
###############################################################################

function _write_fields(list::Vector{Tuple{AnticNumberField, ZZRingElem}}, filename::String)
  f=open(filename, "a")
  for L in list
    x=([coeff(L[1].pol, i) for i=0:degree(L[1].pol)], L[2])
    Base.write(f, "$x\n")
  end
  close(f)
end

function _read_fields(filename::String)
  f=open(filename, "r")
  Qx,x=polynomial_ring(FlintQQ,"x")
  pols=Tuple{QQPolyRingElem, ZZRingElem}[]
  for s in eachline(f)
    a=eval(parse(s))
    push!(pols,(Qx(a[1]), a[2]))
  end
  close(f)
  return pols
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
      arg_type = ZZRingElem
      default = ZZRingElem(-1)
  end

  return parse_args(s)
end

function main()
  parsed_args = parse_commandline()

  local grp_order::Int
  local grp_id::Int
  local dbound::ZZRingElem
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

  file = sprint_formatted("%0$(length(string(length(small_solvable_groups))))d", grp_no) * "-$n-$i."* "log"

  @show grp_order
  @show grp_id
  @show grp_no
  @show dbound
  @show only_real
  @show only_tame
  @show file

  if isfile(file)
    error("File $file does already exist")
  end

  println("========================================")
  println("Group: $grp_no: $n $i")
  println("========================================")

  if dbound == -1
    dbound = Hecke.lower_discriminant_bound(n, n)
  end

  dbound = 10 * dbound

  println("========================================")
  println("Discriminant bound: $dbound")
  println("========================================")

  set_verbose_level(:FieldsNonFancy, 1)

  l = []

  complex_fields = []
  real_fields = []
  all = []

  found_complex = false
  found_real = false

  if mod(n, 2) != 0
    found_complex = true
  end

  while true

    @show only_real

    l = fields(n, i, dbound, only_real = only_real)

    for v in l
      x = v.field
      if !found_complex
        if signature(x)[2] != 0
          push!(complex_fields, v)
        end
      end

      if !found_real
        if signature(x)[2] == 0
          push!(real_fields, v)
        end
      end
    end

    if !found_complex && length(complex_fields) > 0
      append!(all, complex_fields)
      found_complex = true
      println("== FOUND SOMETHING COMPLEX ==")
      empty!(complex_fields)
    end

    if !found_real && length(real_fields) > 0
      append!(all, real_fields)
      found_real = true
      println("== FOUND SOMETHING REAL ==")
      empty!(real_fields)
    end

    if found_complex
      if !found_real
        only_real = true
        println("== I AM IN ONLY_REAL = TRUE MODE ==")
      else
        println("== EXITING ==")
        break
      end
    end

    dbound = 100 * dbound
    println("========================================")
    println("Increasing discriminant bound: $dbound")
    println("========================================")
    println("only_real = $only_real")
    println("found_complex = $found_complex")
    println("found_real = $found_real")
  end

  l = all

  ll = map(v -> v.field, l)
  ffields = [ (x, discriminant(maximal_order(x))) for x in ll ]
  sort!(ffields, lt = (x, y) -> abs(x[2]) <= abs(y[2]))


  @show length(ffields)

  _write_fields(ffields, file)
end

main()
