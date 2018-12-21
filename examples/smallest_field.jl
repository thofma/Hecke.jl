using Libdl, Printf

push!(Libdl.DL_LOAD_PATH, "/tmpbig/thofmann/juliagap/libgap/.libs/")
include("/tmpbig/thofmann/juliagap/LibGAP.jl/src/initialization.jl")
libgap.initialize( [ ""
                   , "-l", "/tmpbig/thofmann/juliagap/libgap/"
                   , "-T", "-r", "-A", "-q"
                   , "-m", "512m" ], ["\0"])

using Hecke

include("/users/cip/users/thofmann/CarloLibGAPTest/towards_cohomology.jl")
include("/tmpbig/thofmann/v0.6/Hecke/examples/FieldEnumeration.jl")
include("/tmpbig/thofmann/v0.6/Hecke/examples/fields.jl")

sprint_formatted(fmt, args...) = @eval @sprintf($fmt, $(args...))

grp_no = Int(eval(Meta.parse(ARGS[1])))

n, i = small_solvable_groups[grp_no]

file = sprint_formatted("%0$(length(string(length(small_solvable_groups))))d", grp_no) * "-$n-$i."* "log"

println("========================================")
println("Group: $n $i")
println("========================================")

global dbound = 0

if length(ARGS) == 2
  dbound = fmpz(eval(Meta.parse(ARGS[2])))
else
  if mod(n, 2) == 0
    dbound = Hecke.lower_discriminant_bound(n, div(n, 2))
  else
    dbound = Hecke.lower_discriminant_bound(n, 0)
  end
end

dbound = 10 * dbound

println("========================================")
println("Discriminant bound: $dbound")
println("========================================")

set_verbose_level(:FieldsNonFancy, 1)

l = []

global complex_fields = []
global real_fields = []
global all = []

global found_complex = false
global found_real = false

if mod(n, 2) != 0
  found_complex = true
end

global only_real = false

while true
  global complex_fields
  global real_fields
  global found_complex
  global found_real
  global only_real
  global dbound

  @show only_real

  global l = fields(n, i, dbound, only_real = only_real)

  for v in l
    x = v[1]
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

ll = map(v -> v[1], l)
ffields = [ (x, discriminant(maximal_order(x))) for x in ll ]
sort!(ffields, lt = (x, y) -> abs(x[2]) <= abs(y[2]))


@show length(ffields)

_write_fields(ffields, file)
