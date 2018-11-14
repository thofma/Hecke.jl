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

set_verbose_level(:Fields, 1)

l = []

while length(l) == 0
  global dbound
  global l = fields(n, i, dbound)
  dbound = 100 * dbound
  println("========================================")
  println("Increasing discriminant bound: $dbound")
  println("========================================")
end

ll = map(v -> v[1], l)
ffields = [ (x, discriminant(maximal_order(x))) for x in ll ]
sort!(ffields, lt = (x, y) -> abs(x[2]) <= abs(y[2]))


@show length(ffields)

_write_fields(ffields, file)
