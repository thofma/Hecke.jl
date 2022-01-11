using Hecke, Test

DEFAULT_NPROCS = 4

# Test if _adjust_path works on Windows
x = Hecke._adjust_path("GrpAb/Elem")
y = joinpath(Hecke.pkgdir, "test", "$x.jl")
@test isfile(y)

################################################################################
#
#  Analyze the arguments
#
################################################################################

# Is short?
short_test = false

if "short" in ARGS || get(ENV, "HECKE_TESTSHORT", "false") in ["1", "true"]
  global short_test = true
end

# Is long?
long_test = false

if "long" in ARGS || get(ENV, "HECKE_TESTLONG", "false") in ["1", "true"]
  global long_test = true
end

# Is GAP there?
_with_gap = false

push!(Base.LOAD_PATH, "@v#.#")

try
  using GAP
  println("Found GAP. Add FieldFactory.jl to the long tests")
  global _with_gap = true
catch e
  if !(isa(e, ArgumentError))
    rethrow(e)
  else
    println("using GAP failed.")
  end
end

# Parallel
isparallel = false
n_procs = 0

fl = get(ENV, "HECKE_TEST_PARALLEL", "false")
if fl != "false"
  isparallel = true
  n_procs = parse(Int, fl)
else
  for a in ARGS
    r = match(r"j([0-9])*", a)
    if r === nothing
      continue
    else
      global isparallel = true
      if r.captures[1] === nothing
        global n_procs = DEFAULT_NPROCS
      else
        global n_procs = parse(Int, r.captures[1])
      end
      @assert n_procs > 0 "Number of processes ($(n_procs)) must be > 0"
    end
  end
end

no_parallel = false

if haskey(ENV, "HECKE_TEST_PARALLEL")
  if ENV["HECKE_TEST_PARALLEL"] == "false"
    isparallel = false
    n_proces = 0
    no_parallel = true
  end
end

fl = get(ENV, "CI", "false")
if fl === "true" && !no_parallel
  isparallel = true
  # CPU_THREADS reports number of logical cores (including hyperthreading)
  # So be pessimistic and divide by 2
  n_procs = div(Sys.CPU_THREADS, 1)
end

# Now collect the tests we want to run

const exclude = ["setup.jl", "runtests.jl", "parallel.jl", "testdefs.jl", "FieldFactory.jl"]

test_directory = joinpath(@__DIR__)

const long_tests = String[]

if _with_gap
  push!(long_tests, "FieldFactory.jl")
end

tests = String[]

for t in readdir(test_directory)
  if !isfile(joinpath(test_directory, t))
    continue
  end

  if startswith(t, '.')
    continue
  end

  if t in long_tests
    if long_test
      push!(tests, t)
    else
      continue
    end
  end

  if !(t in exclude)
    push!(tests, t)
  end
end

# Put FieldFactory.jl and QuadForm.jl at the beginning, because they take the
# longest

for s in ["QuadForm.jl", "FieldFactory.jl"]
  if s in tests
    i = findfirst(isequal(s), tests)
    deleteat!(tests, i)
    pushfirst!(tests, s)
  end
end

test_path(test) = joinpath(@__DIR__, test)

@info "Hecke test setup"
@info "long_test : $long_test"
@info "short_test: $short_test"
if isparallel
  @info "parallel  : $isparallel ($(n_procs))"
else
  @info "parallel  : $isparallel"
end
@info "with_gap  : $(_with_gap)"
@info "tests     : $tests"

if short_test
  include("setup.jl")
  # Short tests are always running on one machine
  @info "Running short tests"
  include(joinpath("..", "system", "precompile.jl"))
else
  if !isparallel
    # We are not short
    k, a = quadratic_field(5)
    @test fmpz(1) - a == -(a - 1)
    @test 1 - a == -(a - 1)

    include("setup.jl")

    for t in tests
      @time include(test_path(t))
    end
  else
    # Now we are parallel
    include("parallel.jl")
  end

  #try
  #  using Polymake
  #  @time include("AlgAssRelOrd/Eichler.jl")
  #catch e
  #  if !(isa(e, ArgumentError))
  #    rethrow(e)
  #  else
  #    println("using Polymake failed. Not running sophisticated norm equation tests")
  #  end
  #end
end
