using Hecke
using Test
using Hecke.Dates
using Hecke.Printf
using Documenter

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

if "threads" in ARGS || get(ENV, "HECKE_TEST_THREADS", "false") in ["1", "true"]
  @info "Running only threading tests with $(Threads.nthreads()): threads.jl"
  include("threads.jl")
  exit()
end

# Is short?
short_test = false

if "short" in ARGS || get(ENV, "HECKE_TESTSHORT", "false") in ["1", "true"] ||
    haskey(ENV, "JULIA_PKGEVAL")
  global short_test = true
end

# Is long?
long_test = false

if "long" in ARGS || get(ENV, "HECKE_TESTLONG", "false") in ["1", "true"]
  global long_test = true
end

PRINT_TIMING_LEVEL = -1
fl = get(ENV, "HECKE_TEST_TIMING", "false")
if fl != "false"
  isparallel = true
  global PRINT_TIMING_LEVEL = parse(Int, fl)
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

# Is Polymake there?
_with_polymake = false

try
  import Polymake
  println("Found Polymake.")
  global _with_polymake = true
catch e
  if !(isa(e, ArgumentError))
    rethrow(e)
  else
    println("using Polymake failed.")
  end
end

# Parallel
isparallel = false
n_procs = 0

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

no_parallel = false

if haskey(ENV, "HECKE_TEST_PARALLEL")
  if ENV["HECKE_TEST_PARALLEL"] == "false"
    isparallel = false
    n_proces = 0
    no_parallel = true
  end
end

fl = get(ENV, "CI", "false")

if fl === "true"
  @info "Running on CI"
  @info "Sys.CPU_THREADS: $(Sys.CPU_THREADS)"
end

if fl === "true" && !no_parallel && !Sys.iswindows() && VERSION < v"1.11"
  @info "On CI, !no_parallel and not Windows"
  isparallel = true
  # CPU_THREADS reports number of logical cores (including hyperthreading)
  # So be pessimistic and divide by 2
  n_procs = max(ceil(Int, Sys.CPU_THREADS/2), 1)
  if Sys.islinux()
    # there is not enough memory to support >= 2 jobs
    # isparallel = false
  end
end

# Special consideration for Windows on CI
# We quickly run out of resources there, so let's do non-parallel and only short
if fl === "true" && Sys.iswindows()
  isparallel = false
  short_test = true
end

# Now collect the tests we want to run

const test_exclude = ["setup.jl", "runtests.jl", "parallel.jl", "testdefs.jl", "Aqua.jl", "FieldFactory.jl", "threads.jl"]

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

  if startswith(t, '.') || endswith(t, ".toml")
    continue
  end

  if t in long_tests
    if long_test
      push!(tests, t)
    else
      continue
    end
  end

  if !(t in test_exclude)
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

# Include all test/*.jl by hand
# We want many jobs for the parallel run

if isparallel
  newtests = String[]
  for t in tests
    tstripped = String(split(t, ".jl")[1])
    for (root, dirs, files) in walkdir(joinpath(test_directory, tstripped))
      for tsub in files

        if startswith(tsub, '.') || endswith(tsub, ".swp")
          continue
        end

        tsubstripped = String(split(tsub, ".jl")[1])

        if tsubstripped in dirs
          # there is a subdirectory
          continue
        end


        # now test_directory = absolute path
        # but I need the relative path from the root directory
        new_test_file = joinpath(String(String(split(root, test_directory)[2])[2:end]), tsub)
        push!(newtests, new_test_file)
      end
    end
  end
  tests = newtests
  Hecke.Random.shuffle!(tests)
end

test_path(test) = joinpath(@__DIR__, test)

@info "Hecke test setup"
@info "CI            : $fl"
@info "long_test     : $long_test"
@info "short_test    : $short_test"
@info "print level   : $PRINT_TIMING_LEVEL"

if isparallel
  @info "parallel      : $isparallel ($(n_procs))"
else
  @info "parallel      : $isparallel"
end
@info "with_gap      : $(_with_gap)"
@info "with_polymake : $(_with_polymake)"
@info "tests         :\n$tests"


function print_res_recursively(testset, cur_level, max_level)
  _testsets = testset.results
  _testsets = filter(x -> isa(x, Test.DefaultTestSet), _testsets)
  if length(_testsets) == 0 || cur_level > max_level
    return nothing
  end
  sort!(_testsets, by = x -> x.time_end - x.time_start, rev = true)
  _maxsize = maximum(x -> min(textwidth(x.description) + 4, 24), _testsets)
  _maxtime = sum(x.time_end - x.time_start for x in _testsets)
  for t in _testsets
    desc = t.description[1:min(20, end)]
    if textwidth(t.description) > 20
      desc = desc * "..."
    end
    print("    "^cur_level, desc)
    print(" "^(_maxsize-textwidth(desc)),": ")
    dur = t.time_end - t.time_start
    @printf "%7.2fs" dur
    @printf " (%4.2fm)" dur/60
    @printf " (%4.2f"  dur/_maxtime * 100
    println("%)")
    print_res_recursively(t, cur_level + 1, max_level)
  end
end

#include("Aqua.jl")

if short_test
  include("setup.jl")
  # Short tests are always running on one machine
  @info "Running short tests"
  include(joinpath("..", "system", "precompile.jl"))
else
  if !isparallel
    # We are not short
    k, a = quadratic_field(5)
    @test ZZRingElem(1) - a == -(a - 1)
    @test 1 - a == -(a - 1)

    include("setup.jl")

    testsets = []

    for t in tests
      res = include(test_path(t))
      push!(testsets, (t, res))
    end

    if PRINT_TIMING_LEVEL > 0
      # Sort by timing
      sort!(testsets, by = x -> x[2].time_end - x[2].time_start, rev = true)
      maxsize = maximum(x -> textwidth(first(x)), testsets)
      maxtime = sum(x[2].time_end - x[2].time_start for x in testsets)
      @info "Timing summary"
      for (name, testset) in testsets
        print(name)
        print(" "^(maxsize-textwidth(name)),": ")
        dur = testset.time_end - testset.time_start
        @printf "%7.2fs" dur
        @printf " (%4.2fm)" dur/60
        @printf " (%4.2f"  dur/maxtime * 100
        println("%)")
        print_res_recursively(testset, 2, PRINT_TIMING_LEVEL)
      end
    end
  else
    # Now we are parallel
    include("parallel.jl")
  end

  # Run the doctests
  if v"1.10-" <= VERSION < v"1.11-"
    @info "Running doctests (Julia version is 1.10)"
    DocMeta.setdocmeta!(Hecke, :DocTestSetup, :(using Hecke); recursive = true)
    doctest(Hecke)
  else
    @info "Not running doctests (Julia version must be 1.10)"
  end
end
