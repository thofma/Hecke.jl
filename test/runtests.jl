using Hecke
using Test
using Distributed
using Documenter

import PrettyTables

old_working_directory = pwd()
cd(joinpath(Hecke.pkgdir, "test"))

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
  @info "Running only threading tests with $(Threads.nthreads()) threads: threads.jl"
  include("threads.jl")
  exit()
end

short_test = "short" in ARGS ||
             get(ENV, "HECKE_TESTSHORT", "false") in ["1", "true"] ||
             haskey(ENV, "JULIA_PKGEVAL")

long_test = "long" in ARGS ||
            get(ENV, "HECKE_TESTLONG", "false") in ["1", "true"]

if get(ENV, "CI", "") == "true" && Sys.iswindows()
  short_test = true
end

numprocs_str = get(ENV, "NUMPROCS", "1")
if !isempty(ARGS)
  jargs = [arg for arg in ARGS if startswith(arg, "-j")]
  if !isempty(jargs)
    numprocs_str = split(jargs[end], "-j")[end]
  end
end

# Short tests are always running on one process.
const numprocs = short_test ? 1 : parse(Int, numprocs_str)
numprocs >= 1 || error("Number of processes ($numprocs) must be at least 1")

if numprocs >= 2
  println("Adding worker processes")
  # Heap size hint for each worker depending on the number of workers and total
  # memory, but at least 2 GB per worker.
  mem = max(2, trunc(Int, Sys.total_memory() / (numprocs * 1024^3)))
  addprocs(numprocs; exeflags=["--heap-size-hint=$(mem)G"])
end

# Keep a custom worker pool to avoid issues from extra processes started by
# tests.
worker_pool = WorkerPool(workers())

if haskey(ENV, "JULIA_PKGEVAL") ||
   get(ENV, "CI", "") == "true" ||
   haskey(ENV, "HECKE_RANDOM_SEED")
  seed = parse(UInt32, get(ENV, "HECKE_RANDOM_SEED", "42"))
  @info string(@__FILE__) * " -- fixed SEED $seed"
else
  seed = Hecke.Random.rand(UInt32)
  @info string(@__FILE__) * " -- SEED $seed"
end

@everywhere using Test
@everywhere using Hecke
@everywhere Hecke.Random.seed!($seed)
# The RNG is task-local and each `@everywhere` runs in a separate task, so seed
# the main process again.
Hecke.Random.seed!(seed)

################################################################################
#
#  Detect optional packages
#
################################################################################

push!(Base.LOAD_PATH, "@v#.#")

_with_gap = false
try
  using GAP
  println("Found GAP. Add FieldFactory.jl to the long tests")
  global _with_gap = true
catch e
  if e isa ArgumentError
    println("using GAP failed.")
  else
    rethrow()
  end
end

_with_polymake = false
try
  import Polymake
  println("Found Polymake.")
  global _with_polymake = true
catch e
  if e isa ArgumentError
    println("using Polymake failed.")
  else
    rethrow()
  end
end

@everywhere long_test = $long_test
@everywhere _with_gap = $_with_gap
@everywhere _with_polymake = $_with_polymake

if _with_gap
  @everywhere push!(Base.LOAD_PATH, "@v#.#")
  @everywhere using GAP
end

if _with_polymake
  @everywhere push!(Base.LOAD_PATH, "@v#.#")
  @everywhere import Polymake
end

setup_file = joinpath(Hecke.pkgdir, "test", "setup.jl")
@everywhere include($setup_file)

################################################################################
#
#  Helpers for gathering and timing tests
#
################################################################################

function gather_test_files(path::AbstractString)
  isfile(path) && return [String(path)]

  tests = String[]
  for (root, dirs, files) in walkdir(path)
    for file in files
      (startswith(file, '.') || !endswith(file, ".jl")) && continue
      # A file with a matching directory is an include-only wrapper. Run the
      # files below the directory directly to create sufficiently many jobs.
      splitext(file)[1] in dirs && continue
      push!(tests, joinpath(root, file))
    end
  end
  return tests
end

@everywhere function timed_test_include(path::String)
  has_compile_time_stat = VERSION > v"1.11.0"
  if !has_compile_time_stat
    Base.cumulative_compile_timing(true)
    compile_elapsed_times = Base.cumulative_compile_time_ns()
  end

  try
    stats = @timed Base.include(identity, Main, path)
    if has_compile_time_stat
      compile_time = stats.compile_time
      recompile_time = stats.recompile_time
    else
      compile_elapsed_times = Base.cumulative_compile_time_ns() .- compile_elapsed_times
      compile_elapsed_times = compile_elapsed_times ./ 10^9
      compile_time = first(compile_elapsed_times)
      recompile_time = last(compile_elapsed_times)
    end

    relative_path = relpath(abspath(path), Hecke.pkgdir)
    println("-> Testing $relative_path took: total time $(round(stats.time; digits=3)) seconds, compilation $(round(compile_time - recompile_time; digits=3)) seconds + recompilation $(round(recompile_time; digits=3)) seconds, GC $(round(stats.gctime; digits=3)) seconds, $(Base.format_bytes(stats.bytes))")
    return Dict(relative_path =>
                (time=stats.time,
                 ctime=compile_time - recompile_time,
                 rctime=recompile_time,
                 gctime=stats.gctime,
                 alloc=stats.bytes / 2^30))
  finally
    has_compile_time_stat || Base.cumulative_compile_timing(false)
  end
end

function print_stats(io::IO, stats_dict::Dict; backend=:text, max=50)
  sorted = sort(collect(stats_dict), by=x -> x[2].time, rev=true)
  println(io, "### Stats per file")
  println(io)
  table = hcat(first.(sorted),
               permutedims(reduce(hcat, collect.(values.(last.(sorted))))))
  header = [:Filename, Symbol("Total time in s"), Symbol("Compilation"),
            Symbol("Recompilation"), Symbol("GC"), Symbol("Allocations in GB")]
  formatters = [PrettyTables.fmt__printf("%.2f", [2, 3, 4, 5]),
                PrettyTables.fmt__printf("%.1f", [6])]
  PrettyTables.pretty_table(io, table; backend,
                            maximum_number_of_rows=max,
                            column_labels=header,
                            formatters)
end

################################################################################
#
#  Collect and run tests
#
################################################################################

test_directory = joinpath(Hecke.pkgdir, "test")
testlist = String[]

if short_test
  @info "Running short tests"
  push!(testlist, joinpath(test_directory, "Aqua.jl"))
  push!(testlist, joinpath(Hecke.pkgdir, "system", "precompile.jl"))
else
  test_exclude = ["setup.jl", "runtests.jl", "Aqua.jl", "threads.jl"]
  long_tests = ["FieldFactory.jl"]

  push!(testlist, joinpath(test_directory, "Aqua.jl"))
  for test in readdir(test_directory)
    isfile(joinpath(test_directory, test)) || continue
    (startswith(test, '.') || !endswith(test, ".jl")) && continue
    test in test_exclude && continue
    test in long_tests && (!long_test || !_with_gap) && continue

    test_subdirectory = joinpath(test_directory, splitext(test)[1])
    if isdir(test_subdirectory)
      append!(testlist, gather_test_files(test_subdirectory))
    else
      push!(testlist, joinpath(test_directory, test))
    end
  end

  # Run the doctests on the main process.
  if v"1.10-" <= VERSION < v"1.11-"
    @info "Running doctests (Julia version is 1.10)"
    DocMeta.setdocmeta!(Hecke, :DocTestSetup, Hecke.doctestsetup(); recursive=true)
    doctest(Hecke)
  else
    @info "Not running doctests (Julia version must be 1.10)"
  end

  if numprocs == 1
    k, a = quadratic_field(5)
    @test ZZRingElem(1) - a == -(a - 1)
    @test 1 - a == -(a - 1)
  end
end

sort!(testlist)
if get(ENV, "HECKE_TEST_SORTED", nothing) !== "true"
  Hecke.Random.shuffle!(Hecke.Random.MersenneTwister(seed), testlist)
end

@info "Hecke test setup"
@info "CI            : $(get(ENV, "CI", "false"))"
@info "long_test     : $long_test"
@info "short_test    : $short_test"
@info "processes     : $numprocs"
@info "with_gap      : $(_with_gap)"
@info "with_polymake : $(_with_polymake)"
@info "tests         :\n$testlist"

# With many workers this distributes test files across them; with one worker it
# is effectively a serial loop.
test_stats = pmap(worker_pool, testlist) do path
  println("Starting tests for $path")
  timed_test_include(path)
end
stats = reduce(merge, test_stats; init=Dict{String,NamedTuple}())

if haskey(ENV, "GITHUB_STEP_SUMMARY")
  open(ENV["GITHUB_STEP_SUMMARY"], "a") do io
    print_stats(io, stats; backend=:markdown)
  end
else
  print_stats(stdout, stats; max=10)
end

cd(old_working_directory)
