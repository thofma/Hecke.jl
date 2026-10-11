using Hecke
using Test
using Distributed

import PrettyTables

old_working_directory = pwd()
cd(joinpath(Hecke.pkgdir, "test"))

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

long_only = "long-only" in ARGS ||
            get(ENV, "HECKE_TESTLONGONLY", "false") in ["1", "true"]

long_test = long_only || "long" in ARGS ||
            get(ENV, "HECKE_TESTLONG", "false") in ["1", "true"]

if get(ENV, "CI", "") == "true" && Sys.iswindows()
  short_test = true
end

short_test && long_only && error("Cannot combine short and long-only tests")

if !long_only
  # Test if _adjust_path works on Windows.
  x = Hecke._adjust_path("GrpAb/Elem")
  y = joinpath(Hecke.pkgdir, "test", "$x.jl")
  @test isfile(y)
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

@everywhere import Dates
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

require_extensions = get(ENV, "HECKE_REQUIRE_TEST_EXTENSIONS", "false") in
                     ["1", "true"]

# Load Polymake before GAP, as in Oscar, to avoid conflicts between libraries.
_with_polymake = false
try
  import Polymake
  println("Found Polymake.")
  global _with_polymake = true
catch e
  if e isa ArgumentError && !require_extensions
    println("using Polymake failed.")
  else
    rethrow()
  end
end

_with_gap = false
try
  using GAP
  println("Found GAP.")
  global _with_gap = true
catch e
  if e isa ArgumentError && !require_extensions
    println("using GAP failed.")
  else
    rethrow()
  end
end

if require_extensions
  Base.get_extension(Hecke, :GAPExt) === nothing &&
    error("Hecke's GAP extension did not load")
  Base.get_extension(Hecke, :PolymakeExt) === nothing &&
    error("Hecke's Polymake extension did not load")
end

@everywhere long_test = $long_test
@everywhere _with_gap = $_with_gap
@everywhere _with_polymake = $_with_polymake

if _with_polymake
  @everywhere push!(Base.LOAD_PATH, "@v#.#")
  @everywhere import Polymake
end

if _with_gap
  @everywhere push!(Base.LOAD_PATH, "@v#.#")
  @everywhere using GAP
end

setup_file = joinpath(Hecke.pkgdir, "test", "setup.jl")
@everywhere include($setup_file)

################################################################################
#
#  Helpers for gathering and timing tests
#
################################################################################

@everywhere function current_rss()
  rss = Ref{Csize_t}(0)
  err = ccall(:uv_resident_set_memory, Cint, (Ref{Csize_t},), rss)
  Base.uv_error("uv_resident_set_memory", err)
  return rss[]
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

    # Sample the worker's current RSS without forcing a garbage collection.
    rss = current_rss()
    relative_path = relpath(abspath(path), Hecke.pkgdir)
    println("-> Testing $relative_path took: total time $(round(stats.time; digits=3)) seconds, compilation $(round(compile_time - recompile_time; digits=3)) seconds + recompilation $(round(recompile_time; digits=3)) seconds, GC $(round(stats.gctime; digits=3)) seconds, $(Base.format_bytes(stats.bytes)), RSS $(Base.format_bytes(rss))")
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
  long_only || push!(testlist, joinpath(test_directory, "Aqua.jl"))
  append!(testlist, Hecke._test_files_in_directory(test_directory; long_only))

  # Reuse a test worker in parallel runs, including its compiled doctest code.
  if !long_only && v"1.10-" <= VERSION < v"1.11-"
    doctest_pid = numprocs >= 2 ? first(workers(worker_pool)) : myid()
    @info "Running doctests on process $doctest_pid (Julia version is 1.10)"
    Distributed.remotecall_eval(Main, doctest_pid, quote
      using Documenter
      DocMeta.setdocmeta!(Hecke, :DocTestSetup, Hecke.doctestsetup(); recursive=true)
      doctest(Hecke)
      nothing
    end)
  else
    @info "Not running doctests (requires Julia 1.10 and ordinary tests)"
  end

  if !long_only && numprocs == 1
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
@info "long_only     : $long_only"
@info "short_test    : $short_test"
@info "processes     : $numprocs"
@info "with_gap      : $(_with_gap)"
@info "with_polymake : $(_with_polymake)"
@info "tests         :\n$testlist"

# With many workers this distributes test files across them; with one worker it
# is effectively a serial loop.
test_stats = pmap(worker_pool, testlist) do path
  println("Starting tests for $path at $(Dates.now(Dates.UTC)) UTC")
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
