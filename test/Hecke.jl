@testset "Test infrastructure" begin
  @test Hecke._test_file("Misc/Integer") ==
        joinpath(Hecke.pkgdir, "test", "Misc", "Integer.jl")
  @test Hecke._test_file("Misc/Integer.jl") ==
        joinpath(Hecke.pkgdir, "test", "Misc", "Integer.jl")

  setup_file = joinpath(Hecke.pkgdir, "test", "setup.jl")
  test_files = [joinpath(Hecke.pkgdir, "test", "Misc", "Integer.jl"),
                joinpath(Hecke.pkgdir, "test", "Misc", "MSet.jl")]
  command = Hecke._test_command(test_files, setup_file; long = false,
                                with_gap = false, with_polymake = false)
  setup_range = findfirst("include($(repr(setup_file)))", command)
  first_test_range = findfirst("include($(repr(test_files[1])))", command)
  second_test_range = findfirst("include($(repr(test_files[2])))", command)
  @test setup_range !== nothing
  @test first_test_range !== nothing
  @test second_test_range !== nothing
  @test first(setup_range) < first(first_test_range) < first(second_test_range)

  mktempdir() do repo
    mkpath(joinpath(repo, "test", "Foo"))
    touch(joinpath(repo, "test", "Foo", "Bar.jl"))
    touch(joinpath(repo, "test", "Foo.jl"))
    source_files = ["src/Foo/Bar.jl", "src/Foo/Baz.jl",
                    "src/Foo/Another.jl", "src/TopLevel.jl"]
    @test Hecke._test_files_for_changes(repo, source_files) ==
          [joinpath("Foo", "Bar.jl"), "Foo.jl"]
  end

  mktempdir() do repo
    run(`git -C $repo init --quiet`)
    mkpath(joinpath(repo, "src"))
    write(joinpath(repo, "src", "staged.jl"), "staged\n")
    run(`git -C $repo add src/staged.jl`)
    write(joinpath(repo, "src", "staged.jl"), "changed again\n")
    write(joinpath(repo, "src", "untracked file.jl"), "untracked\n")
    write(joinpath(repo, "not-source.jl"), "not source\n")
    @test Hecke._git_changed_files(repo) ==
          ["src/staged.jl", "src/untracked file.jl"]
  end
end
