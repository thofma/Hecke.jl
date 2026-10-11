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
  @test Meta.parse(command) isa Expr

  @testset "Ordinary and long test selection" begin
    mktempdir() do directory
      mkpath(joinpath(directory, "Foo", "Nested"))
      wrapper = joinpath(directory, "Foo.jl")
      ordinary = joinpath(directory, "Foo", "Bar.jl")
      marked = joinpath(directory, "Foo", "Slow.jl")
      nested = joinpath(directory, "Foo", "Nested", "Deep.jl")
      unmarked = joinpath(directory, "Foo", "Legacy-long.jl")
      # Construct the fixture marker without marking this test file itself.
      marker = "@" * "long_test"
      write(wrapper, "include(\"Foo/Bar.jl\")")
      write(ordinary, "@long_test_extra nothing")
      write(unmarked, "nothing")
      for path in (marked, nested, joinpath(directory, "setup.jl"),
                   joinpath(directory, "Aqua.jl"),
                   joinpath(directory, "Foo", ".hidden.jl"))
        write(path, "$marker begin; nothing; end")
      end
      all_files = sort([ordinary, marked, nested, unmarked])
      long_files = sort([marked, nested])
      @test Hecke._has_long_tests(marked)
      @test !Hecke._has_long_tests(ordinary)
      @test !Hecke._has_long_tests(unmarked)
      @test Hecke._test_files_in_directory(directory) == all_files
      @test Hecke._test_files_in_directory(directory; long_only = true) == long_files
      @test Hecke._test_files([ordinary]) == [ordinary]
      @test isempty(Hecke._test_files([ordinary]; long_only = true))
      @test Hecke._test_files([marked]; long_only = true) == [marked]
      @test Hecke._test_files([unmarked]) == [unmarked]
      @test Hecke._test_files([wrapper]) == [wrapper]
      @test Hecke._test_files([wrapper]; long_only = true) == long_files
      @test Hecke._test_files([joinpath(directory, "Foo", "Nested.jl")]) == [nested]
      @test Hecke._test_files([ordinary, marked, marked]; long_only = true) == [marked]
      @test_throws ArgumentError Hecke._test_files([joinpath(directory, "Missing.jl")])
    end

    test_directory = normpath(joinpath(Hecke.pkgdir, "test"))
    ordinary = Hecke._test_files_in_directory(test_directory)
    extended = Hecke._test_files_in_directory(test_directory; long_only = true)
    expected_long = Set([
      joinpath(test_directory, "FieldFactory", "FieldFactory.jl"),
      joinpath(test_directory, "FieldFactory", "FrobeniusExtensions.jl"),
      joinpath(test_directory, "QuadForm", "Quad", "Genus.jl"),
      joinpath(test_directory, "QuadForm", "Quad", "ZGenus.jl"),
    ])
    @test issubset(expected_long, Set(extended))
    @test issubset(Set(extended), Set(ordinary))
    @test all(Hecke._has_long_tests, extended)
    @test joinpath(test_directory, "AlgAssRelOrd", "Eichler.jl") in ordinary
    @test joinpath(test_directory, "ModAlgAss", "Lattices", "Absolute.jl") in ordinary
    @test Hecke._test_files([Hecke._test_file("all")]; long_only = true) ==
          [joinpath(test_directory, "runtests.jl")]
  end

  mktempdir() do repo
    mkpath(joinpath(repo, "test", "Foo"))
    touch(joinpath(repo, "test", "Foo", "Bar.jl"))
    touch(joinpath(repo, "test", "Foo.jl"))
    source_files = ["src/Foo/Bar.jl", "src/Foo/Baz.jl",
                    "src/Foo/Another.jl", "src/TopLevel.jl"]
    @test Hecke._test_files_for_changes(repo, source_files) ==
          [joinpath("Foo", "Bar.jl"), "Foo.jl"]
    mkpath(joinpath(repo, "test", "Directory"))
    @test Hecke._test_files_for_changes(repo, ["src/Directory.jl"]) ==
          ["Directory.jl"]
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
