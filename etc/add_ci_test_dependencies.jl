using TOML

project = TOML.parsefile(joinpath(@__DIR__, "..", "Project.toml"))
test_project = joinpath(@__DIR__, "..", "test", "Project.toml")
test_dependencies = TOML.parsefile(test_project)
for name in ("GAP", "Polymake")
  test_dependencies["deps"][name] = project["weakdeps"][name]
end
open(test_project, "w") do io
  TOML.print(io, test_dependencies; sorted = true)
end
