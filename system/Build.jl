using Pkg
if VERSION >= v"1.4"
  d = Pkg.dependencies()
  f = filter(x->occursin("PackageCompiler", x.name), collect(values(d)))
else
  d = Pkg.installed()
  f = filter(x->occursin("PackageCompiler", x), keys(d))
end

@show f

if length(f) == 0
  Pkg.add("PackageCompiler")
end

using PackageCompiler

f = open("/tmp/CompileHecke.jl", "w")
println(f, "using Hecke")
println(f, "using Pkg")
println(f, "Hecke.test_module(\"runtests\", false)")
close(f)

PackageCompiler.create_sysimage([:Hecke, :Nemo, :AbstractAlgebra], sysimage_path="/tmp/Hecke.so", precompile_execution_file="/tmp/CompileHecke.jl")        

println("(re)start julia as")
println("\tjulia -J /tmp/Hecke.so")



