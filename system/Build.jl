using Pkg

Pkg.add("PackageCompiler")
Pkg.add("Libdl")

using PackageCompiler, Libdl

f = open("/tmp/CompileHecke.jl", "w")
println(f, "using Hecke")
println(f, "using Pkg")
println(f, "Hecke.test_module(\"runtests\", false)")
close(f)

PackageCompiler.create_sysimage([:Hecke], sysimage_path="/tmp/Hecke.$(Libdl.dlext)", precompile_execution_file="/tmp/CompileHecke.jl")        

println("(re)start julia as")
println("\tjulia -J /tmp/Hecke.$(Libdl.dlext)")



