# A draft for a "get some data" interface

const _Data = Dict(
  "lattices" => ("data/lattices", "https://github.com/thofma/Hecke.jl/releases/download/DBtest/lattice_test", 2),
  "quadratic_lattices" => ("data/quadratic_lattices", "https://github.com/thofma/Hecke.jl/releases/download/DBtest/qlat_small", 6),
 )

function download_data(;data)
  @assert haskey(_Data, data)
  data = _Data[data]
  println("This will download $(data[3]) MB of data. Proceed? [Y/n]")
  n = readline()
  if n == "" || n == "Y" || n == "yes" || n == "Yes"
    Base.download(data[2], joinpath(pkgdir, data[1]))
  end
  nothing
end
