# A draft for a "get some data" interface

const _Data = Dict(
  "lattices" => ("data/lattices", "https://github.com/thofma/Hecke.jl/releases/download/DBtest/lattice_test", 2),
  "quadratic_lattices" => ("data/quadratic_lattices", "https://github.com/thofma/Hecke.jl/releases/download/DBtest/qlat_small", 6),
  "hermitian_lattices" => ("data/hermitian_lattices", "https://github.com/thofma/Hecke.jl/releases/download/DBtest/hlat_small", 0.2),
  "small_groups_extended" => ("data/small_groups_extended", "https://github.com/thofma/Hecke.jl/releases/download/DBtest/small_groups_extended", 2.4),
 )

function download_data(;data)
  @assert haskey(_Data, data)
  data = _Data[data]
  println("This will download $(data[3]) MB of data. Proceed? [Y/n]")
  n = readline()
  if n == "" || n == "Y" || n == "yes" || n == "Yes" || n == "y"
    Base.download(data[2], joinpath(pkgdir, data[1]))
    return true
  end
  return false
end
