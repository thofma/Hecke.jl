using Hecke
bla = normpath(joinpath(dirname(pathof(Hecke)), "..", "docs", "make.jl"))
local_build = true
include(bla)

function _open(filename; wait = false)
    @static if Sys.isapple()
        run(`open $(filename)`; wait = wait)
    elseif Sys.islinux() || Sys.isbsd()
        run(`xdg-open $(filename)`; wait = wait)
    elseif Sys.iswindows()
        cmd = get(ENV, "COMSPEC", "cmd.exe")
        run(`$(cmd) /c start $(filename)`; wait = wait)
    else
        @warn("Opening files the default application is not supported on this OS.",
              KERNEL = Sys.KERNEL)
    end
end

if !Hecke.html_build[]
  cd(normpath(joinpath(dirname(pathof(Hecke)), "..", "docs"))) do
    run(`mkdocs build --no-directory-urls`, wait = true)
  end

  bla = normpath(joinpath(dirname(pathof(Hecke)), "..", "docs", "site", "index.html"))
  _open(bla)
else
  bla = normpath(joinpath(dirname(pathof(Hecke)), "..", "docs", "build", "index.html"))
  _open(bla)
end
