on_windows = @windows ? true : false
on_osx = @osx ? true : false

oldwdir = pwd()

nemo_pkgdir = Pkg.dir("Nemo") 
nemo_wdir = Pkg.dir("Nemo", "deps")
nemo_vdir = Pkg.dir("Nemo", "local")

pkgdir = Pkg.dir("Hecke") 
wdir = Pkg.dir("Hecke", "deps")
vdir = Pkg.dir("Hecke", "local")


if !ispath(Pkg.dir("Hecke", "local"))
    mkdir(Pkg.dir("Hecke", "local"))
end
if !ispath(Pkg.dir("Hecke", "local", "lib"))
    mkdir(Pkg.dir("Hecke", "local", "lib"))
end

LDFLAGS = "-Wl,-rpath,$nemo_vdir/lib -Wl,-rpath,\$\$ORIGIN/../share/julia/site/v$(VERSION.major).$(VERSION.minor)/Nemo/local/lib -Wl,-rpath,$vdir/lib -Wl,-rpath,\$\$ORIGIN/../share/julia/site/v$(VERSION.major).$(VERSION.minor)/Hecke/local/lib"
DLCFLAGS = "-fPIC -fno-common"

cd(wdir)

if on_windows
  error("not supported yet")
   if Int == Int32
      download_dll("http://nemocas.org/binaries/w32-libarb.dll", joinpath(vdir, "lib", "libarb.dll"))
   else
      download_dll("http://nemocas.org/binaries/w64-libarb.dll", joinpath(vdir, "lib", "libarb.dll"))
   end
else
   cd("$wdir/hecke")
   withenv("LD_LIBRARY_PATH"=>"$vdir/lib:$nemo_vdir/lib", "LDFLAGS"=>LDFLAGS) do
      run(`./configure --prefix=$vdir --disable-static --enable-shared --with-mpir=$nemo_vdir --with-mpfr=$nemo_vdir --with-flint=$nemo_vdir`)
      run(`make -j4`)
      run(`make install`)
   end
end

push!(Libdl.DL_LOAD_PATH, Pkg.dir("Hecke", "local", "lib"))

cd(oldwdir)

