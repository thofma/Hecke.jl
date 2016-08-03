using Docile, Hecke

function Markdown.plain(io::IO, ::Markdown.HorizontalRule)
  println(io, "-"^3)
end

println(Base.source_dir())
makedocs()
