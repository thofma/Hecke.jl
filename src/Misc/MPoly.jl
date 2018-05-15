###############################################################################
# other stuff, trivia and non-trivia
###############################################################################

function Nemo.PolynomialRing(R::Nemo.Ring, n::Int, s::String="x";
                             cached::Bool = false, ordering::Symbol = :lex)
  return Nemo.PolynomialRing(R, ["$s$i" for i=1:n], cached = cached,
                                                    ordering = ordering)
end

function total_degree(f::fmpq_mpoly)
  return Int(maximum(degree(f, i) for i=1:nvars(parent(f))))
end

function total_degree(f::Generic.MPoly)
  return Int(maximum([sum(f.exps[:, i]) for i=1:length(f)]))
end


