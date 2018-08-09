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

function add!(c::fmpq_mpoly, a::fmpq_mpoly, b::fmpq_mpoly)
  ccall((:fmpq_mpoly_add, :libflint), Void,
        (Ref{fmpq_mpoly}, Ref{fmpq_mpoly}, Ref{fmpq_mpoly}, Ref{FmpqMPolyRing}),
        c, a, b, c.parent)
  return c
end
