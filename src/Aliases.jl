import Nemo: is_cyclo_type
import Nemo: is_embedded
import Nemo: is_maxreal_type
import Nemo: ZZModRing  # FIXME: remove if/once Nemo exports this
include(joinpath(pathof(Nemo), "..", "Aliases.jl"))

# make some Julia names compatible with our naming conventions
@alias is_hermitian ishermitian
