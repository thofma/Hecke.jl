#/bin/bash

perl -i -p -e 'BEGIN{undef $/;}  s/"""\n {1,3}(\S)/"""\n    \1/smg'  $(find -name \*\.jl)
