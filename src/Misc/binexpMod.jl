#square-and-multiply algorithm to compute f^e mod g

function binexpMod(f::nmod_poly, e::fmpz, g::nmod_poly)

    #small exponent -> use powmod
    if nbits(e) <= 63
        return powmod(f, Int(e), g)
    else
        #go through binary representation of exponent and multiply with res
        #or (res and f)
        res = parent(f)(1)
        for b=bits(e)
            res = mod(res^2, g)
            if b
                res = mod(res*f, g)
            end
        end
        return res
    end

end
