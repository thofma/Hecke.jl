/*=============================================================================
 This file is part of Hecke.

 Copyright (c) 2015: Claus Fieker, Tommy Hofmann
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:
 * Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.

 * Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation
   and/or other materials provided with the distribution.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

 (C) 2015, 2016 Claus Fieker, Tommy Hofmann

=============================================================================*/
/******************************************************************************

    Copyright (C) 2016 Claus Fieker

******************************************************************************/

#include <gmp.h>
#include "flint.h"
#include "fmpz.h"
#include "fmpz_vec.h"
#include "fmpz_poly.h"
#include "nmod_poly.h"

void
_fmpz_vec_get_nmod_poly(nmod_poly_t res, const fmpz * coeffs, slong len)
{
    if (len == 0)
    {
        nmod_poly_zero(res);
    }
    else
    {
        slong i;
        nmod_poly_fit_length(res, len);
        for (i = 0; i < len; i++)
            res->coeffs[i] = fmpz_fdiv_ui(coeffs + i, res->mod.n);
        _nmod_poly_set_length(res, len);
        _nmod_poly_normalise(res);
    }
}
