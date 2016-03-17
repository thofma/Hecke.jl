#include "flint.h"

void hecke_abort(void)
{
  jl_error("Problem in Flint");
}
