module

public import CORALean.Global.Float.Instances.Flint.Definitions.TrustedFlint

@[expose] public section

/-!
# The one thing the FLINT backend assumes

`trustedFlint` is TRUE if FLINT's `arf_add`, `arf_mul` and `arf_div` round as
documented — correctly, to at most `prec` significand bits, towards minus
infinity under `ARF_RND_FLOOR` and plus infinity under `ARF_RND_CEIL`, with the
error "at most 1 ulp with directed rounding modes" (https://flintlib.org/doc/arf.html,
"arf.h", module introduction and "Types, macros and constants") — and if the
shim `Flint/coralean_flint.c` converts exactly, `arf_set_fmpz_2exp` and
`arf_get_fmpz_2exp` being exact. It trusts that code as `trustedHardware`
trusts IEEE 754 hardware. The shim rounds a `p` below 2 at 2 bits; a direction
holds at any precision, so every `p` is covered. `fmpz` exponents cannot
overflow, so, unlike the hardware's, this assumption has no range condition.

Consistent: `Dyadic p`'s operations satisfy every conjunct as theorems. The
third `axiom` in CORALean, after `trustedHardware` and the bench's false
`nearestUnsound`; `scripts/check-axioms.sh` keeps it out of every result
outside this backend, which is opt-in and linked only by `bench-flint`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)

namespace CORALean.Float.Flint

axiom trustedFlint : TrustedFlint

end CORALean.Float.Flint
