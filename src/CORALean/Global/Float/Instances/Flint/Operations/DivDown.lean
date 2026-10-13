import CORALean.Global.Float.Instances.Flint.Flint

/-!
# Division, rounded down

`arf_div` at `p` bits with `ARF_RND_FLOOR`, run by the C shim `Flint/coralean_flint.c`, which
converts both operands to `arf_t` exactly and the result back. `opaque`: Lean
knows nothing of what it returns, so its direction is assumed in
`Definitions/Axioms` and nowhere proved.

A zero divisor, where FLINT returns a special value no pair can hold, comes
back as `0`: the class constrains a positive divisor only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Flint


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `p` is explicit because it is data here, the precision the C code rounds to. -/
@[extern "coralean_flint_div_down"]
opaque divDown (p : @& ℕ) (a b : @& Flint p) : Flint p

end Flint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
