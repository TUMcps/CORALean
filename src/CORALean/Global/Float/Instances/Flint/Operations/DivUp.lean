import CORALean.Global.Float.Instances.Flint.Flint

/-!
# Division, rounded up

`arf_div` at `p` bits with `ARF_RND_CEIL`, run by the C shim `Flint/coralean_flint.c`, which
converts both operands to `arf_t` exactly and the result back. `opaque`: Lean
knows nothing of what it returns, so its direction is assumed in
`Definitions/Axioms` and nowhere proved.

A zero divisor, where FLINT returns a special value no pair can hold, comes
back as `0`: the class constrains a positive divisor only.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

namespace Flint


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `p` is explicit because it is data here, the precision the C code rounds to. -/
@[extern "coralean_flint_div_up"]
opaque divUp (p : @& ℕ) (a b : @& Flint p) : Flint p

end Flint

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
