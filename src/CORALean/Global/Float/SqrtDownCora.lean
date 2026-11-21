module

public import CORALean.Global.Float.Sqrt

@[expose] public section

/-!
# `sqrtDownCora`

The square root from below that CORA's interval root takes at the lower end of a box: the format's
own machine root where it supplies one (`sqrtDownOverride`), otherwise `sqrtDown`, the quotient of
the radicand by the root from above. The machine root is correctly rounded, not below the real
one, so the bound holds only by the law the format states for it, false at round-to-nearest and
absent from every sound format, where this is `sqrtDown`.

## Inputs
* `p` – Newton steps
* `a` – radicand

## Output
* the root from below, the format's own where it has one
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       21-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The root from below that CORA takes: the format's own where it has one, else `sqrtDown`. -/
def sqrtDownCora (p : ℕ) (a : 𝕋) : 𝕋 :=
  match sqrtDownOverride (𝕋 := 𝕋) with
  | some f => f p a
  | none => sqrtDown p a


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
