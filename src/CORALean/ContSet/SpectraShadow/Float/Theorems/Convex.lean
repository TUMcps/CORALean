module

public import CORALean.ContSet.SpectraShadow.Float.SpectraShadow
public import CORALean.ContSet.Interval.Real.Theorems.Convex

@[expose] public section

/-!
# A float spectrahedral shadow is convex

Not the exact layer's theorem at float data: what this denotes is a nominal
shadow *plus* an error box, so what carries convexity across is `Convex.add`, over
two sets each convex for its own reason — the nominal one as an affine image of a
slice of the positive semidefinite cone, the box because its coordinates are
bounded independently.

So the error box costs the property nothing, which is why no operation has to
restate it after paying a rounding into that box.

## Inputs
* `S` – spectrahedral shadow

## Hypotheses
* none

## Conclusion
* A float spectrahedral shadow is convex
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem SpectraShadow.convex_construct (S : SpectraShadow 𝕋 (Vec 𝕋 n)) : Convex ℝ S.construct :=
  Convex.add (nominal S).convex_construct S.I_error.nominal.convex_construct

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
