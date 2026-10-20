module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalSubsetNominalZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# A box as a zonotope, over a floating-point scalar

The center may be rounded any way at all — the radius is then measured *from the
center that was actually stored*, upward on both sides, so it reaches whichever
end the rounding moved away from. That is why the radius is a maximum of two
directed differences rather than half the width: half a rounded width would
leave one edge short whenever the center moved.

Nothing goes into the error box. The generators already cover the rounding, and
paying for it twice would only widen the result.

## Inputs
* `I` – interval

## Hypotheses
* none

## Conclusion
* interval is contained in its zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- the error box adds nothing, the generators already covering the box
theorem Interval.zonotope_contains (I : Interval (Vec 𝕋 n)) :
    I.construct ⊆ I.zonotope.construct := fun x hx =>
  ⟨x, I.subset_nominal_zonotope hx, 0, fun i => by
    show toReal (zero : 𝕋) ≤ (0 : Vec ℝ n) i ∧ (0 : Vec ℝ n) i ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_refl 0, le_refl 0⟩, by show x + 0 = x; rw [add_zero]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
