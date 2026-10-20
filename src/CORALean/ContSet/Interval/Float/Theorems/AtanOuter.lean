module

public import CORALean.ContSet.Interval.Float.Operations.Atan

@[expose] public section

/-!
# `Interval.atan` contains the image under `arctan`

For every box: monotonicity, then `atanDown_le`/`le_atanUp` at the corners.

## Inputs
* `p` – halving count
* `k` – bisection and Newton steps
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the arctangent image of `I` lies in the result box
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.atan_outer [SoundFloatArithmetic 𝕋] (p k : ℕ) (I : Interval (Vec 𝕋 n)) :
    (fun x i => Real.arctan (x i)) '' I.construct ⊆ (I.atan p k).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact ⟨le_trans (atanDown_le p k _) (Real.arctan_strictMono.monotone hx'.1),
    le_trans (Real.arctan_strictMono.monotone hx'.2) (le_atanUp p k _)⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
