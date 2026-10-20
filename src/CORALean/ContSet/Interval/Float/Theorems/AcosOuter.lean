module

public import CORALean.ContSet.Interval.Float.Operations.Acos

@[expose] public section

/-!
# `Interval.acos` contains the image under `arccos`

For every box, no domain hypothesis: `Real.arccos` is antitone on all of `ℝ`, so the corners
swap.

## Inputs
* `p` – halving count
* `k` – bisection and Newton steps
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the arccosine image of `I` lies in the result box
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

theorem Interval.acos_outer [SoundFloatArithmetic 𝕋] (p k : ℕ) (I : Interval (Vec 𝕋 n)) :
    (fun x i => Real.arccos (x i)) '' I.construct ⊆ (I.acos p k).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact ⟨le_trans (acosDown_le p k _) (Real.antitone_arccos hx'.2),
    le_trans (Real.antitone_arccos hx'.1) (le_acosUp p k _)⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
