import CORALean.ContSet.Interval.Float.Operations.Asin

/-!
# `Interval.asin` contains the image under `arcsin`

For every box, no domain hypothesis: `Real.arcsin` is monotone on all of `ℝ`, constant outside
`[-1, 1]`, and `asinDown`/`asinUp` clamp their argument the same way.
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

theorem Interval.asin_outer [SoundFloatArithmetic 𝕋] (p k : ℕ) (I : Interval (Vec 𝕋 n)) :
    (fun x i => Real.arcsin (x i)) '' I.construct ⊆ (I.asin p k).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact ⟨le_trans (asinDown_le p k _) (Real.arcsin_le_arcsin hx'.1),
    le_trans (Real.arcsin_le_arcsin hx'.2) (le_asinUp p k _)⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
