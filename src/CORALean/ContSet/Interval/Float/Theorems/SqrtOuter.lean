module

public import CORALean.ContSet.Interval.Float.Operations.Sqrt

@[expose] public section

/-!
# `Interval.sqrt` contains the image under `sqrt`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.sqrt_outer [SoundFloatArithmetic 𝕋] (p : ℕ) (I : Interval (Vec 𝕋 n)) :
    (fun x i => Real.sqrt (x i)) '' I.construct ⊆ (I.sqrt p).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact ⟨le_trans (sqrtDown_le p _) (Real.sqrt_le_sqrt hx'.1),
    le_trans (Real.sqrt_le_sqrt hx'.2) (le_sqrtUp p _)⟩


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
