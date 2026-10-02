import CORALean.ContSet.Interval.Float.Operations.Cos

/-!
# `Interval.cos` contains the image under `cos`

For every box and precision: `cosRange_mem` on every coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.cos_outer [SoundFloatArithmetic 𝕋] (p : ℕ) (I : Interval (Vec 𝕋 n)) :
    (fun x i => Real.cos (x i)) '' I.construct ⊆ (I.cos p).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact cosRange_mem p hx'.1 hx'.2


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
