import CORALean.ContSet.Interval.Float.Operations.Sin

/-!
# `Interval.sin` contains the image under `sin`

For every box and precision: `sinRange_mem` on every coordinate.
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

theorem Interval.sin_outer [SoundFloatArithmetic 𝕋] (p : ℕ) (I : Interval (Vec 𝕋 n)) :
    (fun x i => Real.sin (x i)) '' I.construct ⊆ (I.sin p).construct := by
  rintro _ ⟨x, hx, rfl⟩ i
  have hx' : toReal (I.inf i) ≤ x i ∧ x i ≤ toReal (I.sup i) := hx i
  exact sinRange_mem p hx'.1 hx'.2


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
