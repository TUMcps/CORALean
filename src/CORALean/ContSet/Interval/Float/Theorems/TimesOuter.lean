module

public import CORALean.ContSet.Interval.Float.Operations.Times
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `Interval.times` contains the entrywise products

Each coordinate is `Float.Interval.mul_between_corners`, which already pays the rounding.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.times_outer (I J : Interval (Vec 𝕋 n)) :
    Set.image2 (fun x y i => x i * y i) I.construct J.construct ⊆ (I.times J).construct := by
  rintro _ ⟨x, hx, y, hy, rfl⟩ i
  exact Interval.mul_between_corners (hx i).1 (hx i).2 (hy i).1 (hy i).2


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
