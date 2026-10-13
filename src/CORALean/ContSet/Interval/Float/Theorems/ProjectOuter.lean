import CORALean.ContSet.Interval.Float.Operations.Project

/-!
# `Interval.project` contains the projected points

Reading the same coordinates of a member. The stored box reads as the exact one's, so this is the
exact layer's statement.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.project_outer (I : Interval (Vec 𝕋 n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' I.construct ⊆ (I.project dims).construct := by
  rintro _ ⟨x, hx, rfl⟩ k
  exact hx (dims k)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
