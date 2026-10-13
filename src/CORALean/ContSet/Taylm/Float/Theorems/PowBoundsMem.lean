import CORALean.ContSet.Taylm.Float.Operations.PowBounds
import CORALean.ContSet.Interval.Float.Theorems.PowerOuter

/-!
# `Taylm.powBounds` brackets the power

Every power `t ^ k` of a point of `[l, u]` lies in the stored range, by `Interval.power_outer`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.powBounds_mem {l u : 𝕋} {t : ℝ} (hl : toReal l ≤ t) (hu : t ≤ toReal u) (k : ℕ) :
    toReal (Taylm.powBounds l u k).1 ≤ t ^ k ∧ t ^ k ≤ toReal (Taylm.powBounds l u k).2 := by
  have h := Interval.power_outer (⟨fun _ => l, fun _ => u⟩ : Interval (Vec 𝕋 1)) k
    ⟨fun _ => t, fun _ => ⟨hl, hu⟩, rfl⟩ 0
  exact h

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
