import CORALean.ContSet.Interval.Float.Operations.StlInterval

/-!
# `Interval.stlInterval` is exact, over a floating-point scalar

The set of times is the first coordinate of the box the stored floats denote; nothing rounds.
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

theorem Interval.stlInterval_exact (I : Interval (Vec 𝕋 1)) :
    I.stlInterval = (fun x : Vec ℝ 1 => x 0) '' I.construct := by -- --- PROOF ---
  ext t
  constructor
  · intro h
    refine ⟨fun _ => t, fun i => ?_, rfl⟩
    rw [Subsingleton.elim i 0]
    exact h
  · rintro ⟨x, hx, rfl⟩
    exact hx 0

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
