import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.Operations.MaxPoolGapUp

/-!
# A pooled window's gap is nonnegative

Read at the pivot, where the window contributes an exact `zero`, and the maximum is at least
every entry.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem maxPoolGapUp_nonneg (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval (Vec 𝕋 n)) (j : Fin m) : 0 ≤ toReal (maxPoolGapUp tap p I j) := by
  have h := le_maximumOver
    (fun l => if l = p j then zero else subUp (I.sup (tap j l)) (I.inf (tap j (p j)))) (p j)
  rw [if_pos rfl, toReal_zero] at h
  exact h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
