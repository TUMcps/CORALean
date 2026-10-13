import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.Operations.MaxPoolGapUp

/-!
# A pooled window's gap bounds every other tap's reach

At any tap but the pivot, where `subUp` is the one rounding the layer pays, and the maximum is
at least that entry: what `maxPool_bounds` asks of its `g`.
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

theorem le_maxPoolGapUp (tap : Fin m → Fin (k + 1) → Fin n) (p : Fin m → Fin (k + 1))
    (I : Interval (Vec 𝕋 n)) (j : Fin m) {l : Fin (k + 1)} (hl : l ≠ p j) :
    toReal (I.sup (tap j l)) - toReal (I.inf (tap j (p j)))
      ≤ toReal (maxPoolGapUp tap p I j) := by
  have h := le_maximumOver
    (fun l => if l = p j then zero else subUp (I.sup (tap j l)) (I.inf (tap j (p j)))) l
  rw [if_neg hl] at h
  exact le_trans (sub_le_subUp _ _) h

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
