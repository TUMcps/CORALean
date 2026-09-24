import CORALean.NN.Layers.Operations.SampleDevUp
import CORALean.NN.Layers.Theorems.EvalPolyDownLe

/-!
# A sampled deviation's upper bound

The enclosure's high end and the fit's low evaluation, subtracted upward.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_sampleDevUp {E : Enclosure 𝕋} (hE : E.Sound σ) (c : Fin (m + 1) → 𝕋) (x : 𝕋) :
    σ (toReal x) - Real.evalPoly (fun k => toReal (c k)) (toReal x)
      ≤ toReal (sampleDevUp E c x) := by -- --- PROOF ---
  have h1 := sub_le_subUp (E.hi x) (evalPolyDown c x)
  have h2 := hE.le_hi x
  have h3 := evalPolyDown_le c x
  rw [sampleDevUp]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
