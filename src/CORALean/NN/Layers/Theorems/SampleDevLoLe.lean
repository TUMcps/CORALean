module

public import CORALean.NN.Layers.Operations.SampleDevLo
public import CORALean.NN.Layers.Theorems.LeEvalPolyUp

@[expose] public section

/-!
# A sampled deviation's lower bound

The enclosure's low end and the fit's high evaluation, subtracted downward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sampleDevLo_le {E : Enclosure 𝕋} (hE : E.Sound σ) (c : Fin (m + 1) → 𝕋) (x : 𝕋) :
    toReal (sampleDevLo E c x)
      ≤ σ (toReal x) - Real.evalPoly (fun k => toReal (c k)) (toReal x) := by -- --- PROOF ---
  have h1 := subDown_le_sub (E.lo x) (evalPolyUp c x)
  have h2 := hE.lo_le x
  have h3 := le_evalPolyUp c x
  rw [sampleDevLo]
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
